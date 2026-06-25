"""
Arkadia v4 – Monitor de Notícias com Mapa ao Vivo
Versão corrigida: refinamento obrigatório + extração robusta + PNL melhorada.
"""

import feedparser
import threading
import time
import re
import hashlib
import json
import os
import webbrowser
import unicodedata
from datetime import datetime, timedelta
from difflib import SequenceMatcher
from flask import Flask, jsonify, request as flask_req
from flask_cors import CORS

try:
    import requests as _http
    import bs4 as _bs4
    _DEPS_OK = True
except ImportError:
    _DEPS_OK = False
    print("⚠️  requests / beautifulsoup4 não encontrados. Instale com:")
    print("   pip install requests beautifulsoup4")

try:
    from rapidfuzz import fuzz as _fuzz, process as _fuzz_process
    _FUZZY_OK = True
except ImportError:
    _FUZZY_OK = False
    print("⚠️  rapidfuzz não encontrado. Match fuzzy desativado.")
    print("   pip install rapidfuzz")

# ─────────────────────────────────────────────
#  CONFIGURAÇÃO
# ─────────────────────────────────────────────
DEFAULT_CIDADE       = "Guarapari"
DEFAULT_INTERVALO    = 5
DEFAULT_HORAS_FILTRO = 24
SIMILARIDADE_MINIMA  = 0.55
PORT                 = 5050

PESO_SEQ     = 0.40
PESO_JACCARD = 0.30
PESO_EVENTO  = 0.15
PESO_LOCAL   = 0.15

# Score mínimo de fuzzy para aceitar um bairro como candidato (0-100)
FUZZY_THRESHOLD = 85  # aumentado para reduzir falsos positivos

# ─────────────────────────────────────────────
#  CORRELAÇÃO POR CORPO (sem IA) E LOCAL DO FATO
# ─────────────────────────────────────────────
# Quantos corpos no máximo ler por ciclo (evita travar quando há muitas notícias)
MAX_CORPOS_POR_CICLO = 40
# Tempo-limite total (s) para ler corpos antes de seguir com o que tiver
BUDGET_CORPOS_SEG    = 45
# Trabalhadores paralelos para leitura de corpo
CORPOS_WORKERS       = 8

# Limiar para considerar que duas notícias (com corpo) tratam do MESMO fato
SIM_CORPO_MERGE      = 0.30   # similaridade combinada de corpo
ENT_JACCARD_MIN      = 0.16   # sobreposição mínima de entidades próprias
ENT_COMUNS_MIN       = 2      # nº mínimo de entidades próprias em comum

# Pesos da similaridade de corpo
PESO_ENT   = 0.55   # entidades próprias (nomes, cidades, lugares) — mais discriminante
PESO_TOK   = 0.30   # tokens de conteúdo
PESO_NUM   = 0.15   # números específicos (idades, quantidades)

# Verbos/expressões que indicam que um lugar é o LOCAL DO FATO
_VERBOS_FATO = [
    "desapareceu", "desaparecido", "desaparecida", "sumiu", "visto pela ultima vez",
    "vista pela ultima vez", "encontrado", "encontrada", "localizado", "localizada",
    "resgatado", "resgatada", "ocorreu", "aconteceu", "registrado", "flagrado",
    "preso", "presa", "detido", "detida", "morto", "morta", "morreu", "baleado",
    "atropelado", "acidente", "colisao", "incendio", "explosao", "tiroteio",
    "assalto", "roubo", "furto", "apreensao", "operacao", "no bairro", "na regiao",
    "na localidade", "na area", "na rua", "na avenida", "proximo a", "proximo ao",
    "nas proximidades", "deu entrada", "foi levado", "foi levada", "caiu", "afogou",
]
# Expressões que indicam RESIDÊNCIA / ORIGEM / HOSPEDAGEM (NÃO é o local do fato)
_MARCADORES_RESIDENCIA = [
    "morador de", "moradora de", "moradores de", "residente em", "residente no",
    "residente na", "natural de", "naturais de", "vindo de", "veio de", "turista de",
    "turistas de", "hospedado", "hospedada", "hospedados", "de ferias em",
    "de ferias na", "de ferias no", "que mora", "que morava", "que reside",
    "estava hospedado", "estava hospedada", "se hospedava", "ficava hospedado",
    "ficava hospedada", "onde estava hospedado", "onde estava hospedada",
    "estado de", "interior de",
]

# ─────────────────────────────────────────────
#  CARREGAMENTO DO GEO_BRASIL.JSON
# ─────────────────────────────────────────────
_GEO_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "geo_brasil.json")

def _carregar_geo():
    if not os.path.exists(_GEO_FILE):
        print(f"⚠️  geo_brasil.json não encontrado em: {_GEO_FILE}")
        return {}, {}, {}, {}

    with open(_GEO_FILE, encoding="utf-8") as f:
        raw = json.load(f)

    estados = {}
    cidades = {}
    bairros = {}
    bairros_por_cidade = {}

    for uf, cids in raw.items():
        lats, lons = [], []
        for cidade_nome, cidade_data in cids.items():
            coords = tuple(cidade_data.get("coords", [0, 0]))
            lats.append(coords[0]); lons.append(coords[1])
            cidades[cidade_nome] = {"coords": coords, "estado": uf}

            lista = []
            for bairro_nome, b_coords in cidade_data.get("bairros", {}).items():
                chave = f"{bairro_nome}@{cidade_nome}"
                bairros[chave] = {
                    "coords":  tuple(b_coords),
                    "cidade":  cidade_nome,
                    "estado":  uf,
                }
                lista.append((bairro_nome, tuple(b_coords)))
            bairros_por_cidade[cidade_nome] = lista

        if lats:
            estados[uf] = (round(sum(lats)/len(lats), 4),
                           round(sum(lons)/len(lons), 4))

    print(f"✅ geo_brasil.json: {len(estados)} estados | "
          f"{len(cidades)} cidades | {len(bairros)} bairros")
    return estados, cidades, bairros, bairros_por_cidade


GEO_ESTADOS, GEO_CIDADES, GEO_BAIRROS, GEO_BAIRROS_CIDADE = _carregar_geo()

# ─────────────────────────────────────────────
#  ESTADO GLOBAL
# ─────────────────────────────────────────────
estado = {
    "cidade":         DEFAULT_CIDADE,
    "intervalo":      DEFAULT_INTERVALO,
    "horas_filtro":   DEFAULT_HORAS_FILTRO,
    "noticias":       [],
    "historico":      set(),
    "ultima_busca":   None,
    "buscando":       False,
    "total_visto":    0,
    "busca_imediata": False,
}

_media_cache = {}
_media_lock  = threading.Lock()
_media_queue = []
lock = threading.Lock()

_geo_refine_queue = []
_geo_refine_lock  = threading.Lock()

# cache de contornos de cidade (Nominatim) usado pelo destaque "cidade inteira"
_zona_cache = {}

# cache de URLs reais decodificadas do Google News (id → url real)
_gn_url_cache = {}
_gn_url_lock  = threading.Lock()

# cache de coordenadas PRECISAS de bairro via Nominatim ("bairro@cidade" → (lat,lon)|None)
_bairro_coord_cache = {}
_bairro_coord_lock  = threading.Lock()
_geo_coord_queue = []          # fila p/ refinar a POSIÇÃO de bairros já detectados

# cache de CORPO de notícia já lido ("url base" → texto) — evita reler entre ciclos
_corpo_cache = {}
_corpo_lock  = threading.Lock()

# ─────────────────────────────────────────────
#  UTILIDADES DE NORMALIZAÇÃO
# ─────────────────────────────────────────────
def normalizar(texto):
    return unicodedata.normalize("NFD", str(texto).lower())\
                      .encode("ascii", "ignore").decode()

_CIDADES_NORM = {}
for _cidade in GEO_CIDADES:
    _CIDADES_NORM[normalizar(_cidade)] = _cidade

# ─────────────────────────────────────────────
#  BUSCA DIRETA DE BAIRROS (SEM NLP)
# ─────────────────────────────────────────────
# Para cada cidade, monta lista de (nome_norm, nome_orig, [lat, lon])
# ordenada do maior para o menor nome (evita match parcial de nomes curtos)
_BAIRROS_POR_CIDADE_NORM = {}
for _cidade_key, _lista in GEO_BAIRROS_CIDADE.items():
    _entries = []
    for _nome_orig, _coords in _lista:
        _norm = normalizar(_nome_orig)
        _entries.append((_norm, _nome_orig, list(_coords)))
    # ordena do mais longo para o mais curto: "nova guarapari" antes de "guarapari"
    _entries.sort(key=lambda x: -len(x[0]))
    _BAIRROS_POR_CIDADE_NORM[_cidade_key] = _entries

# ─────────────────────────────────────────────
#  MOTOR PRINCIPAL: busca direta por substring
# ─────────────────────────────────────────────

# Bairros cujo nome é uma palavra comum ou nome de outra cidade/país:
# só são aceitos quando há contexto explícito de localização no texto.
# Contexto = precedido de: "bairro", "em", "no", "na", "região", "localidade"
# ou seguido de vírgula + cidade.
_BAIRROS_AMBIGUOS = {
    # palavras comuns
    "portal", "amarelo", "coroado", "condados", "aruana",
    "tartaruga", "aeroporto", "ipiranga", "olaria",
    "sol nascente", "por do sol", "todos os santos",
    # "centro" é altíssima fonte de falso positivo (centro de zoonoses, centro de
    # saúde, etc.) — só vale como bairro com contexto explícito.
    "centro",
    # nomes de outras cidades/países/regiões conhecidas
    "belo horizonte", "buenos aires", "nova guarapari",
    # nomes que aparecem em portais/fontes de notícia
    "portal 27", "portal es",
    # outros ambíguos
    "una", "coroado",
}

# Palavras que, logo após "<bairro> de ...", indicam uma INSTITUIÇÃO e não o
# bairro (ex.: "Centro de Zoonoses", "Centro de Saúde"). Se TODAS as ocorrências
# do nome forem desse tipo, o bairro é descartado.
_INSTITUICAO_TAIL = {
    "zoonoses", "saude", "convencoes", "convencao", "referencia", "reabilitacao",
    "distribuicao", "atendimento", "triagem", "especialidades", "diagnostico",
    "imagem", "imagens", "detencao", "ressocializacao", "operacoes", "controle",
    "custos", "treinamento", "ensino", "pesquisa", "pesquisas", "estudos",
    "educacional", "esportivo", "esportes", "eventos", "cultura", "juventude",
    "idoso", "idosos", "vivencia", "convivencia", "comercial", "empresarial",
    "logistico", "automotivo", "veterinario", "medico", "cirurgico",
    "oftalmologico", "odontologico", "geriatrico", "administrativo",
    "tecnologico", "tecnologia", "historico", "comando", "inteligencia",
    "monitoramento", "abastecimento", "custeio", "formacao", "capacitacao",
    "reciclagem", "triagem", "acolhimento", "testagem", "vacinacao",
}

def _so_uso_institucional(bairro_norm, texto_norm, cidade_norm, uf_norm):
    """
    True se TODAS as aparições do nome forem do tipo "<bairro> de <instituição>"
    (ex.: "centro de zoonoses"). Nesse caso não é referência ao bairro.
    Exceção: "<bairro> de <cidade>" / "<bairro> de <uf>" é referência válida.
    """
    b = re.escape(bairro_norm)
    ocorrencias = list(re.finditer(r'(?<![a-z])' + b + r'(?![a-z])', texto_norm))
    if not ocorrencias:
        return False
    permitido_tail = {cidade_norm, uf_norm, "guarapari", "es", "cidade", "vila", "praia"}
    for mt in ocorrencias:
        depois = texto_norm[mt.end():mt.end() + 30]
        m2 = re.match(r"\s+d[aeo]\s+([a-z]+)", depois)
        if not m2:
            return False  # esta ocorrência NÃO é "X de algo" → é uso normal
        tail = m2.group(1)
        if tail in permitido_tail:
            return False  # "X de Guarapari" → válido
        if tail not in _INSTITUICAO_TAIL:
            return False  # "X de <palavra não-institucional>" → não bloqueia
    return True  # todas as ocorrências são institucionais

def _mencao_explicita_bairro(bairro_norm, texto_norm):
    """True se o nome aparece com marcador forte de bairro ('bairro X', 'no X')."""
    b = re.escape(bairro_norm)
    return bool(re.search(
        r'(?:bairro|localidade|regiao|comunidade|conjunto|distrito)s?\s+' + b
        + r'|\b(?:no|na|em)\s+' + b
        + r'|' + b + r'\s*,\s*(?:guarapari|es\b)',
        texto_norm))

# Padrão de contexto: bairro "X" ou em/no/na X
_RE_CONTEXTO_BAIRRO = re.compile(
    r'(?:bairro|localidade|regiao|comunidade|vila|conjunto|em|no|na|do|da)\s+{bairro}'
    r'|{bairro}\s*(?:,\s*guarapari|,\s*es\b)',
    re.IGNORECASE
)

def _tem_contexto_bairro(bairro_norm, texto_norm):
    """
    Verifica contexto explícito de localização para bairros ambíguos.
    Aceita:
      - "bairro/localidade/região X"
      - "em/no/na/do/da X"
      - "X, guarapari" ou "X, es"
      - "X de guarapari" (ex: aeroporto de guarapari)
      - "X:" no início (ex: "Una: moradores...")
    Rejeita:
      - "portal 27", "portal es", "portal do ..." (nome de site)
    """
    b = re.escape(bairro_norm)
    positivos = re.compile(
        r'(?:bairro|localidade|regiao|comunidade|conjunto|distrito)\s+' + b +
        r'|\bem\s+' + b +
        r'|\bno\s+' + b +
        r'|\bna\s+' + b +
        r'|\bdo\s+' + b +
        r'|\bda\s+' + b +
        r'|' + b + r'\s*,\s*(?:guarapari|es\b)' +
        r'|' + b + r'\s+de\s+(?:guarapari|es\b)' +
        r'|^' + b + r'\s*:',           # "Bairro X: ..." no início do texto
    )
    if positivos.search(texto_norm):
        # padrão negativo para "portal": rejeita "portal 27", "portal es", "portal do/da/de"
        if bairro_norm == "portal":
            negativos = re.compile(r'\bportal\s+(?:\d+|es\b|do\b|da\b|de\b|das\b|dos\b)')
            if negativos.search(texto_norm):
                return False
        return True
    return False

def buscar_bairros_direto(texto, cidade_monitorada):
    """
    Busca DIRETA de bairros no texto por word-boundary.
    - Normaliza tudo (sem acento, lowercase)
    - Exige que o bairro apareça como palavra/frase isolada (não dentro de outra palavra)
    - Bairros ambíguos (palavras comuns ou cidades conhecidas) só são aceitos
      se há contexto explícito de localização ("bairro X", "em X", "X, Guarapari")
    - Retorna lista [{nome, lat, lon}] com todos os bairros encontrados
    - Retorna [] se nenhum bairro for identificado com confiança
    """
    if not texto:
        return []

    cidade_norm = normalizar(cidade_monitorada)
    cidade_key = _CIDADES_NORM.get(cidade_norm)
    if not cidade_key:
        for c in GEO_CIDADES:
            if cidade_norm in normalizar(c) or normalizar(c) in cidade_norm:
                cidade_key = c
                break

    if not cidade_key or cidade_key not in _BAIRROS_POR_CIDADE_NORM:
        return []

    texto_norm = normalizar(texto)
    uf_norm = ""
    if cidade_key in GEO_CIDADES:
        uf_norm = normalizar(GEO_CIDADES[cidade_key].get("estado", ""))
    encontrados = []
    nomes_ja_achados = set()
    houve_explicito = False  # alguma menção forte "bairro X" / "no X"?

    # _BAIRROS_POR_CIDADE_NORM já está ordenado do maior para o menor
    for bairro_norm, bairro_orig, coords in _BAIRROS_POR_CIDADE_NORM[cidade_key]:
        if len(bairro_norm) < 3:
            continue

        # Exige word-boundary: o bairro não pode estar no meio de outra palavra
        padrao_wb = r'(?<![a-z])' + re.escape(bairro_norm) + r'(?![a-z])'
        if not re.search(padrao_wb, texto_norm):
            continue

        # Evita duplicatas: se já temos um bairro maior que contém este, ignora
        ja_coberto = any(bairro_norm in ja for ja in nomes_ja_achados)
        if ja_coberto:
            continue

        # Descarta usos institucionais ("Centro de Zoonoses", "Centro de Saúde"…)
        if _so_uso_institucional(bairro_norm, texto_norm, cidade_norm, uf_norm):
            continue

        # Bairros ambíguos: exigem contexto explícito de localização
        if bairro_norm in _BAIRROS_AMBIGUOS:
            if not _tem_contexto_bairro(bairro_norm, texto_norm):
                continue

        explicito = _mencao_explicita_bairro(bairro_norm, texto_norm)
        if explicito:
            houve_explicito = True

        encontrados.append({
            "nome": bairro_orig.title(),
            "lat": coords[0],
            "lon": coords[1],
            "_norm": bairro_norm,
            "_explicito": explicito,
        })
        nomes_ja_achados.add(bairro_norm)

    # Priorização: se HÁ menção explícita ("bairro X"), descarta os ambíguos
    # que entraram só por aparição solta (reduz ruído tipo "centro").
    if houve_explicito:
        encontrados = [e for e in encontrados
                       if e["_explicito"] or e["_norm"] not in _BAIRROS_AMBIGUOS]

    # remove campos internos antes de retornar
    for e in encontrados:
        e.pop("_norm", None)
        e.pop("_explicito", None)
    return encontrados

def _coords_cidade(nome):
    n = normalizar(nome)
    if n in GEO_CIDADES:
        return GEO_CIDADES[n]["coords"]
    for cidade, dados in GEO_CIDADES.items():
        if n in normalizar(cidade) or normalizar(cidade) in n:
            return dados["coords"]
    return None

# ─────────────────────────────────────────────
#  POSIÇÃO PRECISA DE BAIRRO (Nominatim, cacheado)
#  Separa DETECÇÃO (geo_brasil, offline) de POSICIONAMENTO (Nominatim, preciso).
#  Corrige bairros cuja coordenada no geo_brasil.json é imprecisa, sem editar o
#  arquivo. Cai de volta para o centroide local se o Nominatim falhar.
# ─────────────────────────────────────────────
def _resolver_coord_bairro(nome, cidade):
    if not _DEPS_OK or not nome:
        return None
    chave = f"{normalizar(nome)}@{normalizar(cidade)}"
    with _bairro_coord_lock:
        if chave in _bairro_coord_cache:
            return _bairro_coord_cache[chave]

    base = _coords_cidade(cidade)
    resultado = None
    if base:
        clat, clon = base
        uf = ""
        ckey = _CIDADES_NORM.get(normalizar(cidade))
        if ckey and ckey in GEO_CIDADES:
            uf = GEO_CIDADES[ckey].get("estado", "")
        try:
            # viewbox: limita a busca a ~13 km ao redor do centro da cidade
            d = 0.12
            r = _http.get(
                "https://nominatim.openstreetmap.org/search",
                params={"q": f"{nome}, {cidade}, {uf}, Brasil",
                        "format": "json", "limit": 1, "countrycodes": "br",
                        "bounded": 1,
                        "viewbox": f"{clon-d},{clat-d},{clon+d},{clat+d}"},
                timeout=10,
                headers={"User-Agent": "Arkadia/4.0 (monitor-noticias-mapa)"},
            )
            data = r.json()
            if data:
                lat = float(data[0]["lat"]); lon = float(data[0]["lon"])
                # sanidade: precisa estar perto do centro da cidade (~15 km)
                if abs(lat - clat) < 0.15 and abs(lon - clon) < 0.15:
                    resultado = (round(lat, 6), round(lon, 6))
        except Exception as exc:
            _log(f"Coord precisa de '{nome}' falhou: {exc}", "WARN")

    with _bairro_coord_lock:
        _bairro_coord_cache[chave] = resultado
    return resultado

def _resolver_coord_rua(rua, bairro, cidade, ref=None):
    """Resolve a coordenada PRECISA de uma rua/avenida via Nominatim, escolhendo
    o resultado mais próximo do bairro. Tenta várias formas de consulta. Cacheado."""
    if not _DEPS_OK or not rua:
        return None
    chave = f"rua::{normalizar(rua)}@{normalizar(bairro or '')}@{normalizar(cidade)}"
    with _bairro_coord_lock:
        if chave in _bairro_coord_cache:
            return _bairro_coord_cache[chave]
    base = _coords_cidade(cidade)
    resultado = None
    if base:
        clat, clon = base
        rlat, rlon = ref if ref else (clat, clon)
        uf = ""
        ckey = _CIDADES_NORM.get(normalizar(cidade))
        if ckey and ckey in GEO_CIDADES:
            uf = GEO_CIDADES[ckey].get("estado", "")
        UA = {"User-Agent": "Arkadia/4.0 (monitor-noticias-mapa)"}
        d = 0.15
        viewbox = f"{clon-d},{clat-d},{clon+d},{clat+d}"
        # várias formas: livre (com/sem bairro) e estruturada (street/city)
        consultas = []
        if bairro:
            consultas.append({"q": f"{rua}, {bairro}, {cidade} - {uf}, Brasil"})
        consultas.append({"q": f"{rua}, {cidade} - {uf}, Brasil"})
        consultas.append({"street": rua, "city": cidade, "state": uf, "country": "Brasil"})
        melhor = None; melhor_dist = None
        for base_params in consultas:
            try:
                params = {**base_params, "format": "json", "limit": 5,
                          "countrycodes": "br", "bounded": 1, "viewbox": viewbox}
                r = _http.get("https://nominatim.openstreetmap.org/search",
                              params=params, timeout=10, headers=UA)
                for cand in (r.json() or []):
                    lat = float(cand["lat"]); lon = float(cand["lon"])
                    if abs(lat - clat) >= 0.18 or abs(lon - clon) >= 0.18:
                        continue
                    dist = (lat - rlat) ** 2 + (lon - rlon) ** 2
                    if cand.get("class") == "highway":
                        dist *= 0.25   # favorece resultados que são realmente vias
                    if melhor is None or dist < melhor_dist:
                        melhor = (round(lat, 6), round(lon, 6)); melhor_dist = dist
                if melhor:
                    break   # já achou nesta consulta
            except Exception as exc:
                _log(f"Coord de rua '{rua}' falhou: {exc}", "WARN")
            time.sleep(1.1)   # respeita o limite do Nominatim
        resultado = melhor
    with _bairro_coord_lock:
        _bairro_coord_cache[chave] = resultado
    return resultado

def _enfileirar_coord_precisa(news_id, cidade, bairros, rua=None):
    """Agenda o refino de POSIÇÃO (Nominatim) — rua do fato quando houver, senão o bairro."""
    if not bairros:
        return
    with _geo_refine_lock:
        _geo_coord_queue.append({"id": news_id, "cidade": cidade,
                                 "bairros": [dict(b) for b in bairros], "rua": rua})

def _worker_coord_precisa():
    """Refina a posição do marcador PRINCIPAL: tenta a rua do fato (precisão de rua);
    se não houver/achar, usa a coordenada precisa do bairro. Cacheado, ≥1.1 s/req."""
    while True:
        with _geo_refine_lock:
            item = _geo_coord_queue.pop(0) if _geo_coord_queue else None
        if not item:
            time.sleep(2)
            continue
        news_id = item["id"]; cidade = item["cidade"]
        bairros = item["bairros"]; rua = item.get("rua")
        if not bairros:
            continue
        principal = bairros[0]
        nb = dict(principal)
        precisao = "bairro"
        mudou = False
        rua_registrada = False

        # 1) tenta posicionar na RUA do fato
        if rua:
            coord_rua = _resolver_coord_rua(rua, principal.get("nome"), cidade,
                                            ref=(principal.get("lat"), principal.get("lon")))
            if coord_rua:
                nb["lat"], nb["lon"] = coord_rua[0], coord_rua[1]
                nb["rua"] = rua
                precisao = "rua"
                mudou = True
                rua_registrada = True
                _log(f"Posição na RUA: {rua} / {principal.get('nome')}", "GEO")
            else:
                # Nominatim não resolveu coord da rua, mas a rua foi detectada:
                # registra o nome para exibir no card/popup mesmo sem mover o pin
                nb["rua"] = rua
                rua_registrada = True
                mudou = True
                _log(f"Rua detectada (coord não resolvida, usando bairro): {rua}", "GEO")

        # 2) se não achou coord de rua, refina ao menos a posição do bairro
        if precisao != "rua":
            with _bairro_coord_lock:
                ja = f"{normalizar(principal['nome'])}@{normalizar(cidade)}" in _bairro_coord_cache
            coord = _resolver_coord_bairro(principal["nome"], cidade)
            if not ja:
                time.sleep(1.1)
            if coord and (abs(coord[0]-principal["lat"]) > 0.0005 or abs(coord[1]-principal["lon"]) > 0.0005):
                nb["lat"], nb["lon"] = coord[0], coord[1]
                mudou = True

        if not mudou:
            continue
        novos = [nb] + [dict(b) for b in bairros[1:]]
        novos[0]["principal"] = True
        if precisao == "rua":
            rotulo = f"{rua} ({principal['nome']})"
        elif rua_registrada:
            rotulo = f"{principal['nome']} · {rua}"
        else:
            rotulo = principal["nome"]
        with lock:
            for n in estado["noticias"]:
                if n["id"] == news_id:
                    n["bairros"] = novos
                    n["lat"] = nb["lat"]; n["lon"] = nb["lon"]
                    n["label"] = rotulo; n["precisao"] = precisao
                    if rua_registrada:
                        n["rua"] = rua
                        if "estatisticas" in n:
                            n["estatisticas"]["rua"] = rua
                    break
        payload = {
            "id": news_id, "bairros": novos,
            "lat": nb["lat"], "lon": nb["lon"],
            "label": rotulo, "precisao": precisao, "geo_score": 1.0,
        }
        if rua_registrada:
            payload["rua"] = rua
        _publicar_sse("geo_update", payload)


def _gn_decode_url(url):
    """
    Resolve o link 'news.google.com/rss/articles/CBMi…' para a URL real do
    artigo. Tenta o formato antigo (base64 direto) e, se falhar, usa o endpoint
    interno batchexecute do Google (Fbv4je/garturlreq) — único método que
    funciona para os links novos (CBMi…AU_yq…). Resultado é cacheado.
    """
    if not _DEPS_OK or "news.google.com" not in url:
        return url
    base = url.split("?")[0]
    with _gn_url_lock:
        if base in _gn_url_cache:
            return _gn_url_cache[base]
    real = _gn_decode_url_impl(base)
    with _gn_url_lock:
        _gn_url_cache[base] = real
    return real

def _gn_decode_url_impl(url):
    import base64
    from urllib.parse import urlparse, quote
    try:
        path = urlparse(url).path.split("/")
    except Exception:
        return url
    gn_id = None
    for marcador in ("articles", "read"):
        if marcador in path:
            i = path.index(marcador)
            if i + 1 < len(path):
                gn_id = path[i + 1]
            break
    if not gn_id:
        return url

    # 1) Formato antigo: a URL vem embutida em base64 (CBMiSGh0dHBz…)
    try:
        s = gn_id + "=" * (-len(gn_id) % 4)
        raw = base64.urlsafe_b64decode(s)
        txt = raw.decode("latin-1", "ignore")
        mt = re.search(r"https?://[A-Za-z0-9\-._~:/?#\[\]@!$&'()*+,;=%]+", txt)
        if mt:
            cand = mt.group(0)
            if "news.google.com" not in cand and len(cand) > 15:
                return cand
    except Exception:
        pass

    # 2) Formato novo: precisa do batchexecute (assinatura + timestamp da página)
    try:
        headers = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                                 "AppleWebKit/537.36 (KHTML, like Gecko) "
                                 "Chrome/125.0.0.0 Safari/537.36"}
        art_url = f"https://news.google.com/rss/articles/{gn_id}"
        r = _http.get(art_url, headers=headers, timeout=10)
        soup = _bs4.BeautifulSoup(r.text, "html.parser")
        div = soup.select_one("c-wiz > div")
        if div is None:
            return url
        sig = div.get("data-n-a-sg")
        ts  = div.get("data-n-a-ts")
        if not sig or not ts:
            return url
        inner = json.dumps([
            "garturlreq",
            [["X", "X", ["X", "X"], None, None, 1, 1, "US:en", None, 1,
              None, None, None, None, None, 0, 1],
             "X", "X", 1, [1, 1, 1], 1, 1, None, 0, 0, None, 0],
            gn_id, int(ts), sig,
        ])
        freq = json.dumps([[["Fbv4je", inner, None, "generic"]]])
        body = "f.req=" + quote(freq)
        r2 = _http.post(
            "https://news.google.com/_/DotsSplashUi/data/batchexecute",
            data=body, timeout=10,
            headers={**headers,
                     "Content-Type": "application/x-www-form-urlencoded;charset=UTF-8"},
        )
        for line in r2.text.splitlines():
            line = line.strip()
            if line.startswith('[["wrb.fr"'):
                rows = json.loads(line)
                for row in rows:
                    if len(row) > 2 and row[1] == "Fbv4je" and row[2]:
                        real = json.loads(row[2])[1]
                        if real and real.startswith("http"):
                            return real
    except Exception as exc:
        _log(f"Decode Google News falhou ({gn_id[:18]}…): {exc}", "WARN")
    return url

def _resolver_url_real(url):
    return _gn_decode_url(url)

# Seletores de blocos que NÃO são o corpo do artigo — sidebars de "leia
# também", "matérias relacionadas", "mais lidas", comentários, newsletter,
# compartilhamento etc. Esses blocos costumam estar DENTRO do mesmo
# <article>/<main>/.content do site (não só fora dele), então remover só
# nav/footer/header/aside não basta — é preciso removê-los explicitamente
# antes de extrair o texto, ou eles "contaminam" o corpo com texto de
# OUTRAS notícias (causa de geolocalização errada).
_SELETORES_RUIDO = [
    # classes/ids comuns de "leia também" / relacionadas / mais lidas
    "[class*='relacionad']", "[id*='relacionad']",
    "[class*='leia-tambem']", "[class*='leiatambem']", "[id*='leia-tambem']",
    "[class*='leia_tambem']", "[class*='veja-tambem']", "[class*='veja_tambem']",
    "[class*='mais-lidas']", "[class*='maislidas']", "[class*='mais_lidas']",
    "[class*='mais-noticias']", "[class*='mais_noticias']",
    "[class*='widget']", "[class*='sidebar']", "[id*='sidebar']",
    "[class*='recommend']", "[class*='recomenda']",
    "[class*='related']", "[id*='related']",
    "[class*='trending']", "[class*='popular']",
    "[class*='newsletter']", "[class*='comment']", "[id*='comment']",
    "[class*='compartilh']", "[class*='share']",
    "[class*='outras-noticias']", "[class*='outras_noticias']",
    "[class*='materias-relacionadas']",
    "[class*='post-relacionado']", "[class*='posts-relacionados']",
    "[class*='also-read']", "[class*='read-more']", "[class*='readmore']",
    "[class*='taboola']", "[class*='outbrain']",  # widgets de "conteúdo patrocinado"
    "[class*='breadcrumb']", "[class*='tags']", "[class*='tag-list']",
    "[class*='autor-box']", "[class*='author-box']", "[class*='bio-autor']",
]

# Frases que marcam o FIM do corpo real do artigo e o início de chamadas para
# OUTRAS matérias (mesmo dentro do próprio <article>). Cortamos o texto no
# primeiro ponto em que uma dessas frases aparece, para nunca incluir o que
# vem depois — que tipicamente é a lista de "leia também".
_MARCADORES_FIM_CORPO = re.compile(
    r'\b(?:leia\s+tamb[eé]m|leia\s+mais|veja\s+tamb[eé]m|veja\s+mais|'
    r'assista\s+tamb[eé]m|confira\s+tamb[eé]m|saiba\s+mais|'
    r'mais\s+not[ií]cias|mat[eé]rias?\s+relacionadas?|not[ií]cias?\s+relacionadas?|'
    r'compartilhe\s+essa\s+not[ií]cia|compartilhar\s+essa\s+not[ií]cia|'
    r'o\s+que\s+voc[eê]\s+achou\s+da\s+reportagem)\b',
    re.IGNORECASE
)

def _remover_ruido(soup):
    """Remove do soup os blocos que tipicamente contêm chamadas para OUTRAS
    matérias (relacionadas, mais lidas, sidebars etc.), que não fazem parte
    do corpo real do artigo mas costumam estar dentro do mesmo container."""
    for sel in _SELETORES_RUIDO:
        try:
            for tag in soup.select(sel):
                tag.decompose()
        except Exception:
            continue
    return soup

def _cortar_no_fim_do_corpo(texto):
    """Corta o texto no primeiro marcador de 'leia também'/'relacionadas' etc.
    — qualquer coisa depois disso tende a ser chamada de OUTRA matéria que
    sobreviveu à remoção de ruído por seletor (texto sem marcação clara)."""
    if not texto:
        return texto
    m = _MARCADORES_FIM_CORPO.search(texto)
    if m and m.start() > 80:  # exige um mínimo de corpo real antes do corte
        return texto[:m.start()].strip()
    return texto

def _extrair_texto_puro(url):
    if not _DEPS_OK:
        return None
    url_real = _resolver_url_real(url)
    try:
        r = _http.get(url_real, timeout=12, headers={
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
            "Accept-Language": "pt-BR,pt;q=0.9",
        })
        soup = _bs4.BeautifulSoup(r.text, "html.parser")
        for tag in soup(["script", "style", "nav", "footer", "header", "aside"]):
            tag.decompose()
        # remove sidebars de "leia também" / relacionadas / mais lidas / etc.
        # ANTES de extrair texto — eles costumam estar dentro do mesmo
        # <article>/<main>/.content do artigo de verdade.
        _remover_ruido(soup)

        # Seletores em ordem de CONFIANÇA decrescente: os específicos de artigo
        # primeiro (mais provável de ser só o corpo da matéria); os genéricos
        # (main, .content, "p" solto) só entram como último recurso, pois são
        # os que mais sofrem contaminação por widgets sem classe reconhecível.
        selectors_especificos = [
            "article", ".article-body", ".post-content", ".entry-content",
            ".materia", ".noticia", "#noticia", ".corpo", ".story", ".news-content",
        ]
        selectors_genericos = [
            ".texto", ".content", "main", ".text",
            "article p", ".article-body p", ".content p", "main p", ".materia p", "p",
        ]
        text = ""
        for sel in selectors_especificos + selectors_genericos:
            elements = soup.select(sel)
            if elements:
                text = " ".join(p.get_text(" ", strip=True) for p in elements[:25])
                if len(text) > 150:
                    break
        if not text:
            text = soup.get_text(" ", strip=True)
        # Limpeza extra
        text = re.sub(r'\s+', ' ', text).strip()
        # corta no primeiro marcador de "leia também"/relacionadas (segunda
        # camada de defesa, para o caso de a sidebar não ter classe reconhecível)
        text = _cortar_no_fim_do_corpo(text)
        return text[:5000]
    except Exception as exc:
        _log(f"Erro ao ler corpo ({url_real[:60]}): {exc}", "WARN")
        return None

def geocodificar_com_corpo(titulo, url, cidade):
    """Lê o corpo da notícia e busca bairros diretamente — retorna lista multi-bairro."""
    corpo = _extrair_texto_puro(url)
    if not corpo:
        _log(f"Falha ao ler corpo de {url[:80]}", "WARN")
        return None
    _log(f"Corpo lido ({len(corpo)} chars)", "GEO")
    texto_completo = f"{titulo} {titulo} {corpo}"
    bairros = buscar_bairros_direto(texto_completo, cidade)
    if bairros:
        nomes = ", ".join(b["nome"] for b in bairros[:4])
        _log(f"GEO-CORPO [{len(bairros)} bairro(s)]: {nomes} | '{titulo[:50]}'", "GEO")
        return bairros
    return None

# ─────────────────────────────────────────────
#  LEITURA DE CORPO COM CACHE + ENRIQUECIMENTO EM LOTE
# ─────────────────────────────────────────────
def obter_corpo(url):
    """Lê (e cacheia) o corpo de uma notícia. Reaproveita entre ciclos."""
    if not url:
        return ""
    chave = url.split("?")[0]
    with _corpo_lock:
        if chave in _corpo_cache:
            return _corpo_cache[chave]
    corpo = _extrair_texto_puro(url) or ""
    with _corpo_lock:
        _corpo_cache[chave] = corpo
    return corpo

def enriquecer_corpos(noticias):
    """
    Lê o corpo de TODAS as fontes em paralelo e devolve a mesma lista de tuplas
    com o corpo anexado no índice 6. Respeita orçamento de tempo e nº máximo.
    Cada item de entrada: (titulo, link, fonte, data_fmt, dt, resumo)
    Saída: (titulo, link, fonte, data_fmt, dt, resumo, corpo)
    """
    if not _DEPS_OK or not noticias:
        return [tuple(list(n) + [""]) for n in noticias]

    from concurrent.futures import ThreadPoolExecutor, as_completed
    alvos = noticias[:MAX_CORPOS_POR_CICLO]
    corpos = {}
    total = len(alvos)
    feitos = 0
    _publicar_sse("corpos_progresso", {"lendo": True, "feitos": 0, "total": total})
    try:
        with ThreadPoolExecutor(max_workers=CORPOS_WORKERS) as ex:
            futuros = {ex.submit(obter_corpo, n[1]): i for i, n in enumerate(alvos)}
            for fut in as_completed(futuros, timeout=BUDGET_CORPOS_SEG):
                i = futuros[fut]
                try:
                    corpos[i] = fut.result() or ""
                except Exception:
                    corpos[i] = ""
                feitos += 1
                if feitos % 4 == 0 or feitos == total:
                    _publicar_sse("corpos_progresso",
                                  {"lendo": feitos < total, "feitos": feitos, "total": total})
    except Exception as exc:
        _log(f"Leitura de corpos interrompida pelo tempo-limite: {exc}", "WARN")
    _publicar_sse("corpos_progresso", {"lendo": False, "feitos": total, "total": total})

    ok = sum(1 for v in corpos.values() if v)
    _log(f"Corpos lidos: {ok}/{total} (cacheados reaproveitados)", "INFO")

    saida = []
    for i, n in enumerate(noticias):
        corpo = corpos.get(i, "") if i < len(alvos) else ""
        saida.append(tuple(list(n) + [corpo]))
    return saida

def _worker_geo_refinamento():
    """Thread de refinamento: lê corpo e atualiza bairros da notícia."""
    while True:
        with _geo_refine_lock:
            fila_len = len(_geo_refine_queue)
            if not fila_len:
                time.sleep(2)
                continue
            item = _geo_refine_queue.pop(0)
            fila_restante = len(_geo_refine_queue)
        news_id = item.get("id")
        url = item.get("url")
        cidade = item.get("cidade","")
        titulo = item.get("titulo","")
        _publicar_sse("geo_progresso", {"processando": True, "fila": fila_restante, "id": news_id})
        _log(f"Refinando geo [{fila_restante} na fila] '{titulo[:60]}'…", "GEO")
        bairros_corpo = geocodificar_com_corpo(titulo, url, cidade)
        if not bairros_corpo:
            _publicar_sse("geo_progresso", {"processando": fila_restante > 0, "fila": fila_restante, "id": news_id})
            time.sleep(0.5)
            continue
        # tenta extrair a rua do corpo para que _worker_coord_precisa resolva a posição precisa
        # usa o cache (obter_corpo) — já foi lido em geocodificar_com_corpo
        corpo_txt = obter_corpo(url)
        textos_rua = [(f"{titulo} {corpo_txt}".strip(), 1.0)]
        rua_corpo, _, _ = extrair_rua_do_fato(textos_rua) if corpo_txt else (None, None, None)
        with lock:
            for n in estado["noticias"]:
                if n["id"] == news_id:
                    # só atualiza se o corpo encontrou bairros e o titulo não tinha encontrado
                    bairros_atuais = n.get("bairros", [])
                    if not bairros_atuais:
                        n["bairros"] = bairros_corpo
                        n["label"] = bairros_corpo[0]["nome"]
                        n["lat"] = bairros_corpo[0]["lat"]
                        n["lon"] = bairros_corpo[0]["lon"]
                        n["precisao"] = "bairro"
                        n["geo_refinado"] = True
                        n["geo_score"] = 1.0
                        _log(f"GEO refinado [corpo→bairro(s)]: {', '.join(b['nome'] for b in bairros_corpo[:3])} | '{titulo[:50]}'", "GEO")
                        _publicar_sse("geo_update", {
                            "id": news_id,
                            "bairros": bairros_corpo,
                            "lat": bairros_corpo[0]["lat"],
                            "lon": bairros_corpo[0]["lon"],
                            "label": bairros_corpo[0]["nome"],
                            "precisao": "bairro",
                            "geo_score": 1.0,
                        })
                        _enfileirar_coord_precisa(news_id, cidade, bairros_corpo, rua=rua_corpo)
                    break
        _publicar_sse("geo_progresso", {"processando": fila_restante > 0, "fila": fila_restante, "id": news_id})
        time.sleep(0.5)

# ─────────────────────────────────────────────
#  LÓGICA DE BUSCA (com refinamento obrigatório)
# ─────────────────────────────────────────────
def normalizar_texto(texto):
    texto = texto.lower()
    texto = re.sub(r'\s*-\s*[^-]+$', '', texto)
    texto = re.sub(r'[^\w\s]', ' ', texto)
    return re.sub(r'\s+', ' ', texto).strip()

def similaridade(a, b):
    return SequenceMatcher(None, a, b).ratio()

def extrair_palavras(texto):
    stops = {
        'em','de','a','o','e','do','da','no','na','após','para','com','que','um','uma',
        'os','as','se','por','mais','mas','como','está','ser','era','foram','pelo',
        'pela','nos','nas','dos','das','este','esta','esse','essa','isso',
    }
    return [p for p in texto.split() if p not in stops and len(p) > 2]

_EVENTOS_KEYWORDS = {
    "incêndio": ["incendio","fogo","chamas","queimou","ardeu","fumaca"],
    "acidente": ["acidente","batida","colisao","capotou","capotamento","engavetamento",
                 "invadiu","invadiu a","invadiu o","invasao","derrapou","perdeu o controle",
                 "saiu da pista","capotagem"],
    "crime": ["crime","policia","preso","detido","criminoso","bandido","suspeito","flagrante"],
    "homicídio": ["homicidio","morte","morto","morreu","vitima","cadaver","corpo","matar","matou"],
    "tráfico": ["trafico","drogas","entorpecente","cocaina","maconha","crack"],
    "furto/roubo": ["roubo","furto","assalto","roubou","furtou","assaltou"],
    "atropelamento": ["atropelamento","atropelou","atropelado","pedestre"],
    "desaparecimento": ["desaparecido","desapareceu","sumiu","procurado"],
    "enchente": ["enchente","alagamento","inundacao","transbordou","chuva","temporal","deslizamento"],
    "explosão": ["explosao","explodiu","detonou","bomba"],
    "tiroteio": ["tiroteio","tiros","balaco","disparos","fuzilamento"],
    "obra/trânsito": ["obras","transito","interdito","bloqueio","semaforo"],
    "saúde": ["hospital","ubs","medico","paciente","surto","dengue","covid","virus"],
    "política": ["prefeitura","vereador","prefeito","governador","lei","projeto","aprovado"],
    "afogamento": ["afogamento","afogou","se afogou","resgatado no mar","resgatada no mar",
                   "arrastado pela correnteza","arrastada pela correnteza"],
    "queda": ["caiu","cair de","despencou","tombou","desabou","desabamento"],
    "violência doméstica": ["violencia domestica","agressao","espancou","espancado","espancada",
                            "feminicidio","ameacou com"],
    "animal": ["ataque de cachorro","cachorro atacou","mordida","picada de cobra","cobra"],
    "clima/vendaval": ["vendaval","ventania","arvore caiu","arvore cair","raio","granizo"],
}
# Eventos onde algo (veículo, objeto) ENTRA/ATINGE um estabelecimento ou local —
# categoria própria porque é um padrão recorrente em notícias locais e não se
# encaixa bem em "acidente" sozinho (ex.: "carro invade pizzaria").
_EVENTOS_KEYWORDS["acidente"] += ["invadiu uma","invadiu um"]


def _detectar_eventos(texto_norm):
    encontrados = set()
    for tipo, palavras in _EVENTOS_KEYWORDS.items():
        for p in palavras:
            if p in texto_norm:
                encontrados.add(tipo)
                break
    return encontrados

# Categorias de evento que costumam descrever o MESMO fato visto de ângulos
# diferentes (ex.: uma matéria foca na prisão = "crime", outra foca nos tiros
# = "tiroteio", mas é o mesmo episódio policial). Usado só para a comparação
# de "mesmo evento" entre duas notícias — não afeta o rótulo exibido.
_FAMILIAS_EVENTO = [
    {"crime", "tiroteio", "furto/roubo", "homicídio", "tráfico", "violência doméstica"},
    {"acidente", "atropelamento"},
]
_EVENTO_PARA_FAMILIA = {}
for _i, _fam in enumerate(_FAMILIAS_EVENTO):
    for _t in _fam:
        _EVENTO_PARA_FAMILIA[_t] = _i

def _mesma_familia_evento(ev1, ev2):
    """True se ev1 e ev2 têm pelo menos uma categoria em comum OU pertencem
    à mesma família de eventos correlatos (ex.: crime + tiroteio)."""
    if ev1 & ev2:
        return True
    fams1 = {_EVENTO_PARA_FAMILIA[t] for t in ev1 if t in _EVENTO_PARA_FAMILIA}
    fams2 = {_EVENTO_PARA_FAMILIA[t] for t in ev2 if t in _EVENTO_PARA_FAMILIA}
    return bool(fams1 & fams2)

# ─────────────────────────────────────────────
#  FINGERPRINT DE CORPO (entidades próprias + números + tokens)
#  Permite reconhecer o MESMO fato mesmo com títulos bem diferentes,
#  sem usar IA — apenas comparando o que os textos têm em comum.
# ─────────────────────────────────────────────
_STOP_ENT = {
    "O","A","Os","As","Um","Uma","De","Do","Da","Dos","Das","No","Na","Em","Por",
    "Para","Com","Que","Como","Foi","Está","Após","Segundo","Polícia","Política",
    "Brasil","Veja","Leia","Saiba","Confira","Entenda","Assista","Foto","Vídeo",
    "Imagem","Reportagem","Notícia","Notícias","Cidade","Estado","País","Região",
}

def _extrair_entidades(texto_bruto):
    """
    Extrai 'entidades próprias': sequências de palavras Capitalizadas
    (ex.: 'Governador Valadares', 'Minas Gerais', 'Praia do Morro').
    Trabalha sobre o texto ORIGINAL (com maiúsculas), normaliza só na saída.
    """
    if not texto_bruto:
        return set()
    ents = set()
    # sequências de Capitalizadas, permitindo conectores minúsculos curtos (de, do, da)
    padrao = re.compile(
        r'\b([A-ZÀ-Ý][a-zà-ÿ]{1,}(?:\s+(?:d[aeo]s?|e)?\s*[A-ZÀ-Ý][a-zà-ÿ]{1,}){0,3})')
    for m in padrao.finditer(texto_bruto):
        frase = m.group(1).strip()
        palavras = frase.split()
        # descarta entidades de 1 palavra muito comuns/genéricas
        if len(palavras) == 1 and palavras[0] in _STOP_ENT:
            continue
        norm = normalizar(frase)
        if len(norm) >= 4:
            ents.add(norm)
    return ents

def _extrair_numeros(texto):
    """Números 'específicos' (idades, quantidades): bons identificadores de fato."""
    return set(re.findall(r'(?<!\d)(\d{1,4})(?!\d)', texto or ""))

def fingerprint_corpo(titulo, corpo):
    """Monta a assinatura de uma notícia a partir de título + corpo."""
    bruto = f"{titulo}. {corpo}"
    ents = _extrair_entidades(bruto)
    nums = _extrair_numeros(bruto)
    toks = set(extrair_palavras(normalizar_texto(corpo or titulo)))
    return {"ents": ents, "nums": nums, "toks": toks}

def _jaccard(a, b):
    if not a and not b:
        return 0.0
    u = a | b
    return len(a & b) / len(u) if u else 0.0

def similaridade_corpo(fp1, fp2):
    """
    Similaridade combinada entre dois fingerprints de corpo.
    Retorna (score, ents_comuns).
    """
    if not fp1 or not fp2:
        return 0.0, set()
    ents_comuns = fp1["ents"] & fp2["ents"]
    ent_j = _jaccard(fp1["ents"], fp2["ents"])
    tok_j = _jaccard(fp1["toks"], fp2["toks"])
    nums_comuns = fp1["nums"] & fp2["nums"]
    # números em comum: satura em ~3
    num_score = min(len(nums_comuns), 3) / 3.0
    score = PESO_ENT * ent_j + PESO_TOK * tok_j + PESO_NUM * num_score
    return score, ents_comuns

def _titulo_limpo(t):
    """Remove o sufixo de veículo no padrão 'Título - Veículo' (Google News),
    que atrapalha a comparação de títulos do mesmo fato."""
    if not t:
        return t
    if " - " in t:
        base, _, suf = t.rpartition(" - ")
        if base and 1 <= len(suf.split()) <= 6:
            return base.strip()
    return t

def mesmo_fato_avancado(t1, t2, f1="", f2="", dt1=None, dt2=None, fp1=None, fp2=None,
                         texto1=None, texto2=None, loc1=None, loc2=None):
    if f1 and f2 and f1 == f2:
        return False, 0.0, []
    # compara os títulos SEM o sufixo do veículo
    n1, n2 = normalizar_texto(_titulo_limpo(t1)), normalizar_texto(_titulo_limpo(t2))
    seq_sim = similaridade(n1, n2)
    if seq_sim >= 0.90:
        return True, seq_sim, [f"Títulos quase idênticos ({seq_sim:.0%})"]
    p1, p2 = set(extrair_palavras(n1)), set(extrair_palavras(n2))
    jaccard = len(p1 & p2) / len(p1 | p2) if p1 | p2 else 0

    # ── EVENTO e LOCAL: detectados sobre o TEXTO COMPLETO (título + resumo +
    #    corpo) quando disponível, não só o título. Uma notícia pode descrever
    #    o mesmo fato com um título que não cita o tipo de evento ou o bairro
    #    explicitamente (ex.: "Carro invade pizzaria" vs "Menino de 12 anos
    #    dirigia veículo que invadiu pizzaria"), mas o corpo da matéria cita. ──
    texto_evlocal_1 = normalizar_texto(texto1) if texto1 else n1
    texto_evlocal_2 = normalizar_texto(texto2) if texto2 else n2
    ev1, ev2 = _detectar_eventos(texto_evlocal_1), _detectar_eventos(texto_evlocal_2)
    ev_comuns = ev1 & ev2
    evento_ok = _mesma_familia_evento(ev1, ev2)
    time_ok = False
    if dt1 and dt2:
        diff_h = abs((dt1 - dt2).total_seconds()) / 3600
        time_ok = diff_h < 72
    # loc1/loc2 podem vir pré-computados (agrupar_fatos calcula 1x por notícia
    # em vez de recalcular a cada par i,j — mais barato com texto completo)
    if loc1 is None:
        res1 = buscar_bairros_direto(texto1 if texto1 else n1, estado["cidade"])
        loc1 = {normalizar(b["nome"]) for b in res1} if res1 else set()
    if loc2 is None:
        res2 = buscar_bairros_direto(texto2 if texto2 else n2, estado["cidade"])
        loc2 = {normalizar(b["nome"]) for b in res2} if res2 else set()
    loc_comuns = loc1 & loc2
    local_ok = len(loc_comuns) > 0

    ev_txt = ", ".join(ev_comuns) if ev_comuns else (
        ", ".join(sorted(ev1 | ev2)) if evento_ok else ""
    )

    # ── CORRELAÇÃO POR CORPO (sem IA): casa o MESMO fato mesmo com títulos
    #    bem diferentes, comparando entidades/nomes/números dos textos. ──
    corpo_score, ents_comuns = (0.0, set())
    if fp1 and fp2:
        corpo_score, ents_comuns = similaridade_corpo(fp1, fp2)
        compativel_no_tempo = (time_ok or dt1 is None or dt2 is None)
        forte_corpo = (
            len(ents_comuns) >= ENT_COMUNS_MIN
            and _jaccard(fp1["ents"], fp2["ents"]) >= ENT_JACCARD_MIN
            and evento_ok
            and compativel_no_tempo
        )
        # 3+ nomes/lugares específicos em comum já é um sinal forte por si só
        muitas_ents = len(ents_comuns) >= 3 and compativel_no_tempo
        # similaridade de TOKENS sozinha (palavras comuns no texto) não é um sinal
        # confiável sem nenhuma entidade própria em comum — dois fatos diferentes
        # do mesmo bairro/assunto (ex.: dois crimes distintos) compartilham muito
        # vocabulário sem serem o mesmo fato. Por isso exigimos ao menos 1 entidade
        # em comum e compatibilidade de tempo também neste caminho.
        corpo_similar_ok = (
            corpo_score >= SIM_CORPO_MERGE
            and len(ents_comuns) >= 1
            and compativel_no_tempo
        )
        if forte_corpo or muitas_ents or corpo_similar_ok:
            amostra = ", ".join(list(ents_comuns)[:3]) if ents_comuns else ""
            razoes = [f"Texto das matérias muito parecido ({corpo_score:.0%})"]
            if amostra:
                razoes.append(f"Nomes/lugares em comum: {amostra}")
            if ev_txt:
                razoes.append(f"Mesmo tipo de evento: {ev_txt}")
            return True, round(min(max(corpo_score, 0.7), 1.0), 3), razoes

    # Mesmo evento + mesmo local citados em QUALQUER parte do texto lido
    # (não apenas no título) já é um sinal forte de que é o mesmo fato.
    if evento_ok and local_ok and (time_ok or dt1 is None or dt2 is None):
        score = max(0.82 + jaccard * 0.18, 0.82)
        razoes = [f"Mesmo tipo de evento: {ev_txt}", f"Mesmo local citado: {', '.join(list(loc_comuns)[:2])}"]
        if time_ok: razoes.append("Publicadas quase ao mesmo tempo")
        return True, min(score, 1.0), razoes

    # Mesmo sem bater nenhuma categoria fechada de evento (a lista de keywords
    # nunca cobre tudo), MESMO local citado + pelo menos 2 entidades próprias
    # em comum (nomes, lugares específicos) e tempo compatível já é um sinal
    # forte o suficiente — evita depender só do dicionário de eventos.
    if local_ok and len(ents_comuns) >= 2 and (time_ok or dt1 is None or dt2 is None):
        score = max(0.75 + jaccard * 0.15, 0.75)
        razoes = [f"Mesmo local citado: {', '.join(list(loc_comuns)[:2])}",
                  f"Nomes/lugares em comum: {', '.join(list(ents_comuns)[:3])}"]
        if time_ok: razoes.append("Publicadas quase ao mesmo tempo")
        return True, min(score, 1.0), razoes

    score = (seq_sim * PESO_SEQ + jaccard * PESO_JACCARD + (PESO_EVENTO if evento_ok else 0) + (PESO_LOCAL if local_ok else 0))
    penalidade_tempo = 1.0
    if time_ok:
        score += 0.05
    elif dt1 and dt2:
        # datas bem distantes (mais de uma semana) reduzem a chance de ser o
        # mesmo fato — evita unir, por exemplo, duas prisões diferentes no
        # mesmo bairro só porque o evento e o local citados coincidem.
        diff_dias = abs((dt1 - dt2).total_seconds()) / 86400
        if diff_dias > 7:
            penalidade_tempo = 0.6
            score *= penalidade_tempo
    if corpo_score: score = max(score, corpo_score * 0.9 * penalidade_tempo)
    razoes = []
    if seq_sim > 0.55: razoes.append(f"Títulos parecidos ({seq_sim:.0%})")
    if jaccard > 0.30: razoes.append(f"Mesmo assunto no título ({jaccard:.0%})")
    if ev_txt: razoes.append(f"Mesmo tipo de evento: {ev_txt}")
    if loc_comuns: razoes.append(f"Mesmo local citado: {', '.join(list(loc_comuns)[:2])}")
    if corpo_score >= 0.20: razoes.append(f"Texto das matérias parecido ({corpo_score:.0%})")
    if time_ok: razoes.append("Publicadas quase ao mesmo tempo")
    return score >= SIMILARIDADE_MINIMA, round(min(score, 1.0), 3), razoes

def mesmo_fato(t1, t2):
    ok, _, _ = mesmo_fato_avancado(t1, t2)
    return ok

def _fontes_rss(cidade):
    q = cidade.replace(" ", "+")
    qp = cidade.replace(" ", "%20")
    return [
        f"https://news.google.com/rss/search?q={q}&hl=pt-BR&gl=BR&ceid=BR:pt-419",
        f"https://news.google.com/rss/search?q={q}+acidente&hl=pt-BR&gl=BR&ceid=BR:pt-419",
        f"https://news.google.com/rss/search?q={q}+crime+policia&hl=pt-BR&gl=BR&ceid=BR:pt-419",
        f"https://news.google.com/rss/search?q={q}+incendio+transito+obra&hl=pt-BR&gl=BR&ceid=BR:pt-419",
        f"https://news.google.com/rss/search?q={q}+prefeitura+saude+educacao&hl=pt-BR&gl=BR&ceid=BR:pt-419",
        f"https://news.google.com/rss/search?q={q}+defesa+civil+temporal+enchente&hl=pt-BR&gl=BR&ceid=BR:pt-419",
        f"https://www.folhaonline.es/feed/?s={qp}",
        f"https://www.aquinoticias.com/?s={qp}&feed=rss2",
        "https://www.folhavitoria.com.br/rss.xml",
        "https://tribunaonline.com.br/feed",
        "https://www.seculodiario.com.br/feed",
        "https://www.gazetaonline.com.br/rss.xml",
        "https://www.a-gazeta.com.br/rss.xml",
        "https://g1.globo.com/rss/g1/espirito-santo/",
        "https://agenciabrasil.ebc.com.br/rss/ultimasnoticias/feed.xml",
    ]

def _nome_fonte_de_link(link):
    """Deriva o nome do veículo a partir do domínio do link real."""
    try:
        from urllib.parse import urlparse
        host = urlparse(link).netloc.replace("www.", "")
        # remove TLDs comuns e pega o miolo
        partes = host.split(".")
        nome = partes[0] if partes else host
        return nome.replace("-", " ").title() if nome else host
    except Exception:
        return ""

def _parsear_feed(url, cidade_lower, limite):
    try:
        feed = feedparser.parse(url, request_headers={"User-Agent": "Arkadia/4.0 (monitor-noticias-mapa)"})
    except Exception:
        return []
    noticias = []
    for item in feed.entries:
        titulo = getattr(item, "title", "") or ""
        if not titulo:
            continue
        resumo = getattr(item, "summary", "") or ""
        if cidade_lower not in titulo.lower() and cidade_lower not in resumo.lower():
            continue
        link = getattr(item, "link", "") or ""
        fonte = ""
        if hasattr(item, "source") and hasattr(item.source, "title"):
            fonte = item.source.title or ""
        if not fonte:
            ft = (feed.feed.get("title","") or "")
            # feeds agregadores (Google/Bing) não identificam o veículo: usa o domínio
            if ("news.google" in url) or ("bing.com" in url) or not ft:
                fonte = _nome_fonte_de_link(link) or ft or "Fonte desconhecida"
            else:
                fonte = ft
        dp = getattr(item, "published_parsed", None)
        if dp:
            dt = datetime(*dp[:6])
            if dt < limite:
                continue
            data_fmt = dt.strftime("%d/%m %H:%M")
        else:
            dt, data_fmt = None, "—"
        # resumo do RSS limpo de HTML (frequentemente cita o bairro)
        resumo_limpo = re.sub(r'<[^>]+>', ' ', resumo)
        resumo_limpo = re.sub(r'\s+', ' ', resumo_limpo).strip()
        noticias.append((titulo, link, fonte, data_fmt, dt, resumo_limpo))
    return noticias

def buscar_noticias(cidade, horas_filtro):
    from concurrent.futures import ThreadPoolExecutor, as_completed
    limite = datetime.now() - timedelta(hours=horas_filtro)
    cidade_lower = cidade.lower()
    urls = _fontes_rss(cidade)
    todas, vistas = [], set()
    ok_feeds = 0; vazios = 0; falhas = 0
    with ThreadPoolExecutor(max_workers=10) as ex:
        futuros = {ex.submit(_parsear_feed, u, cidade_lower, limite): u for u in urls}
        for fut in as_completed(futuros, timeout=25):
            try:
                itens = fut.result()
                if itens: ok_feeds += 1
                else: vazios += 1
                for item in itens:
                    chave = normalizar(item[0])[:80]
                    if chave not in vistas:
                        vistas.add(chave)
                        todas.append(item)
            except Exception:
                falhas += 1
    todas.sort(key=lambda x: x[4] or datetime.min, reverse=True)
    _log(f"Fontes: {ok_feeds} com resultado · {vazios} sem · {falhas} falha(s) | {len(todas)} itens únicos", "SEARCH")
    return todas

def agrupar_fatos(noticias):
    grupos, usadas = [], set()
    # pré-computa o fingerprint de cada notícia (título + corpo, se houver) e o
    # texto completo (título + resumo + corpo) usado para detectar evento/local
    # com base em TODO o conteúdo lido, não só no título.
    fps = []
    textos_completos = []
    locais_por_item = []  # bairros encontrados no texto completo, pré-computados 1x
    for it in noticias:
        resumo = it[5] if len(it) > 5 and it[5] else ""
        corpo = it[6] if len(it) > 6 else ""
        fps.append(fingerprint_corpo(it[0], corpo))
        texto_completo = f"{it[0]}. {resumo} {corpo}".strip()
        textos_completos.append(texto_completo)
        bairros = buscar_bairros_direto(texto_completo, estado["cidade"])
        locais_por_item.append({normalizar(b["nome"]) for b in bairros} if bairros else set())
    for i, item1 in enumerate(noticias):
        t1, l1, f1, d1, dt1 = item1[0], item1[1], item1[2], item1[3], item1[4]
        if t1 in usadas:
            continue
        grupo = [item1]
        grupo_scores = []
        for j, item2 in enumerate(noticias):
            t2, l2, f2, d2, dt2 = item2[0], item2[1], item2[2], item2[3], item2[4]
            if i == j or t2 in usadas or f1 == f2:
                continue
            ok, score, razoes = mesmo_fato_avancado(
                t1, t2, f1, f2, dt1, dt2, fps[i], fps[j],
                texto1=textos_completos[i], texto2=textos_completos[j],
                loc1=locais_por_item[i], loc2=locais_por_item[j])
            if ok:
                grupo.append(item2)
                grupo_scores.append({"score": score, "razoes": razoes, "fonte": f2})
                usadas.add(t2)
        try:
            grupo.sort(key=lambda x: x[4] or datetime.min)
        except Exception:
            pass
        grupos.append((grupo, grupo_scores))
        usadas.add(t1)
    return grupos

def make_id(titulo):
    return hashlib.md5(titulo.encode("utf-8","ignore")).hexdigest()[:10]

# ─────────────────────────────────────────────
#  RANQUEAMENTO DO LOCAL DO FATO (sem IA)
#  Lê o contexto em volta de cada menção de bairro e distingue:
#   - "fato":       lugar onde o acontecimento ocorreu (perto de verbo de fato)
#   - "residência": onde a pessoa mora / está hospedada / é natural
#   - "menção":     citado sem contexto forte
#  Corrobora por nº de fontes que citam o mesmo lugar.
# ─────────────────────────────────────────────
def _classificar_contexto(janela_norm):
    tem_residencia = any(m in janela_norm for m in _MARCADORES_RESIDENCIA)
    tem_fato = any(v in janela_norm for v in _VERBOS_FATO)
    if tem_fato and not tem_residencia:
        return "fato"
    if tem_residencia and not tem_fato:
        return "residência"
    if tem_fato and tem_residencia:
        return "fato"
    return "menção"

def _papel_por_proximidade(tnorm, s, e, janela=120):
    """
    Classifica a menção de um lugar olhando QUAL marcador está mais COLADO ao
    nome: 'hospedado na <X>' (residência) vence 'visto na <X>' (fato) etc.
    s,e = posição (início/fim) do nome em tnorm.
    """
    ini = max(0, s - janela)
    fim = min(len(tnorm), e + janela)
    win = tnorm[ini:fim]
    nome_ini = s - ini
    nome_fim = e - ini

    def menor_dist(keywords):
        best = None
        for kw in keywords:
            start = 0
            while True:
                p = win.find(kw, start)
                if p < 0:
                    break
                kw_fim = p + len(kw)
                if kw_fim <= nome_ini:        # marcador antes do nome
                    dist = nome_ini - kw_fim
                elif p >= nome_fim:           # marcador depois do nome
                    dist = p - nome_fim
                else:
                    dist = 0
                if best is None or dist < best:
                    best = dist
                start = p + 1
        return best

    dr = menor_dist(_MARCADORES_RESIDENCIA)
    df = menor_dist(_VERBOS_FATO)
    # marcadores de residência costumam vir colados ao nome ("hospedado na X");
    # damos uma pequena tolerância para que vençam um verbo de fato igualmente perto.
    if dr is not None and (df is None or dr <= df + 6):
        return "residência"
    if df is not None:
        return "fato"
    return "menção"

def ranquear_locais_fato(textos_por_fonte, cidade):
    """
    textos_por_fonte: lista de (corpo_ou_texto, peso_fonte). Devolve lista de
    bairros ordenada por relevância como LOCAL DO FATO, com papel e nº de fontes.
    """
    # candidatos válidos = união do que buscar_bairros_direto aceita em cada fonte
    candidatos = {}   # nome_norm → {nome,lat,lon}
    for texto, _ in textos_por_fonte:
        for b in buscar_bairros_direto(texto or "", cidade):
            candidatos[normalizar(b["nome"])] = b
    if not candidatos:
        return []

    JANELA = 90
    agregado = {}  # nome_norm → {score, fontes, papeis, trecho, fonte_idx, tem_fato}
    for idx, (texto, _) in enumerate(textos_por_fonte):
        if not texto:
            continue
        tnorm = normalizar(texto)
        mesmo_tam = (len(tnorm) == len(texto))
        tam_total = len(tnorm)
        for bn, info in candidatos.items():
            padrao = r'(?<![a-z])' + re.escape(bn) + r'(?![a-z])'
            ocorrencias = list(re.finditer(padrao, tnorm))
            if not ocorrencias:
                continue
            ag = agregado.setdefault(bn, {"score": 0.0, "fontes": set(), "papeis": {},
                                          "trecho": None, "fonte_idx": idx, "tem_fato": False})
            ag["fontes"].add(idx)
            for mt in ocorrencias:
                papel = _papel_por_proximidade(tnorm, mt.start(), mt.end())
                ag["papeis"][papel] = ag["papeis"].get(papel, 0) + 1
                peso_base = {"fato": 3.0, "menção": 1.0, "residência": -1.5}[papel]
                # penalidade de posição: textos de fonte costumam ter o corpo
                # real no início; uma menção bem perto do FINAL (último ~12%)
                # do texto lido é mais suspeita de ser ruído residual de
                # sidebar/relacionadas que sobrou da limpeza do scraping —
                # reduzimos seu peso em vez de descartá-la (corroboração por
                # múltiplas fontes ainda pode resgatá-la se for legítima).
                pos_relativa = mt.start() / tam_total if tam_total else 0.0
                if pos_relativa > 0.88 and peso_base > 0:
                    peso_base *= 0.35
                ag["score"] += peso_base
                # guarda o trecho original onde o bairro aparece (prioriza contexto de fato)
                eh_fato = (papel == "fato")
                if ag["trecho"] is None or (eh_fato and not ag["tem_fato"]):
                    ini = max(0, mt.start() - JANELA); fim = mt.end() + JANELA
                    bruto = texto[ini:fim] if mesmo_tam else tnorm[ini:fim]
                    tam_texto = len(texto) if mesmo_tam else len(tnorm)
                    ag["trecho"] = _limpar_trecho(bruto, ini > 0, fim < tam_texto)
                    ag["fonte_idx"] = idx
                    ag["tem_fato"] = eh_fato

    resultado = []
    for bn, ag in agregado.items():
        info = candidatos[bn]
        n_fontes = len(ag["fontes"])
        # corroboração: várias fontes citando o mesmo lugar aumentam a confiança
        score = ag["score"] * (1 + 0.5 * (n_fontes - 1))
        papeis = ag["papeis"]
        # papel final = o mais frequente entre as ocorrências (desempate: fato > menção > residência)
        prioridade = {"fato": 0, "menção": 1, "residência": 2}
        papel = max(papeis.items(), key=lambda kv: (kv[1], -prioridade[kv[0]]))[0] if papeis else "menção"
        resultado.append({
            "nome": info["nome"], "lat": info["lat"], "lon": info["lon"],
            "score": round(score, 2), "papel": papel, "fontes": n_fontes,
            "trecho": ag["trecho"], "fonte_idx": ag["fonte_idx"],
        })

    # ordena: fato > menção > residência; dentro de cada grupo, por score
    ordem_papel = {"fato": 0, "menção": 1, "residência": 2}
    resultado.sort(key=lambda x: (ordem_papel[x["papel"]], -x["score"]))

    # se existe ao menos um "fato", remove menções fracas de fonte única (ruído)
    tem_fato = any(r["papel"] == "fato" for r in resultado)
    if tem_fato:
        resultado = [r for r in resultado
                     if r["papel"] == "fato"
                     or r["fontes"] >= 2
                     or r["score"] >= 2.0]
    return resultado

# ─────────────────────────────────────────────
#  EXTRAÇÃO DA RUA DO FATO (sem IA)
#  Procura vias ("Rua/Avenida/Rodovia… <Nome>") próximas de verbos de fato.
#  A POSIÇÃO precisa é resolvida depois pelo Nominatim (fonte confiável).
# ─────────────────────────────────────────────
_TIPO_VIA = (r'(?:[Rr]ua|[Aa]venida|[Aa]v\.?|[Tt]ravessa|[Rr]odovia|[Rr]od\.?|'
             r'[Ee]strada|[Aa]lameda|[Pp]ra[çc]a|[Ll]argo|[Bb]eco|[Vv]iela|[Ll]adeira)')
_RUA_RE = re.compile(
    _TIPO_VIA + r'\s+((?:d[aeo]s?\s+)?[A-ZÀ-Ý0-9][\wÀ-ÿ.\'\-]*'
    r'(?:\s+(?:d[aeo]s?\s+|e\s+)?[A-ZÀ-Ý0-9][\wÀ-ÿ.\'\-]*){0,4})')

def _limpar_trecho(s, cortado_esq=True, cortado_dir=True):
    """Limpa um trecho de texto para exibição.
    Só remove a palavra das pontas quando a janela REALMENTE foi cortada no
    meio dela (cortado_esq/cortado_dir) — quando a janela já começa/termina no
    limite do texto original não há palavra cortada para remover.
    Nunca devolve vazio só por causa do corte: preferimos manter o trecho
    inteiro a perder a citação (era a causa de trechos "desaparecendo")."""
    s = re.sub(r'\s+', ' ', s or '').strip()
    if not s:
        return ''
    palavras = s.split(' ')
    # só corta se sobrarem palavras suficientes depois do corte
    if cortado_esq and len(palavras) > 4:
        palavras = palavras[1:]
    if cortado_dir and len(palavras) > 4:
        palavras = palavras[:-1]
    s2 = ' '.join(palavras).strip()
    if not s2:
        s2 = s  # nunca devolve vazio
    return '…' + s2 + '…'

def extrair_rua_do_fato(textos_por_fonte):
    """Devolve (nome_da_via, trecho, fonte_idx) ou (None, None, None)."""
    cont = {}
    for idx, (texto, _) in enumerate(textos_por_fonte):
        if not texto:
            continue
        for m in _RUA_RE.finditer(texto):
            tipo = m.group(0).split()[0]
            nome = m.group(1).strip(" .,-")
            if len(nome) < 3:
                continue
            full = f"{tipo[:1].upper()}{tipo[1:]} {nome}".strip()
            key = normalizar(full)
            janela_norm = normalizar(texto[max(0, m.start()-120): m.end()+120])
            perto_fato = any(v in janela_norm for v in _VERBOS_FATO)
            perto_resid = any(r in janela_norm for r in _MARCADORES_RESIDENCIA)
            ag = cont.setdefault(key, {"nome": full, "score": 0.0, "fontes": set(),
                                       "trecho": None, "fonte_idx": idx, "tem_fato": False})
            ag["fontes"].add(idx)
            ag["score"] += (3.0 if perto_fato else 1.0) - (1.5 if perto_resid else 0.0)
            # guarda o trecho original (prioriza a ocorrência perto de um verbo de fato)
            if ag["trecho"] is None or (perto_fato and not ag["tem_fato"]):
                ini = max(0, m.start()-90); fim = m.end()+90
                trecho = texto[ini:fim]
                ag["trecho"] = _limpar_trecho(trecho, ini > 0, fim < len(texto))
                ag["fonte_idx"] = idx
                ag["tem_fato"] = perto_fato
    if not cont:
        return None, None, None
    melhor = max(cont.values(), key=lambda x: x["score"] * (1 + 0.5*(len(x["fontes"])-1)))
    if melhor["score"] >= 3.0 or len(melhor["fontes"]) >= 2:
        trecho_final = melhor["trecho"]
        if not trecho_final:
            # rede de segurança: nunca devolver a via sem ao menos tentar achar o trecho de novo
            trecho_final, _idx2 = _trecho_do_termo(textos_por_fonte, melhor["nome"])
        return melhor["nome"], trecho_final, melhor["fonte_idx"]
    return None, None, None

def _trecho_do_termo(textos_por_fonte, termo):
    """Acha no texto ORIGINAL o trecho onde o bairro/termo aparece (priorizando
    a ocorrência perto de um verbo de fato). Retorna (trecho, fonte_idx)."""
    if not termo:
        return None, None
    termo_n = normalizar(termo)
    melhor = None; melhor_idx = None; melhor_fato = False
    for idx, (texto, _) in enumerate(textos_por_fonte):
        if not texto:
            continue
        tn = normalizar(texto)
        mesmo_tam = (len(tn) == len(texto))
        for m in re.finditer(r'(?<![a-z])' + re.escape(termo_n) + r'(?![a-z])', tn):
            ini = max(0, m.start()-90); fim = m.end()+90
            jn = tn[ini:fim]
            tem_fato = any(v in jn for v in _VERBOS_FATO)
            if mesmo_tam:
                snip = texto[ini:fim]
            else:
                snip = jn
            if melhor is None or (tem_fato and not melhor_fato):
                melhor = _limpar_trecho(snip, ini > 0, fim < len(tn)); melhor_idx = idx; melhor_fato = tem_fato
                if tem_fato:
                    return melhor, melhor_idx
    return melhor, melhor_idx

def _montar_resumo(grupo):
    """Resumo curto do fato (sem IA): melhor resumo do RSS ou início do corpo."""
    cands = [x[5] for x in grupo if len(x) > 5 and x[5]]
    melhor = max(cands, key=len) if cands else ""
    if len(melhor) < 40:
        corpos = [x[6] for x in grupo if len(x) > 6 and x[6]]
        if corpos:
            melhor = max(corpos, key=len)
    melhor = re.sub(r'<[^>]+>', ' ', melhor)
    melhor = re.sub(r'\s+', ' ', melhor).strip()
    if len(melhor) > 260:
        corte = melhor[:260]
        p = corte.rfind('. ')
        melhor = (corte[:p+1] if p > 120 else corte).strip() + '…'
    return melhor

def montar_noticia(grupo_tuple, cidade):
    grupo, grupo_scores = grupo_tuple
    titulo_base = max(grupo, key=lambda x: len(x[0]))[0]

    # ── GEOCODIFICAÇÃO: lê o CORPO de TODAS as fontes e ranqueia o LOCAL DO FATO ──
    # Cada fonte entra com: título (peso) + resumo do RSS + corpo do artigo.
    textos_por_fonte = []
    for x in grupo:
        titulo_x = x[0]
        resumo_x = x[5] if len(x) > 5 and x[5] else ""
        corpo_x  = x[6] if len(x) > 6 and x[6] else ""
        texto = f"{titulo_x}. {resumo_x} {corpo_x}".strip()
        textos_por_fonte.append((texto, 1.0))

    bairros_rank = ranquear_locais_fato(textos_por_fonte, cidade)

    # fallback adicional: se o ranking não achou nada, tenta a busca direta antiga
    if not bairros_rank:
        texto_geo = f"{titulo_base} {titulo_base} " + " ".join(t for t, _ in textos_por_fonte)
        for b in buscar_bairros_direto(texto_geo, cidade):
            bairros_rank.append({**b, "score": 1.0, "papel": "menção", "fontes": 1})

    # coords de fallback = centro da cidade
    base = _coords_cidade(cidade)
    clat, clon = base if base else (-20.67, -40.51)

    # marcador PRINCIPAL = melhor local do fato (residência/hospedagem é
    # despriorizada na escolha do principal, mas continua na lista de citados).
    principais = [b for b in bairros_rank if b.get("papel") != "residência"]
    if principais:
        primario = principais[0]
    elif bairros_rank:
        primario = bairros_rank[0]
    else:
        primario = None

    if primario:
        lat, lon = primario["lat"], primario["lon"]
        label = primario["nome"]
        precisao = "bairro"
        geo_score = 1.0
        # mantém SOMENTE o local principal (não plota os demais)
        primario["principal"] = True
        bairros_rank = [primario]
    else:
        lat, lon = clat, clon
        label = cidade.title()
        precisao = "cidade"
        geo_score = 0.0

    # rua/avenida do fato (posição precisa é resolvida depois pelo Nominatim)
    rua_fato, rua_trecho, rua_fidx = (extrair_rua_do_fato(textos_por_fonte) if primario else (None, None, None))
    # trecho da matéria onde o BAIRRO foi identificado: usa o capturado no ranqueamento
    if primario and primario.get("trecho"):
        local_trecho, local_fidx = primario["trecho"], primario.get("fonte_idx")
    elif primario:
        local_trecho, local_fidx = _trecho_do_termo(textos_por_fonte, primario["nome"])
    else:
        local_trecho, local_fidx = None, None

    def _fonte_de(idx):
        try: return grupo[idx][2]
        except Exception: return ""

    confianca_corr = 0.0
    if grupo_scores:
        confianca_corr = sum(s["score"] for s in grupo_scores) / len(grupo_scores)
    razoes_unicas = []
    for gs in grupo_scores:
        for r in gs.get("razoes",[]):
            if r not in razoes_unicas:
                razoes_unicas.append(r)

    # datas: usa a publicação mais recente do grupo para o tempo relativo
    dts = [x[4] for x in grupo if len(x) > 4 and x[4]]
    dt_recente = max(dts) if dts else None
    data_iso = dt_recente.isoformat() if dt_recente else None
    data_fmt = dt_recente.strftime("%d/%m %H:%M") if dt_recente else (grupo[0][3] if grupo else "—")

    news_id = make_id(titulo_base)
    return {
        "id": news_id, "titulo": titulo_base, "fontes": [x[2] for x in grupo],
        "links": [x[1] for x in grupo], "data": data_fmt, "data_iso": data_iso,
        "multi": len(grupo) >= 2, "rua": rua_fato,
        "confianca_corr": round(confianca_corr, 2), "razoes_corr": razoes_unicas,
        # estatísticas detalhadas (mostradas no botão "Estatísticas" do popup)
        "estatisticas": {
            "n_fontes": len(grupo),
            "confianca": round(confianca_corr, 2),
            "razoes": razoes_unicas,
            "precisao": precisao,
            "local": label,
            "local_trecho": local_trecho,
            "local_fonte": _fonte_de(local_fidx) if local_fidx is not None else "",
            "rua": rua_fato,
            "rua_trecho": rua_trecho,
            "rua_fonte": _fonte_de(rua_fidx) if rua_fidx is not None else "",
            "geo_score": round(geo_score, 2),
        },
        # campo principal (local do fato ou cidade)
        "lat": lat, "lon": lon,
        "label": label, "precisao": precisao,
        "geo_refinado": bool(any(x[6] if len(x) > 6 else "" for x in grupo)),
        "geo_score": round(geo_score, 2),
        "evidencias_geo": [f"local principal: {label}" + (f" / via: {rua_fato}" if rua_fato else "")] if primario else [],
        # somente o local principal é plotado
        "bairros": bairros_rank,
        "detalhes": [{"titulo": x[0], "fonte": x[2], "link": x[1], "data": x[3],
                      "score": (grupo_scores[i-1]["score"] if i > 0 else 1.0),
                      "razoes": (grupo_scores[i-1]["razoes"] if i > 0 else [])} for i, x in enumerate(grupo)],
    }

# ─────────────────────────────────────────────
#  SSE E LOGS
# ─────────────────────────────────────────────
_sse_clients = []
_sse_clients_lock = threading.Lock()
_log_buffer = []
_log_lock = threading.Lock()

def _log(msg, level="INFO"):
    ts = datetime.now().strftime("%H:%M:%S")
    line = {"ts": ts, "level": level, "msg": msg}
    with _log_lock:
        _log_buffer.append(line)
        if len(_log_buffer) > 200:
            _log_buffer.pop(0)
    prefix = {"INFO":"ℹ️ ","OK":"✅ ","WARN":"⚠️  ","ERR":"✗  ",
              "SEARCH":"🔍 ","GEO":"📍 ","SCRAPE":"🌐 "}.get(level,"   ")
    print(f"[{ts}] {prefix}{msg}")
    _publicar_sse("log", line)

def _publicar_sse(evento, payload_dict):
    import json as _json
    msg = f"event: {evento}\ndata: {_json.dumps(payload_dict, ensure_ascii=False)}\n\n"
    with _sse_clients_lock:
        mortos = []
        for q in _sse_clients:
            try:
                q.put_nowait(msg)
            except Exception:
                mortos.append(q)
        for q in mortos:
            _sse_clients.remove(q)

# ─────────────────────────────────────────────
#  CICLO PRINCIPAL DE BUSCA (refinamento obrigatório)
# ─────────────────────────────────────────────
def ciclo_busca():
    ultimo_ciclo = 0.0
    while True:
        with lock:
            cidade = estado["cidade"]
            horas = estado["horas_filtro"]
            intervalo = estado["intervalo"]
            buscando = estado["buscando"]
            busca_imediata = estado.get("busca_imediata", False)
        agora = time.time()
        deve_buscar = busca_imediata or (agora - ultimo_ciclo >= intervalo * 60)
        if buscando or not deve_buscar:
            time.sleep(2)
            continue
        with lock:
            estado["buscando"] = True
            estado["busca_imediata"] = False
        try:
            _log(f"Iniciando busca sobre '{cidade}'…", "SEARCH")
            _publicar_sse("buscando", {"buscando": True, "cidade": cidade})
            raw = buscar_noticias(cidade, horas)
            _log(f"{len(raw)} itens brutos coletados", "INFO")
            # Lê o corpo de TODAS as fontes (paralelo + cache) ANTES de agrupar,
            # para que títulos diferentes do mesmo fato caiam no mesmo card e a
            # geolocalização use o texto completo de cada matéria.
            _log("Lendo o corpo das fontes para correlação e geolocalização…", "SEARCH")
            raw = enriquecer_corpos(raw)
            grupos = agrupar_fatos(raw)
            _log(f"{len(grupos)} grupos de fatos identificados", "INFO")
            n_novas = 0
            for grupo_tuple in grupos:
                n = montar_noticia(grupo_tuple, cidade)
                chave = normalizar_texto(n["titulo"])
                with lock:
                    if estado["cidade"] != cidade:
                        _log(f"Cidade mudou, abortando ciclo", "WARN")
                        break
                    if chave in estado["historico"]:
                        continue
                    estado["historico"].add(chave)
                    estado["noticias"] = [n] + estado["noticias"]
                    estado["noticias"] = estado["noticias"][:200]
                    estado["total_visto"] += 1
                    estado["ultima_busca"] = datetime.now().strftime("%d/%m/%Y %H:%M:%S")
                prec = n.get("precisao","?")
                bairros_n = n.get("bairros", [])
                bairros_str = ", ".join(b["nome"] for b in bairros_n[:3]) if bairros_n else "—"
                fontes_str = ", ".join(n.get("fontes",[]))[:60]
                _log(f"[{prec}] bairros={bairros_str} | {n['titulo'][:60]}… | {fontes_str}", "OK")
                _publicar_sse("noticia", n)
                n_novas += 1
                link0 = n.get("links",[""])[0]
                # Enfileira refinamento com corpo para TODAS as notícias sem bairro no título
                if not bairros_n and link0:
                    with _geo_refine_lock:
                        _geo_refine_queue.append({
                            "id": n["id"], "url": link0, "cidade": cidade,
                            "precisao": prec, "titulo": n.get("titulo",""),
                            "geo_score": n.get("geo_score",0),
                        })
                else:
                    # já tem bairro: refina a POSIÇÃO (rua do fato → Nominatim) em background
                    _enfileirar_coord_precisa(n["id"], cidade, bairros_n, rua=n.get("rua"))
                if link0:
                    with _geo_refine_lock:
                        _media_queue.append(link0)
            with lock:
                estado["buscando"] = False
                estado["ultima_busca"] = datetime.now().strftime("%d/%m/%Y %H:%M:%S")
            _publicar_sse("buscando", {"buscando": False, "ultima_busca": estado["ultima_busca"], "total_visto": estado["total_visto"], "cidade": cidade})
            _log(f"Ciclo concluído: {n_novas} nova(s) / {len(estado['noticias'])} total", "OK")
            ultimo_ciclo = time.time()
        except Exception as exc:
            import traceback; traceback.print_exc()
            _log(f"Erro na busca: {exc}", "ERR")
            with lock:
                estado["buscando"] = False
            _publicar_sse("buscando", {"buscando": False})
            ultimo_ciclo = time.time()

def _worker_media_prefetch():
    while True:
        item_url = None
        with _geo_refine_lock:
            if _media_queue:
                item_url = _media_queue.pop(0)
        if not item_url:
            time.sleep(2)
            continue
        with _media_lock:
            if item_url in _media_cache:
                continue
        try:
            with app.test_request_context(f'/api/scrape?url={item_url}'):
                api_scrape()
                _log(f"Mídia pré-carregada: {item_url[:50]}…", "SCRAPE")
        except Exception:
            pass
        time.sleep(1)

# ─────────────────────────────────────────────
#  FLASK API (igual ao original, sem alterações)
# ─────────────────────────────────────────────
app = Flask(__name__)
CORS(app)

@app.route("/api/health")
def api_health():
    return jsonify({"ok": True})

@app.route("/api/noticias")
def api_noticias():
    with lock:
        return jsonify({
            "noticias": estado["noticias"], "ultima_busca": estado["ultima_busca"],
            "buscando": estado["buscando"], "total_visto": estado["total_visto"],
            "cidade": estado["cidade"],
        })

@app.route("/api/config", methods=["POST"])
def api_config():
    data = flask_req.json or {}
    mudou_cidade = False
    with lock:
        if "cidade" in data:
            nova = data["cidade"].strip()
            if nova and nova != estado["cidade"]:
                estado["cidade"] = nova
                estado["noticias"] = []
                estado["historico"] = set()
                mudou_cidade = True
        if "intervalo" in data:
            estado["intervalo"] = max(1, int(data["intervalo"]))
        if "horas_filtro" in data:
            estado["horas_filtro"] = max(1, int(data["horas_filtro"]))
        estado["busca_imediata"] = True
        estado["buscando"] = False
    if mudou_cidade:
        _publicar_sse("limpar", {"cidade": estado["cidade"]})
    return jsonify({"ok": True, "cidade": estado["cidade"]})

@app.route("/api/limpar", methods=["POST"])
def api_limpar():
    with lock:
        estado["noticias"] = []
        estado["historico"] = set()
        estado["busca_imediata"] = True
        estado["buscando"] = False
    _publicar_sse("limpar", {"cidade": estado["cidade"]})
    return jsonify({"ok": True})

@app.route("/api/stream")
def api_stream():
    import queue, json as _json
    q = queue.Queue(maxsize=200)
    with _sse_clients_lock:
        _sse_clients.append(q)
    with lock:
        snapshot = {
            "noticias": estado["noticias"], "ultima_busca": estado["ultima_busca"],
            "buscando": estado["buscando"], "total_visto": estado["total_visto"],
            "cidade": estado["cidade"],
        }
    with _log_lock:
        log_snap = list(_log_buffer)
    init_msg = f"event: snapshot\ndata: {_json.dumps(snapshot, ensure_ascii=False)}\n\n"
    log_msg = f"event: log_snapshot\ndata: {_json.dumps({'logs': log_snap}, ensure_ascii=False)}\n\n"
    def stream():
        yield init_msg
        yield log_msg
        while True:
            try:
                msg = q.get(timeout=20)
                yield msg
            except Exception:
                yield ": heartbeat\n\n"
    resp = app.response_class(stream(), mimetype="text/event-stream")
    resp.headers["Cache-Control"] = "no-cache"
    resp.headers["X-Accel-Buffering"] = "no"
    return resp

@app.route("/api/geocode")
def api_geocode():
    q = flask_req.args.get("q","").strip()
    cidade = flask_req.args.get("cidade", estado["cidade"]).strip()
    if not q:
        return jsonify({"error": "query obrigatória"}), 400
    bairros = buscar_bairros_direto(q, cidade)
    if bairros:
        return jsonify({
            "lat": bairros[0]["lat"], "lon": bairros[0]["lon"],
            "label": bairros[0]["nome"], "precisao": "bairro",
            "bairros": bairros,
        })
    # fallback: centro da cidade
    base = _coords_cidade(cidade)
    if base:
        return jsonify({"lat": base[0], "lon": base[1], "label": cidade.title(), "precisao": "cidade", "bairros": []})
    return jsonify({"error": "Localização não encontrada"})

@app.route("/api/cidade_zona")
def api_cidade_zona():
    """
    Retorna o contorno (polígono) da cidade para destacá-la inteira no mapa.
    Usado quando a notícia só tem referência à cidade (sem bairro): em vez de
    plotar um ponto, o front desenha a área da cidade ao clicar no card.
    Tenta o Nominatim (polygon_geojson); se falhar, devolve círculo de fallback.
    """
    cidade = flask_req.args.get("cidade", estado["cidade"]).strip()
    cidade_n = normalizar(cidade)

    # cache em memória
    cached = _zona_cache.get(cidade_n)
    if cached is not None:
        return jsonify(cached)

    base = _coords_cidade(cidade)
    clat, clon = base if base else (-20.67, -40.51)

    # estado (UF) para desambiguar a busca no Nominatim
    uf = ""
    cidade_key = _CIDADES_NORM.get(cidade_n)
    if cidade_key and cidade_key in GEO_CIDADES:
        uf = GEO_CIDADES[cidade_key].get("estado", "")

    resultado = None
    if _DEPS_OK:
        try:
            q = f"{cidade}, {uf}, Brasil" if uf else f"{cidade}, Brasil"
            r = _http.get(
                "https://nominatim.openstreetmap.org/search",
                params={"q": q, "format": "json", "polygon_geojson": 1,
                        "limit": 1, "countrycodes": "br"},
                timeout=10,
                headers={"User-Agent": "Arkadia/4.0 (monitor-noticias-mapa)"},
            )
            data = r.json()
            if data:
                item = data[0]
                geo = item.get("geojson")
                bbox = item.get("boundingbox")
                if geo and geo.get("type") in ("Polygon", "MultiPolygon"):
                    resultado = {"tipo": "poligono", "geojson": geo,
                                 "lat": clat, "lon": clon, "bbox": bbox}
        except Exception as exc:
            _log(f"Zona da cidade via Nominatim falhou: {exc}", "WARN")

    if resultado is None:
        # fallback: círculo de ~5 km no centro da cidade
        resultado = {"tipo": "circulo", "lat": clat, "lon": clon, "raio_m": 5000}

    _zona_cache[cidade_n] = resultado
    return jsonify(resultado)

@app.route("/api/logs")
def api_logs():
    with _log_lock:
        return jsonify({"logs": list(_log_buffer)})

@app.route("/api/geo_info")
def api_geo_info():
    cidade = flask_req.args.get("cidade","").strip()
    info = {"estados": len(GEO_ESTADOS), "cidades": len(GEO_CIDADES), "bairros": len(GEO_BAIRROS)}
    if cidade:
        cidade_n = normalizar(cidade)
        cidade_key = _CIDADES_NORM.get(cidade_n)
        info["bairros_cidade"] = len(GEO_BAIRROS_CIDADE.get(cidade_key, []))
        info["cidade_key"] = cidade_key
    return jsonify(info)

def _norm_img_key(src):
    """Chave p/ deduplicar imagens iguais servidas em tamanhos/URLs diferentes.
    Usa o NOME DO ARQUIVO sem tokens de tamanho/cópia — junta variantes da mesma foto."""
    if not src:
        return ""
    s = src.split("?")[0].split("#")[0].lower().rstrip("/")
    base = s.rsplit("/", 1)[-1]
    base = re.sub(r'\.(jpe?g|png|webp|gif|avif|bmp|jfif)$', '', base)
    base = re.sub(r'@\d+x$', '', base)                                # @2x
    base = re.sub(r'\(\d+\)$', '', base)                              # foto(1)
    base = re.sub(r'\d{2,4}x\d{2,4}', '', base)                       # 800x600
    base = re.sub(r'[-_](?:scaled|thumb|thumbnail|small|medium|large|mini|mobile|desktop|'
                  r'crop|resize|resized|resizing|fit|cover|fhd|hd|webp|opt|otimizad[ao]|'
                  r'compress(?:ed|ada)?|copy|copia)\b', '', base)
    base = re.sub(r'[-_](?:w|h|q|s|size|width|height)[-_]?\d{1,4}', '', base)   # w_800
    base = re.sub(r'[-_]\d{6,}$', '', base)                           # timestamp/id no final
    base = re.sub(r'[-_]\d{2,4}$', '', base)                          # foto-1024 ou cópia -1
    base = re.sub(r'[-_]+', ' ', base).strip()
    return base or s

def _img_score(src, w=0, h=0, forcar=False):
    """Estima a 'qualidade/tamanho' de uma imagem para priorizar a maior."""
    try:
        if w and h:
            return int(w) * int(h)
    except Exception:
        pass
    low = (src or "").lower()
    nums = re.findall(r'(\d{2,4})x(\d{2,4})', low)
    if nums:
        return max(int(a) * int(b) for a, b in nums)
    m = re.findall(r'[-_/](?:w|width|h|height|s|size)[-_]?(\d{2,4})', low)
    if m:
        d = max(int(x) for x in m); return d * d
    m2 = re.findall(r'[-_](\d{3,4})(?=\.(?:jpe?g|png|webp|avif))', low)
    if m2:
        d = max(int(x) for x in m2); return d * d
    return 480000 if forcar else 90000   # meta sem tamanho ≈ imagem grande de destaque

def _dedup_imagens_por_conteudo(imgs, budget_seg=6, max_imgs=20):
    """Remove duplicatas REAIS comparando os bytes do início de cada imagem.
    A deduplicação por nome de arquivo (_norm_img_key) não pega tudo: a mesma
    foto às vezes é servida em URLs com nomes completamente diferentes (CDN,
    cache-busting, formatos alternativos). Aqui baixamos só os primeiros KB de
    cada imagem (suficiente p/ um hash estável) e agrupamos por hash, mantendo
    a versão de maior score de cada grupo. Best-effort: se o download falhar
    ou demorar, a imagem é mantida como estava (nunca perdemos uma imagem por
    causa de um erro de rede)."""
    if not _DEPS_OK or len(imgs) <= 1:
        return imgs
    UA = {"User-Agent": "Mozilla/5.0 (Arkadia/4.0; dedup-midia)"}

    def _hash_de(im):
        try:
            r = _http.get(im["src"], timeout=5, stream=True, headers=UA)
            dados = bytearray()
            for chunk in r.iter_content(8192):
                dados.extend(chunk)
                if len(dados) >= 65536:
                    break
            r.close()
            if not dados:
                return im, None
            return im, hashlib.md5(bytes(dados)).hexdigest()
        except Exception:
            return im, None

    from concurrent.futures import ThreadPoolExecutor as _TPE, as_completed as _ac
    alvo = imgs[:max_imgs]
    resto = imgs[max_imgs:]
    ordem = []          # ordem original (por hash, ou marcador único se falhou)
    melhor_por_hash = {}
    t0 = time.time()
    try:
        with _TPE(max_workers=6) as ex:
            futs = {ex.submit(_hash_de, im): im for im in alvo}
            for fut in _ac(futs, timeout=budget_seg):
                im, h = fut.result()
                chave = h if h else f"__semhash__{id(im)}"
                ordem.append((chave, im))
                atual = melhor_por_hash.get(chave)
                if atual is None or im["score"] > atual["score"]:
                    melhor_por_hash[chave] = im
                if time.time() - t0 > budget_seg:
                    break
    except Exception:
        return imgs   # qualquer falha geral: devolve a lista original, sem risco

    if not melhor_por_hash:
        return imgs

    vistos = set(); resultado = []
    for chave, im in ordem:
        if chave in vistos:
            continue
        vistos.add(chave)
        resultado.append(melhor_por_hash[chave])
    return resultado + resto

@app.route("/api/scrape")
def api_scrape():
    import urllib.parse as _up
    url = flask_req.args.get("url","").strip().split('?')[0]
    urls_extra = flask_req.args.get("urls","").strip()
    # chave de cache inclui TODAS as fontes — evita devolver resultado de 1 só fonte
    cache_key = url + ("|" + urls_extra if urls_extra else "")
    with _media_lock:
        if cache_key in _media_cache:
            return jsonify(_media_cache[cache_key])
    if not _DEPS_OK:
        return jsonify({"error":"requests/bs4 não instalados","images":[],"videos":[],"fontes":[]})
    todas_urls = [url]
    if urls_extra:
        todas_urls += [u.strip() for u in urls_extra.split(",") if u.strip()]
    _LOGO_DOMAINS = {
        "news.google.com","gstatic.com","google.com","googleapis.com",
        "googleusercontent.com","gravatar.com","feedburner.com",
        "wp.com/i/","s.w.org","wordpress.com/i/","disqus.com",
        "facebook.com/tr","twitter.com/i/","addthis.com",
    }
    def _is_logo_url(src):
        sl = src.lower()
        if any(d in sl for d in _LOGO_DOMAINS): return True
        if re.search(r'(?:logo|icon|favicon|avatar|sprite|placeholder|noimage|default|loading|blank|spacer|pixel|badge|button)\b', sl): return True
        if sl.startswith("data:"): return True
        return False
    def _resolver_url_googlenews(u):
        if "news.google.com" not in u: return u
        real = _gn_decode_url(u)
        if real and "news.google.com" not in real:
            return real
        # fallback: tenta redirect simples
        try:
            r2 = _http.get(u, timeout=8, headers={"User-Agent":"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36","Accept-Language":"pt-BR,pt;q=0.9"}, allow_redirects=True)
            if "news.google.com" not in r2.url: return r2.url
        except Exception:
            pass
        return u
    def _normalizar_src(src, base_url):
        if not src: return ""
        src = src.strip()
        if src.startswith("//"): src = "https:" + src
        elif src.startswith("/") and not src.startswith("//"):
            parsed = _up.urlparse(base_url)
            src = f"{parsed.scheme}://{parsed.netloc}{src}"
        return src
    def _melhor_src_de_srcset(srcset_str, base_url):
        melhor_src, melhor_w = "", 0
        for parte in srcset_str.split(","):
            parte = parte.strip()
            if not parte: continue
            tokens = parte.split()
            src_raw = tokens[0]; w = 0
            if len(tokens) > 1:
                try: w = int(tokens[1].lower().replace("w","").replace("x",""))
                except: w = 0
            if w > melhor_w: melhor_w = w; melhor_src = src_raw
        return _normalizar_src(melhor_src, base_url) if melhor_src else ""
    def scrape_one(u):
        try:
            session = _http.Session()
            u_real = _resolver_url_googlenews(u)
            if "url=" in u_real:
                u_real = _up.unquote(u_real.split("url=")[-1].split("&")[0])
            r = session.get(u_real, timeout=12, headers={"User-Agent":"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/125.0.0.0 Safari/537.36","Accept-Language":"pt-BR,pt;q=0.9","Accept":"text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8","Referer":"https://www.google.com/"}, allow_redirects=True)
            soup = _bs4.BeautifulSoup(r.text, "html.parser")
            base_url = r.url

            # nome de exibição da fonte (jornal)
            og_site = soup.find("meta",property="og:site_name")
            site_name = og_site["content"].strip() if og_site and og_site.get("content") else _up.urlparse(base_url).netloc.replace("www.","")

            # ── 1) Remove blocos que NÃO fazem parte da matéria (Veja Também,
            #      relacionados, mais lidas, recomendados, sidebar, anúncios…).
            #      É isso que evita indexar fotos de notícias sugeridas. ──
            LIXO_SEL = [
                "aside","nav","footer","header","form",
                "[class*='relacionad']","[class*='related']","[class*='veja']","[class*='leia']",
                "[class*='mais-lid']","[class*='maislid']","[class*='mais_lid']","[class*='recomend']",
                "[class*='suggest']","[class*='sugest']","[class*='popular']","[class*='newsletter']",
                "[class*='banner']","[class*='publicidade']","[class*='propaganda']","[class*='ads']",
                "[class*='ad-']","[class*='-ad']","[class*='sidebar']","[class*='widget']",
                "[class*='outbrain']","[class*='taboola']","[class*='assine']","[class*='paywall']",
                "[class*='compartilh']","[class*='share']","[class*='social']","[class*='comment']",
                "[class*='coment']","[class*='galeria-relacion']","[class*='card']","[class*='trending']",
                "[id*='relacionad']","[id*='related']","[id*='veja']","[id*='sidebar']",
                "[id*='newsletter']","[id*='mais-lid']","[id*='recomend']","[id*='ads']",
            ]
            for sel in LIXO_SEL:
                try:
                    for tag in soup.select(sel):
                        tag.decompose()
                except Exception:
                    pass

            videos = []   # videos: [{type,url,poster,fonte}]
            img_by_key = {}   # key → {src,fonte,score} (mantém a MAIOR versão)
            _vistas_vid = set()
            def _add_img(src, forcar=False, w=0, h=0):
                src = _normalizar_src(src, base_url)
                if not src or not src.startswith("http"):
                    return False
                if _is_logo_url(src):
                    return False
                if not forcar:
                    exts = ('.jpg','.jpeg','.png','.webp','.gif','.bmp','.jfif','.avif')
                    if not any(src.lower().split('?')[0].endswith(ext) for ext in exts):
                        return False
                k = _norm_img_key(src)
                sc = _img_score(src, w, h, forcar)
                ja = img_by_key.get(k)
                # mantém apenas a variante de maior qualidade/tamanho desta imagem
                if (ja is None) or (sc > ja["score"]):
                    img_by_key[k] = {"src": src, "fonte": site_name, "score": sc}
                return True
            def _add_video(vtype, vurl, poster=""):
                if not vurl: return
                vurl = _normalizar_src(vurl, base_url)
                if not vurl or vurl in _vistas_vid: return
                _vistas_vid.add(vurl)
                videos.append({"type":vtype,"url":vurl,
                               "poster":_normalizar_src(poster, base_url) if poster else "",
                               "fonte":site_name})

            # ── 2) Imagem-destaque da matéria (sempre relacionada ao fato) ──
            for attr, val in [("property","og:image"),("property","og:image:url"),
                              ("property","og:image:secure_url"),("name","twitter:image"),
                              ("name","twitter:image:src"),("itemprop","image")]:
                for tag in soup.find_all("meta",{attr:val}):
                    _add_img(tag.get("content","") or tag.get("src",""), forcar=True)
            import json as _json2
            for script in soup.find_all("script",type="application/ld+json"):
                try:
                    ld = _json2.loads(script.string or "")
                    items = ld if isinstance(ld,list) else [ld]
                    for item in items:
                        if not isinstance(item, dict): continue
                        img = item.get("image")
                        if isinstance(img,str): _add_img(img, forcar=True)
                        elif isinstance(img,dict): _add_img(img.get("url",""), forcar=True)
                        elif isinstance(img,list):
                            for i in img: _add_img(i if isinstance(i,str) else (i.get("url","") if isinstance(i,dict) else ""), forcar=True)
                        # vídeo dentro do ld+json
                        vid = item.get("video")
                        vids = vid if isinstance(vid,list) else ([vid] if vid else [])
                        for vv in vids:
                            if isinstance(vv,dict):
                                _add_video("file", vv.get("contentUrl","") or vv.get("embedUrl",""), vv.get("thumbnailUrl",""))
                except: pass

            # ── 3) Raiz do CORPO da matéria: só pegamos imagens DENTRO dela ──
            ROOT_SEL = ["article",".article-body","[itemprop='articleBody']",".materia",
                        ".post-content",".entry-content",".conteudo-materia",".texto-materia",
                        ".content-text",".noticia-conteudo","main"]
            root = None
            for sel in ROOT_SEL:
                el = soup.select_one(sel)
                if el:
                    root = el; break
            if root is None:
                root = soup.body or soup

            for img_tag in root.select("img, figure img, picture img, picture source")[:40]:
                src_candidates = [
                    img_tag.get("srcset",""),img_tag.get("data-srcset",""),
                    img_tag.get("src",""),img_tag.get("data-src",""),
                    img_tag.get("data-lazy-src",""),img_tag.get("data-original",""),
                    img_tag.get("data-lazy",""),img_tag.get("data-hi-res-src",""),
                    img_tag.get("data-full-src",""),img_tag.get("data-image",""),
                ]
                src = ""
                for cand in src_candidates:
                    if not cand: continue
                    if "," in cand and " " in cand: src = _melhor_src_de_srcset(cand, base_url)
                    else: src = _normalizar_src(cand, base_url)
                    if src: break
                if not src or not src.startswith("http"): continue
                w = img_tag.get("width",""); h = img_tag.get("height","")
                try:
                    if int(w) < 200 or int(h) < 120: continue   # descarta thumbs pequenas
                except: pass
                wn = re.sub(r'\D','',str(w)); hn = re.sub(r'\D','',str(h))
                _add_img(src, w=int(wn) if wn else 0, h=int(hn) if hn else 0)
                if len(img_by_key) >= 16: break

            # ── 4) Vídeos (somente dentro do corpo + meta da página) ──
            for iframe in root.find_all("iframe", src=True):
                src = iframe["src"]
                if "youtube" in src or "youtu.be" in src: _add_video("youtube", src)
                elif "vimeo.com" in src: _add_video("vimeo", src)
                elif "dailymotion" in src: _add_video("dailymotion", src)
            for vtag in root.find_all("video"):
                poster = vtag.get("poster","")
                vsrc = vtag.get("src","")
                if vsrc: _add_video("file", vsrc, poster)
                for s in vtag.find_all("source", src=True):
                    _add_video("file", s["src"], poster)
            for prop in ["og:video","og:video:url","og:video:secure_url"]:
                ogv = soup.find("meta", property=prop)
                if ogv and ogv.get("content"):
                    low = ogv["content"].lower()
                    vtype = "youtube" if ("youtube" in low or "youtu.be" in low) else ("vimeo" if "vimeo" in low else "file")
                    _add_video(vtype, ogv["content"])

            desc = ""
            for attr, val in [("property","og:description"),("name","description"),("name","twitter:description")]:
                tag = soup.find("meta",{attr:val})
                if tag and tag.get("content"): desc = tag["content"]; break
            og_title = soup.find("meta",property="og:title")
            title = (og_title["content"] if og_title else (soup.title.string if soup.title else ""))
            # maior/melhor qualidade primeiro
            images = sorted(img_by_key.values(), key=lambda x: -x["score"])
            return {"url":u,"site_name":site_name,"images":images[:12],"videos":videos[:4],
                    "title":(title or "").strip(),"description":(desc or "").strip(),"ok":True}
        except Exception:
            return {"url":u,"site_name":"","images":[],"videos":[],"title":"","description":"","ok":False}
    from concurrent.futures import ThreadPoolExecutor, as_completed
    resultados = []
    with ThreadPoolExecutor(max_workers=4) as ex:
        futuros = {ex.submit(scrape_one, u): u for u in todas_urls}
        for fut in as_completed(futuros, timeout=15):
            try: resultados.append(fut.result())
            except: pass
    resultados.sort(key=lambda x: 0 if x["url"] == url else 1)
    all_videos, desc_global, title_global = [], "", ""
    _seen_vid = set()
    img_best = {}   # (host|key) → {src,fonte,score}
    from urllib.parse import urlparse as _urlp
    for r in resultados:
        if not desc_global and r.get("description"): desc_global = r["description"]
        if not title_global and r.get("title"): title_global = r["title"]
        for img in r.get("images",[]):
            s = img.get("src") if isinstance(img,dict) else img
            if not s: continue
            sc = img.get("score") if isinstance(img,dict) else _img_score(s)
            fonte = img.get("fonte") if isinstance(img,dict) else r.get("site_name","")
            # chave inclui o HOST: imagens de fontes diferentes são preservadas;
            # variantes da mesma imagem (mesmo host) são deduplicadas pela maior.
            try: host = _urlp(s).netloc.replace("www.","")
            except Exception: host = ""
            k = host + "|" + _norm_img_key(s)
            ja = img_best.get(k)
            if (ja is None) or (sc > ja["score"]):
                img_best[k] = {"src": s, "fonte": fonte, "score": sc}
        for v in r.get("videos",[]):
            vu = v.get("url") if isinstance(v,dict) else None
            if vu and vu not in _seen_vid:
                _seen_vid.add(vu); all_videos.append(v)
    all_images = sorted(img_best.values(), key=lambda x: -x["score"])
    all_images = _dedup_imagens_por_conteudo(all_images)
    result = {"images":all_images[:16],"videos":all_videos[:6],
              "title":title_global,"description":desc_global,"fontes":resultados}
    with _media_lock:
        _media_cache[cache_key] = result
    return jsonify(result)

@app.route("/")
def index():
    return HTML_PAGE

# ─────────────────────────────────────────────
#  FRONTEND (mesmo HTML da versão anterior)
# ─────────────────────────────────────────────
HTML_PAGE = r"""<!DOCTYPE html>
<html lang="pt-BR">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Arkadia v4 – Notícias ao Vivo</title>
<link rel="stylesheet" href="https://unpkg.com/leaflet@1.9.4/dist/leaflet.css"/>
<script src="https://unpkg.com/leaflet@1.9.4/dist/leaflet.js"></script>
<style>
* { box-sizing: border-box; margin: 0; padding: 0; }
body {
  font-family: system-ui, -apple-system, sans-serif;
  background: #0f1117; color: #e2e8f0;
  height: 100vh; display: flex; flex-direction: column; overflow: hidden;
}
#wrapper { display: flex; flex-direction: column; flex: 1; overflow: hidden; }
#header {
  display: flex; align-items: center; gap: 12px; padding: 10px 16px;
  background: #1a1d27; border-bottom: 1px solid #2d3148; flex-shrink: 0;
}
#header h1 { font-size: 14px; font-weight: 700; color: #fff; white-space: nowrap; }
.dot { width: 8px; height: 8px; border-radius: 50%; background: #22c55e; animation: blink 2s infinite; flex-shrink: 0; }
@keyframes blink { 0%,100%{opacity:1} 50%{opacity:.3} }
.dot.loading { background: #f59e0b; }
.dot.off { background: #ef4444; animation: none; }
#header input, #header select {
  background: #252836; border: 1px solid #3d4266; color: #e2e8f0;
  border-radius: 6px; padding: 5px 10px; font-size: 13px;
}
#header input:focus, #header select:focus { outline: none; border-color: #6366f1; }
#cidade-input { width: 155px; }
#header label { font-size: 12px; color: #94a3b8; white-space: nowrap; }
button {
  background: #6366f1; color: #fff; border: none; border-radius: 6px;
  padding: 6px 14px; font-size: 13px; cursor: pointer; font-weight: 500;
  transition: background .15s;
}
button:hover { background: #4f46e5; }
button.danger { background: #ef4444; }
button.danger:hover { background: #dc2626; }
button:disabled { opacity: .5; cursor: not-allowed; }
#status-text { font-size: 12px; color: #94a3b8; white-space: nowrap; }
#geo-refinando {
  font-size: 11px; color: #f59e0b; white-space: nowrap;
  display: none; align-items: center; gap: 4px;
}
#geo-refinando.ativo { display: flex; }
#geo-refinando::before { content: ''; display: inline-block; width: 6px; height: 6px;
  border-radius: 50%; background: #f59e0b; animation: blink 1s infinite; }
.spacer { flex: 1; }
#count-badge {
  background: #6366f1; color: #fff; border-radius: 20px;
  padding: 2px 10px; font-size: 12px; font-weight: 600; white-space: nowrap;
}
#main { display: flex; flex: 1; overflow: hidden; }
#map-wrapper { flex: 1; position: relative; overflow: hidden; }
#map { width: 100%; height: 100%; }

/* Botão "ver todos" + legenda no mapa */
#map-controls { position: absolute; top: 10px; right: 10px; z-index: 500; display: flex; gap: 6px; }
#btn-fit {
  background: #1a1d27; color: #c7d2fe; border: 1px solid #3d4266; border-radius: 7px;
  padding: 6px 10px; font-size: 11.5px; font-weight: 600; cursor: pointer; box-shadow: 0 2px 8px rgba(0,0,0,.4);
}
#btn-fit:hover { background: #252a3a; border-color: #6366f1; }
#map-legend {
  position: absolute; bottom: 14px; left: 10px; z-index: 500;
  background: rgba(20,23,31,.92); border: 1px solid #2d3148; border-radius: 8px;
  padding: 7px 10px; font-size: 11px; color: #cbd5e1; box-shadow: 0 2px 10px rgba(0,0,0,.4); min-width: 120px;
}
.leg-title { font-weight: 700; color: #94a3b8; font-size: 10px; text-transform: uppercase; letter-spacing: .4px; display: flex; justify-content: space-between; cursor: default; }
#leg-toggle { cursor: pointer; user-select: none; }
#leg-body { display: flex; flex-direction: column; gap: 4px; margin-top: 6px; }
#map-legend.collapsed #leg-body { display: none; }
.leg-row { display: flex; align-items: center; gap: 7px; }
.leg-dot { width: 11px; height: 11px; border-radius: 50%; border: 2px solid #fff; flex-shrink: 0; }
.leg-dot.leg-area { background: transparent; border: 2px dashed #6366f1; }

/* Marcador com pulsar (múltiplas fontes + rua) */
.pin-wrap { position: relative; display: flex; align-items: center; justify-content: center; overflow: visible; }
.pin-dot { border-radius: 50%; border: 2px solid #fff; position: relative; z-index: 2; }
.pin-pulse {
  position: absolute; left: 50%; top: 50%; width: 16px; height: 16px; margin: -8px 0 0 -8px;
  border-radius: 50%; background: #ef4444; z-index: 1; animation: pinpulse 1.4s ease-out infinite;
}
@keyframes pinpulse {
  0%   { transform: scale(.7); opacity: .75; }
  70%  { transform: scale(2.6); opacity: 0; }
  100% { transform: scale(2.6); opacity: 0; }
}

/* Ferramentas da sidebar (busca/ordenar/filtro) */
#sidebar-tools { display: flex; gap: 5px; padding: 7px 10px; border-bottom: 1px solid #2d3148; align-items: center; }
#lista-busca {
  flex: 1; min-width: 0; background: #0f1117; border: 1px solid #2d3148; border-radius: 6px;
  color: #e2e8f0; font-size: 11.5px; padding: 5px 8px; outline: none;
}
#lista-busca:focus { border-color: #6366f1; }
#lista-sort {
  background: #0f1117; border: 1px solid #2d3148; border-radius: 6px; color: #cbd5e1;
  font-size: 11px; padding: 5px 4px; cursor: pointer; outline: none;
}
.tool-toggle {
  background: #0f1117; border: 1px solid #2d3148; border-radius: 6px; color: #94a3b8;
  font-size: 10.5px; padding: 5px 7px; cursor: pointer; white-space: nowrap;
}
.tool-toggle.ativo { background: #064e3b; border-color: #10b981; color: #6ee7b7; }
#sidebar-resumo { font-size: 10.5px; color: #64748b; padding: 5px 12px; border-bottom: 1px solid #1e2334; display: none; }
#sidebar-resumo.show { display: block; }
#proxima-busca { font-size: 11px; color: #64748b; white-space: nowrap; }
.card-stats { float: right; cursor: pointer; opacity: .55; font-size: 12px; }
.card-stats:hover { opacity: 1; }

#sidebar {
  width: 315px; flex-shrink: 0; background: #1a1d27;
  border-left: 1px solid #2d3148; display: flex; flex-direction: column; overflow: hidden;
}
#sidebar-header {
  padding: 10px 14px; border-bottom: 1px solid #2d3148;
  font-size: 12px; color: #94a3b8; display: flex; justify-content: space-between; align-items: center;
}
#news-list { flex: 1; overflow-y: auto; }
#news-list::-webkit-scrollbar { width: 4px; }
#news-list::-webkit-scrollbar-track { background: #1a1d27; }
#news-list::-webkit-scrollbar-thumb { background: #3d4266; border-radius: 2px; }
.card {
  padding: 11px 14px; border-bottom: 1px solid #2d3148;
  cursor: pointer; transition: background .1s;
}
.card:hover { background: #252836; }
.card-new { animation: cardSlideIn .5s ease; border-left: 3px solid #22c55e !important; }
@keyframes cardSlideIn {
  from { opacity: 0; transform: translateY(-8px); background: #0f2e1a; }
  to   { opacity: 1; transform: translateY(0); background: transparent; }
}
.card.active { background: #1e2044; border-left: 3px solid #6366f1; }
.card-city {
  font-size: 10px; font-weight: 600; text-transform: uppercase; letter-spacing: .5px;
  color: #818cf8; margin-bottom: 3px; display: flex; align-items: center; gap: 5px; flex-wrap: wrap;
}
.badge-multi { background: #ef4444; color: #fff; border-radius: 10px; padding: 1px 6px; font-size: 9px; font-weight: 700; }
.precisao-badge { font-size: 9px; padding: 1px 6px; border-radius: 8px; font-weight: 700; white-space: nowrap; }
.bairros-encontrados { display: flex; flex-wrap: wrap; gap: 4px; margin: 4px 0 2px 0; }
.bairro-tag { font-size: 10px; background: #1a3a2a; color: #6ee7b7; border: 1px solid #065f46; border-radius: 10px; padding: 1px 8px; white-space: nowrap; font-weight: 600; }
.bairro-tag.bt-fato { background: #14532d; color: #bbf7d0; border-color: #16a34a; box-shadow: 0 0 0 1px #16a34a55; }
.bairro-tag.bt-cit { background: #3a2a14; color: #fcd9a8; border-color: #b45309; }
.preview-cap { font-size: 10px; color: #818cf8; font-weight: 600; margin-bottom: 5px; }
.bairros-sem { font-size: 10px; color: #64748b; margin: 3px 0; font-style: italic; }.precisao-rua    { background: #064e3b; color: #6ee7b7; }
.precisao-bairro { background: #1e3a5f; color: #93c5fd; }
.precisao-cidade { background: #1e3a5f; color: #93c5fd; }
.precisao-estado { background: #3b2f00; color: #fcd34d; }
.precisao-manual { background: #4c1d3f; color: #f9a8d4; }
.precisao-local  { background: #2d3748; color: #a0aec0; }
.badge-confianca { font-size: 9px; padding: 1px 7px; border-radius: 10px; font-weight: 700; white-space: nowrap; }
.conf-alta  { background: #064e3b; color: #6ee7b7; }
.conf-media { background: #1e3a5f; color: #93c5fd; }
.conf-baixa { background: #2d3748; color: #a0aec0; }
.razoes-corr { margin-top: 4px; font-size: 10px; color: #64748b; line-height: 1.5; border-left: 2px solid #3d4266; padding-left: 6px; }
.badge-geo-score { font-size: 9px; padding: 1px 7px; border-radius: 10px; font-weight: 700; white-space: nowrap; }
.geo-score-alta  { background: #064e3b; color: #6ee7b7; }
.geo-score-media { background: #1e3a5f; color: #93c5fd; }
.geo-score-baixa { background: #3b2f00; color: #fcd34d; }
.evidencias-geo { font-size: 10px; color: #4a5568; margin-top: 2px; padding-left: 6px; border-left: 2px solid #2d3148; line-height: 1.4; }
.card-title { font-size: 12px; color: #e2e8f0; line-height: 1.45; margin-bottom: 5px; }
.card-meta  { font-size: 11px; color: #64748b; }
.card-sources { display: flex; gap: 4px; flex-wrap: wrap; margin-top: 4px; }
.src-tag { font-size: 10px; padding: 1px 7px; border-radius: 10px; background: #252836; border: 1px solid #3d4266; color: #94a3b8; }
.card-links { display: flex; gap: 6px; margin-top: 6px; flex-wrap: wrap; }
.card-links a { font-size: 10px; color: #818cf8; text-decoration: none; border: 1px solid #3d4266; border-radius: 4px; padding: 1px 6px; }
.card-links a:hover { color: #a5b4fc; border-color: #6366f1; }
.card-actions { display: flex; gap: 5px; margin-top: 7px; flex-wrap: wrap; align-items: center; }
.btn-action {
  font-size: 10px; padding: 2px 8px; border-radius: 4px; cursor: pointer;
  border: 1px solid #3d4266; background: #252836; color: #94a3b8;
  font-weight: 500; transition: all .15s; white-space: nowrap; line-height: 1.6;
}
.btn-action:hover  { border-color: #6366f1; color: #a5b4fc; background: #1e2044; }
.btn-action.active { border-color: #6366f1; color: #818cf8; background: #1e2044; }
.preview-panel { display: none; margin-top: 8px; border-top: 1px solid #2d3148; padding-top: 8px; }
.preview-loading, .preview-empty { color: #64748b; font-size: 11px; font-style: italic; padding: 2px 0; }
.preview-desc { font-size: 11px; color: #94a3b8; line-height: 1.5; margin-bottom: 7px; max-height: 52px; overflow: hidden; }
.preview-images { display: flex; gap: 4px; flex-wrap: wrap; margin-bottom: 6px; }
.preview-images img { width: 84px; height: 56px; object-fit: cover; border-radius: 4px; cursor: pointer; border: 1px solid #3d4266; transition: border-color .15s, transform .1s; background: #252836; }
.preview-images img:hover { border-color: #6366f1; transform: scale(1.05); }
.preview-videos iframe { width: 100%; height: 128px; border-radius: 4px; border: 1px solid #3d4266; margin-bottom: 4px; display: block; }
#empty-state { padding: 40px 20px; text-align: center; color: #475569; font-size: 13px; }
#empty-state p { margin-top: 8px; font-size: 12px; }
.leaflet-popup-content-wrapper { background: #1a1d27; color: #e2e8f0; border: 1px solid #3d4266; border-radius: 8px; min-width: 240px; }
.leaflet-popup-tip { background: #1a1d27; }
.leaflet-popup-content { margin: 10px 14px; font-size: 12px; line-height: 1.5; }
.leaflet-popup-content strong { color: #818cf8; display: block; margin-bottom: 6px; }
.popup-fonte { color: #64748b; font-size: 11px; }
.popup-link  { color: #818cf8; font-size: 11px; }
.popup-titulo { color: #e2e8f0; font-weight: 600; font-size: 12.5px; line-height: 1.45; margin-bottom: 6px; }
.popup-foco { font-size: 11px; margin-bottom: 6px; padding: 3px 7px; border-radius: 5px; }
.popup-foco.foco-princ { background: #14532d; color: #bbf7d0; border: 1px solid #16a34a; }
.popup-foco.foco-cit { background: #3a2a14; color: #fcd9a8; border: 1px solid #b45309; }
.popup-resumo { font-size: 11.5px; color: #cbd5e1; line-height: 1.5; margin-bottom: 7px; padding-left: 8px; border-left: 2px solid #4f46e5; }
.popup-bairros { display: flex; flex-wrap: wrap; gap: 4px; margin-bottom: 6px; }
.popup-precisao { font-size: 11px; color: #6ee7b7; margin-bottom: 6px; }
.popup-data { font-size: 11px; color: #94a3b8; margin-bottom: 7px; }
.popup-data b { color: #cbd5e1; }
.popup-fontes-links { margin-top: 6px; display: flex; flex-wrap: wrap; gap: 6px; }
.popup-botoes { display: flex; gap: 5px; margin-bottom: 4px; }
.popup-midia-btn, .popup-stats-btn {
  flex: 1; background: #4f46e5; color: #fff; border: none; border-radius: 6px;
  padding: 6px 8px; font-size: 11.5px; font-weight: 600; cursor: pointer;
}
.popup-midia-btn:hover { background: #6366f1; }
.popup-stats-btn { background: #334155; }
.popup-stats-btn:hover { background: #475569; }

/* Modal de estatísticas */
#stats-overlay {
  position: fixed; inset: 0; background: rgba(2,6,23,.78); backdrop-filter: blur(3px);
  display: none; align-items: center; justify-content: center; z-index: 4100;
}
.stats-box {
  width: min(540px, 94vw); max-height: 86vh; background: #14171f; border: 1px solid #2d3148;
  border-radius: 12px; display: flex; flex-direction: column; overflow: hidden; box-shadow: 0 20px 60px rgba(0,0,0,.5);
}
.stats-sub { padding: 0 16px 10px; font-size: 12px; color: #94a3b8; border-bottom: 1px solid #2d3148; line-height: 1.4; }
.stats-body { padding: 14px 16px; overflow-y: auto; display: flex; flex-direction: column; gap: 10px; }
.st-sec { background: #0f1320; border: 1px solid #232a3d; border-radius: 9px; padding: 11px 13px; display: flex; flex-direction: column; gap: 7px; }
.st-sec-title { font-size: 12px; font-weight: 700; color: #c7d2fe; }
.st-local { font-size: 15px; color: #e2e8f0; display: flex; align-items: center; gap: 8px; flex-wrap: wrap; }
.st-prec { font-size: 10px; font-weight: 700; padding: 2px 8px; border-radius: 10px; }
.st-prec.pp-rua { background: #3a2a14; color: #fcd9a8; border: 1px solid #b45309; }
.st-prec.pp-bairro { background: #14532d; color: #bbf7d0; border: 1px solid #16a34a; }
.st-prec.pp-cidade { background: #1e3a5f; color: #93c5fd; border: 1px solid #2563eb; }
.st-quote-label { font-size: 10.5px; color: #94a3b8; }
.st-quote-label.dim { color: #64748b; font-style: italic; }
.st-quote {
  font-size: 12px; color: #e2e8f0; line-height: 1.55;
  background: #181c2a; border-left: 3px solid #6366f1; padding: 8px 11px; border-radius: 4px;
}
.st-src { color: #64748b; font-size: 11px; margin-top: 4px; }
.st-conf-frase { font-size: 13px; color: #e2e8f0; }
.st-meter { height: 8px; background: #232a3d; border-radius: 5px; overflow: hidden; }
.st-meter-fill { height: 100%; border-radius: 5px; }
.st-meter-fill.m-alta { background: #10b981; }
.st-meter-fill.m-media { background: #3b82f6; }
.st-meter-fill.m-baixa { background: #f59e0b; }
.st-list { margin: 2px 0 0; padding-left: 18px; color: #cbd5e1; font-size: 12px; line-height: 1.7; }
.st-srclist { display: flex; flex-wrap: wrap; gap: 6px; }
.st-srctag { font-size: 11px; background: #252836; border: 1px solid #3d4266; color: #c7d2fe; padding: 3px 10px; border-radius: 10px; text-decoration: none; }
.st-srctag:hover { border-color: #6366f1; }
.st-note { font-size: 10.5px; color: #64748b; border-top: 1px solid #2d3148; padding-top: 9px; line-height: 1.5; }

/* Overlay da galeria de mídia */
#midia-overlay {
  position: fixed; inset: 0; background: rgba(2,6,23,.78); backdrop-filter: blur(3px);
  display: none; align-items: center; justify-content: center; z-index: 4000;
}
.midia-box {
  width: min(760px, 94vw); max-height: 88vh; background: #14171f; border: 1px solid #2d3148;
  border-radius: 12px; display: flex; flex-direction: column; overflow: hidden; box-shadow: 0 20px 60px rgba(0,0,0,.5);
}
.midia-head { padding: 12px 44px 12px 16px; font-size: 13px; font-weight: 600; color: #c7d2fe; border-bottom: 1px solid #2d3148; }
.midia-close, .lb-close {
  position: absolute; background: #1e2330; color: #e2e8f0; border: 1px solid #3d4266;
  width: 32px; height: 32px; border-radius: 50%; cursor: pointer; z-index: 5;
  display: flex; align-items: center; justify-content: center; padding: 0;
}
.midia-close svg, .lb-close svg { display: block; width: 14px; height: 14px; }
.midia-close { top: 10px; right: 12px; }
.midia-body { padding: 14px 16px; overflow-y: auto; }
.midia-grid { display: grid; grid-template-columns: repeat(auto-fill, minmax(120px,1fr)); gap: 8px; margin: 4px 0 12px; }
.midia-item {
  position: relative; aspect-ratio: 3/2; border-radius: 7px; overflow: hidden; cursor: pointer;
  border: 1px solid #2d3148; background: #0b0d13; transition: transform .12s, border-color .12s;
}
.midia-item:hover { transform: scale(1.03); border-color: #6366f1; }
.midia-item img { width: 100%; height: 100%; object-fit: cover; display: block; }
.midia-item.vid { display: flex; align-items: center; justify-content: center; background: #11151f; }
.midia-play { position: absolute; font-size: 26px; color: #fff; text-shadow: 0 2px 8px #000; }
.midia-fonte {
  position: absolute; left: 0; right: 0; bottom: 0; font-size: 9.5px; color: #e2e8f0;
  background: linear-gradient(transparent, rgba(0,0,0,.8)); padding: 10px 6px 3px; text-align: left;
}
.preview-cap { font-size: 11px; color: #818cf8; font-weight: 600; margin: 4px 0; }
.preview-desc { font-size: 11.5px; color: #94a3b8; line-height: 1.5; margin-bottom: 8px; }
.preview-loading, .preview-empty { font-size: 12px; color: #64748b; padding: 16px 4px; text-align: center; }

/* Lightbox (imagem em tamanho real / vídeo) */
#midia-lightbox {
  position: fixed; inset: 0; background: rgba(0,0,0,.92); display: none;
  align-items: center; justify-content: center; z-index: 4200;
}
#midia-lightbox .lb-close { top: 16px; right: 18px; display: flex; align-items: center; justify-content: center; }
.lb-inner { display: flex; flex-direction: column; align-items: center; gap: 10px; max-width: 96vw; max-height: 94vh; }
.lb-img {
  max-width: 96vw; max-height: 88vh; object-fit: contain; border-radius: 6px;
  cursor: zoom-in; transition: transform .2s ease; transform-origin: center center;
  user-select: none; touch-action: none;
}
.lb-img.zoomed { cursor: zoom-out; }
.lb-video { width: min(960px, 92vw); aspect-ratio: 16/9; max-height: 86vh; border-radius: 6px; background: #000; }
.lb-cap { font-size: 12px; color: #cbd5e1; }
.lb-cap a { color: #818cf8; }
.lb-nav {
  position: fixed; top: 50%; transform: translateY(-50%);
  width: 46px; height: 70px; border: none; border-radius: 8px;
  background: rgba(30,35,48,.55); color: #fff; font-size: 34px; line-height: 1;
  cursor: pointer; z-index: 4300; display: flex; align-items: center; justify-content: center;
}
.lb-nav:hover { background: rgba(79,70,229,.85); }
.lb-prev { left: 14px; }
.lb-next { right: 14px; }
.lb-counter {
  position: fixed; top: 18px; left: 50%; transform: translateX(-50%);
  font-size: 12px; color: #e2e8f0; background: rgba(30,35,48,.7);
  padding: 4px 12px; border-radius: 12px; z-index: 4300;
}

/* Terminal */
#terminal-bar {
  display: flex; align-items: center; gap: 8px;
  padding: 5px 14px; background: #111318;
  border-top: 1px solid #2d3148; flex-shrink: 0;
  cursor: pointer; user-select: none;
}
#terminal-bar:hover { background: #15181f; }
#terminal-toggle-btn { font-size: 11px; color: #64748b; white-space: nowrap; display: flex; align-items: center; gap: 5px; }
#terminal-bar .term-dot { width:6px; height:6px; border-radius:50%; background:#22c55e; flex-shrink:0; animation: blink 2s infinite; }
#terminal-bar .term-dot.idle { background:#475569; animation:none; }
#terminal-last-msg { font-size: 11px; color: #475569; font-family: monospace; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; flex:1; }
#terminal-count { font-size: 10px; color: #475569; white-space: nowrap; }
#terminal-panel { display: none; flex-direction: column; height: 220px; background: #0a0c10; border-top: 1px solid #2d3148; flex-shrink: 0; overflow: hidden; }
#terminal-panel.open { display: flex; }
#terminal-toolbar { display: flex; align-items: center; gap: 8px; padding: 5px 12px; background: #111318; border-bottom: 1px solid #1e2334; flex-shrink: 0; }
#terminal-toolbar span { font-size: 11px; color: #475569; }
#terminal-filter { display: flex; gap: 4px; flex-wrap: wrap; }
.term-filter-btn { font-size: 10px; padding: 2px 8px; border-radius: 10px; cursor: pointer; border: 1px solid #2d3148; background: transparent; color: #475569; transition: all .12s; font-weight: 500; }
.term-filter-btn.active { border-color: #6366f1; color: #818cf8; background: #1e2044; }
.term-filter-btn[data-level="OK"].active    { border-color:#22c55e; color:#22c55e; background:#0f2e1a; }
.term-filter-btn[data-level="WARN"].active  { border-color:#f59e0b; color:#f59e0b; background:#2a1e00; }
.term-filter-btn[data-level="ERR"].active   { border-color:#ef4444; color:#ef4444; background:#2a0000; }
.term-filter-btn[data-level="GEO"].active   { border-color:#10b981; color:#10b981; background:#0a1e16; }
.term-filter-btn[data-level="SCRAPE"].active{ border-color:#818cf8; color:#818cf8; background:#1a1d40; }
.term-filter-btn[data-level="SEARCH"].active{ border-color:#60a5fa; color:#60a5fa; background:#0f1e30; }
.spacer-term { flex:1; }
#terminal-clear-btn { font-size: 10px; padding: 2px 8px; border-radius: 6px; cursor: pointer; border: 1px solid #3d4266; background: transparent; color: #64748b; }
#terminal-clear-btn:hover { color: #ef4444; border-color: #ef4444; }
#terminal-output { flex: 1; overflow-y: auto; font-family: 'SFMono-Regular','Consolas',monospace; font-size: 11px; padding: 6px 10px; line-height: 1.7; }
#terminal-output::-webkit-scrollbar { width: 4px; }
#terminal-output::-webkit-scrollbar-track { background: #0a0c10; }
#terminal-output::-webkit-scrollbar-thumb { background: #2d3148; border-radius: 2px; }
.term-line { display: flex; gap: 8px; align-items: baseline; padding: 1px 0; transition: background .08s; }
.term-line:hover { background: #111318; }
.term-ts  { color: #334155; white-space: nowrap; flex-shrink: 0; }
.term-lvl { font-weight: 700; white-space: nowrap; flex-shrink: 0; min-width: 46px; }
.term-msg { color: #94a3b8; word-break: break-all; }
.term-line[data-level="OK"]     .term-lvl { color: #22c55e; }
.term-line[data-level="OK"]     .term-msg { color: #bbf7d0; }
.term-line[data-level="WARN"]   .term-lvl { color: #f59e0b; }
.term-line[data-level="WARN"]   .term-msg { color: #fde68a; }
.term-line[data-level="ERR"]    .term-lvl { color: #ef4444; }
.term-line[data-level="ERR"]    .term-msg { color: #fca5a5; }
.term-line[data-level="GEO"]    .term-lvl { color: #10b981; }
.term-line[data-level="GEO"]    .term-msg { color: #6ee7b7; }
.term-line[data-level="SCRAPE"] .term-lvl { color: #818cf8; }
.term-line[data-level="SCRAPE"] .term-msg { color: #c4b5fd; }
.term-line[data-level="SEARCH"] .term-lvl { color: #60a5fa; }
.term-line[data-level="SEARCH"] .term-msg { color: #bfdbfe; }
.term-line[data-level="INFO"]   .term-lvl { color: #64748b; }
.term-line[data-level="INFO"]   .term-msg { color: #94a3b8; }
.term-line.term-new { animation: termFade .4s ease; }
@keyframes termFade { from { background: #1a1d30; } to { background: transparent; } }
</style>
</head>
<body>
<div id="wrapper">
<div id="header">
  <div class="dot" id="dot"></div>
  <h1>Arkadia <span style="font-size:10px;color:#6366f1;font-weight:400;">v4</span></h1>
  <label>Cidade:</label>
  <input id="cidade-input" type="text" placeholder="ex: Guarapari" value="Guarapari"/>
  <label>Intervalo:</label>
  <select id="intervalo-select">
    <option value="1">1 min</option>
    <option value="2">2 min</option>
    <option value="5" selected>5 min</option>
    <option value="10">10 min</option>
    <option value="30">30 min</option>
  </select>
  <label>Filtro:</label>
  <select id="horas-select">
    <option value="3">3h</option>
    <option value="6">6h</option>
    <option value="12">12h</option>
    <option value="24" selected>24h</option>
    <option value="48">2 dias</option>
    <option value="168">7 dias</option>
    <option value="720">1 mês</option>
    <option value="2160">3 meses</option>
  </select>
  <button id="btn-aplicar" onclick="aplicarConfig()">Aplicar</button>
  <button class="danger" onclick="limpar()">Limpar</button>
  <div class="spacer"></div>
  <span id="proxima-busca" title="Tempo até a próxima atualização automática"></span>
  <span id="status-text">—</span>
  <span id="geo-refinando">refinando geo…</span>
  <div id="count-badge">0 notícias</div>
</div>
<div id="main">
  <div id="map-wrapper">
    <div id="map"></div>
    <div id="map-controls">
      <button id="btn-fit" onclick="ajustarATodos()" title="Ajustar o mapa a todos os pins">⤢ Ver todos</button>
    </div>
    <div id="map-legend">
      <div class="leg-title">Legenda <span id="leg-toggle" onclick="toggleLegenda()">▾</span></div>
      <div id="leg-body">
        <div class="leg-row"><span class="leg-dot" style="background:#10b981"></span> Bairro</div>
        <div class="leg-row"><span class="leg-dot" style="background:#f59e0b"></span> Rua exata</div>
        <div class="leg-row"><span class="leg-dot" style="background:#ef4444"></span> Múltiplas fontes</div>
        <div class="leg-row"><span class="leg-dot leg-area"></span> Cidade (sem local)</div>
      </div>
    </div>
  </div>
  <div id="sidebar">
    <div id="sidebar-header">
      <span>Feed de notícias</span>
      <span id="last-update">—</span>
    </div>
    <div id="sidebar-tools">
      <input id="lista-busca" type="text" placeholder="🔎 filtrar por palavra…" oninput="onListaCfg()">
      <select id="lista-sort" onchange="onListaCfg()" title="Ordenar">
        <option value="recentes">⏱ Recentes</option>
        <option value="antigas">⏱ Mais antigas</option>
        <option value="confianca">✓ Confiança</option>
        <option value="precisao">📍 Precisão do local</option>
      </select>
      <button id="lista-mapa" class="tool-toggle" onclick="toggleSoMapa()" title="Mostrar só notícias com local no mapa">📍 só no mapa</button>
    </div>
    <div id="sidebar-resumo"></div>
    <div id="news-list">
      <div id="empty-state">📡<p>Aguardando primeira busca...</p></div>
    </div>
  </div>
</div>
<div id="terminal-bar" onclick="toggleTerminal()">
  <span id="terminal-toggle-btn">
    <span class="term-dot idle" id="term-dot"></span>
    <span id="terminal-label">▶ Terminal</span>
  </span>
  <span id="terminal-last-msg">aguardando logs…</span>
  <span id="terminal-count">0 linhas</span>
</div>
<div id="terminal-panel">
  <div id="terminal-toolbar">
    <span>Filtro:</span>
    <div id="terminal-filter">
      <button class="term-filter-btn active" data-level="ALL">Todos</button>
      <button class="term-filter-btn" data-level="OK">✅ OK</button>
      <button class="term-filter-btn" data-level="WARN">⚠️ Warn</button>
      <button class="term-filter-btn" data-level="ERR">✗ Erro</button>
      <button class="term-filter-btn" data-level="GEO">📍 Geo</button>
      <button class="term-filter-btn" data-level="SCRAPE">🌐 Scrape</button>
      <button class="term-filter-btn" data-level="SEARCH">🔍 Busca</button>
      <button class="term-filter-btn" data-level="INFO">ℹ️ Info</button>
    </div>
    <div class="spacer-term"></div>
    <label style="font-size:10px;color:#475569;display:flex;align-items:center;gap:4px;cursor:pointer;">
      <input type="checkbox" id="term-autoscroll" checked style="accent-color:#6366f1;"> Auto-scroll
    </label>
    <button id="terminal-clear-btn" onclick="termClear()">🗑 Limpar</button>
  </div>
  <div id="terminal-output"></div>
</div>
</div>

<script>
const API = 'http://localhost:5050';
let newsCache=[], newsById={}, selectedId=null, cidade_atual='Guarapari';
let _listaCfg={q:'', sort:'recentes', soMapa:false};
let _ultimaBuscaTs=null;   // timestamp da última busca (para a contagem regressiva)
const _novosIds=new Set(); // ids recém-chegados (para flash visual)
let markers={};   // id → array com 1 L.marker (local principal)
let cityHighlight=null;   // camada de destaque da cidade inteira (polígono/círculo)
const _zonaCache={};      // cache de contorno da cidade no front
const _coordUso={};       // "lat,lon" → quantos marcadores já nesse ponto (anti-sobreposição)
const openPreviews={};


function escHtml(s){if(s==null)return'';return String(s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;');}
function _normJs(s){return String(s||'').toLowerCase().normalize('NFD').replace(/[\u0300-\u036f]/g,'');}
function escAttr(s){if(s==null)return'';return String(s).replace(/"/g,'&quot;').replace(/'/g,'&#39;');}

// Tempo relativo: "agora", "há 5 min", "há 2 h", "há 4 dias"…
function tempoRelativo(iso){
  if(!iso) return '';
  const t=Date.parse(iso); if(isNaN(t)) return '';
  let s=Math.floor((Date.now()-t)/1000);
  if(s<0) s=0;
  if(s<60) return 'agora';
  const min=Math.floor(s/60); if(min<60) return `há ${min} min`;
  const h=Math.floor(min/60); if(h<24) return `há ${h} h`;
  const d=Math.floor(h/24); if(d<30) return `há ${d} ${d===1?'dia':'dias'}`;
  const me=Math.floor(d/30); if(me<12) return `há ${me} ${me===1?'mês':'meses'}`;
  const a=Math.floor(d/365); return `há ${a} ${a===1?'ano':'anos'}`;
}
function atualizarTemposRelativos(){
  document.querySelectorAll('.card-rel').forEach(el=>{
    const iso=el.getAttribute('data-iso');
    if(iso) el.textContent=tempoRelativo(iso);
  });
}
// garante que exatamente um bairro esteja marcado como principal (o 1º)
function _marcarPrincipal(bs){
  if(bs&&bs.length&&!bs.some(b=>b&&b.principal)){
    bs.forEach((b,i)=>{ if(b) b.principal=(i===0); });
  }
  return bs;
}
// chip de local: principal (verde) x também citado (laranja)
function bairroChip(b){
  const ehPrincipal = b.principal===true;
  const ic = ehPrincipal ? '🎯' : '📍';
  const cls = ehPrincipal ? 'bairro-tag bt-fato' : 'bairro-tag bt-cit';
  const ttl = ehPrincipal ? 'Local principal do fato' : 'Também citado na notícia';
  const extra=(b.fontes&&b.fontes>1)?` · ${b.fontes} fontes`:'';
  return `<span class="${cls}" title="${escAttr(ttl)}">${ic} ${escHtml(b.nome)}${extra}</span>`;
}

const map = L.map('map',{center:[-20.67,-40.51],zoom:12});
L.tileLayer('https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png',{attribution:'© OpenStreetMap',maxZoom:19}).addTo(map);

function makeIcon(multi,precisao,refinado){
  const ehRua=(precisao==='rua');
  let color = ehRua ? '#f59e0b' : '#10b981';   // rua=laranja, bairro=verde
  let pulse=false;
  if(multi && ehRua){ color='#f59e0b'; pulse=true; }  // múltiplas fontes + rua = laranja pulsando vermelho
  else if(multi){ color='#ef4444'; }                  // múltiplas fontes (bairro) = vermelho
  const size=multi?18:15;
  const pulseHtml = pulse ? '<div class="pin-pulse"></div>' : '';
  return L.divIcon({
    className:'',
    html:`<div class="pin-wrap" style="width:${size}px;height:${size}px;">${pulseHtml}<div class="pin-dot" style="width:${size}px;height:${size}px;background:${color};box-shadow:0 0 0 3px ${color}44;"></div></div>`,
    iconSize:[size,size],iconAnchor:[size/2,size/2],
  });
}

// nome do jornal/portal de cada fonte (ex.: "G1", "Folha Vitória")
function nomeFonte(n,j){
  let f=((n.fontes&&n.fontes[j])||'').trim();
  if(!f||/^fonte desconhecida$/i.test(f)){
    try{f=new URL(n.links[j]).hostname.replace('www.','');}catch(e){f='Fonte '+(j+1);}
  }
  return f;
}
function srcImagem(x){return (x&&typeof x==='object')?x.src:x;}

function makePopupHtml(n,manual,imgSrc,focoNome){
  const precisaoText={rua:'📍 Rua exata',bairro:'🏘️ Bairro',cidade:'🏙️ Cidade',estado:'🗺️ Estado',manual:'📌 Fixado',local:'📍 Local'}[n.precisao]||'📍';
  let imgHtml='';
  if(imgSrc) imgHtml=`<img src="${escAttr(imgSrc)}" onerror="this.style.display='none'" onclick="abrirMidia('${n.id}')" title="Ver mídia em tamanho real" style="width:100%;max-height:140px;object-fit:cover;border-radius:5px;margin-bottom:7px;display:block;border:1px solid #3d4266;cursor:zoom-in;">`;
  // cabeçalho com o LOCAL do fato (rua quando houver, senão bairro)
  const local = n.label || (n.bairros&&n.bairros[0]&&n.bairros[0].nome) || cidade_atual;
  const header=`<div class="popup-foco foco-princ">${precisaoText}: <b>${escHtml(local)}</b></div>`;
  const rel=tempoRelativo(n.data_iso);
  const dataHtml=`<div class="popup-data">📅 ${escHtml(n.data||'')}${rel?` · <b>${escHtml(rel)}</b>`:''}</div>`;
  const fontesLinks=n.links.map((l,j)=>`<a class="popup-link" href="${escAttr(l)}" target="_blank">🔗 ${escHtml(nomeFonte(n,j))}</a>`).join(' · ');
  const tituloPrefix=manual?'📌 ':'';
  return imgHtml
    + header
    + `<div class="popup-titulo">${tituloPrefix}${escHtml(n.titulo)}</div>`
    + dataHtml
    + `<div class="popup-botoes">`
    +   `<button class="popup-midia-btn" onclick="abrirMidia('${n.id}')">🖼 Mídia</button>`
    +   `<button class="popup-stats-btn" onclick="abrirEstatisticas('${n.id}')">📊 Estatísticas</button>`
    + `</div>`
    + `<div class="popup-fontes-links">${fontesLinks}</div>`;
}

const _popupImgCache={};
const _scrapeCache={};
// busca mídia de TODAS as fontes do card de uma vez (api_scrape agrega imagens/vídeos)
async function _scrapeAll(n){
  if(_scrapeCache[n.id]!==undefined) return _scrapeCache[n.id];
  const links=(n.links||[]).filter(Boolean);
  if(!links.length){_scrapeCache[n.id]=null;return null;}
  try{
    const principal=links[0];
    const extra=links.slice(1).join(',');
    let qs=`url=${encodeURIComponent(principal)}`;
    if(extra) qs+=`&urls=${encodeURIComponent(extra)}`;
    const res=await fetch(`${API}/api/scrape?${qs}`);
    const data=await res.json();
    _scrapeCache[n.id]=data;return data;
  }catch(e){_scrapeCache[n.id]=null;return null;}
}
async function _getPopupImg(n){
  if(_popupImgCache[n.id]!==undefined) return _popupImgCache[n.id];
  const data=await _scrapeAll(n);
  let img=null;
  if(data&&data.images&&data.images.length) img=srcImagem(data.images[0]);
  _popupImgCache[n.id]=img;return img;
}

// ─────────────────────────────────────────────
//  GALERIA DE MÍDIA + LIGHTBOX (dentro do mapa, sem redirecionar)
// ─────────────────────────────────────────────
let _midiaImgs=[], _midiaVids=[], _lbIndex=-1;
function _embedYoutube(u){let e=u;if(!e.includes('/embed/'))e=e.replace('watch?v=','embed/').replace('youtu.be/','youtube.com/embed/');if(!e.startsWith('http'))e='https:'+e;if(!/autoplay=/.test(e))e+=(e.includes('?')?'&':'?')+'autoplay=1&rel=0';return e;}
function _embedVimeo(u){let e=u;if(!e.includes('player.vimeo'))e=e.replace('vimeo.com/','player.vimeo.com/video/');if(!/autoplay=/.test(e))e+=(e.includes('?')?'&':'?')+'autoplay=1';return e;}

async function abrirMidia(id){
  const n=newsById[id]; if(!n) return;
  let ov=document.getElementById('midia-overlay');
  if(!ov){ov=document.createElement('div');ov.id='midia-overlay';
    ov.addEventListener('click',e=>{if(e.target===ov)fecharMidia();});
    document.body.appendChild(ov);}
  ov.innerHTML=`<div class="midia-box">
      <button class="midia-close" onclick="fecharMidia()"><svg viewBox="0 0 14 14" fill="none" xmlns="http://www.w3.org/2000/svg"><path d="M1 1L13 13M13 1L1 13" stroke="currentColor" stroke-width="1.6" stroke-linecap="round"/></svg></button>
      <div class="midia-head">🖼 Mídia — ${escHtml(n.titulo)}</div>
      <div class="midia-body" id="midia-body"><div class="preview-loading">⏳ Carregando mídia de todas as fontes…</div></div>
    </div>`;
  ov.style.display='flex';
  document.addEventListener('keydown',_midiaKey);
  const data=await _scrapeAll(n);
  const body=document.getElementById('midia-body');
  if(body) body.innerHTML=_galeriaHtml(n,data);
}
function _midiaKey(e){
  const lb=document.getElementById('midia-lightbox');
  const lbAberto=lb&&lb.style.display==='flex';
  if(e.key==='Escape'){ if(lbAberto){_fecharLightbox();}else{fecharMidia();} return; }
  if(lbAberto&&_lbIndex>=0){
    if(e.key==='ArrowRight'){e.preventDefault();_lbNav(1);}
    else if(e.key==='ArrowLeft'){e.preventDefault();_lbNav(-1);}
  }
}
function fecharMidia(){
  _fecharLightbox();
  const ov=document.getElementById('midia-overlay');
  if(ov){ov.style.display='none';ov.innerHTML='';}
  document.removeEventListener('keydown',_midiaKey);
}

// ─────────────────────────────────────────────
//  MODAL DE ESTATÍSTICAS (confiança, razões, trechos de origem)
// ─────────────────────────────────────────────
function _statsKey(e){ if(e.key==='Escape') fecharStats(); }
function fecharStats(){
  const ov=document.getElementById('stats-overlay');
  if(ov){ov.style.display='none';ov.innerHTML='';}
  document.removeEventListener('keydown',_statsKey);
}
function abrirEstatisticas(id){
  const n=newsById[id]; if(!n) return;
  const st=n.estatisticas||{};

  // ── LOCAL DO FATO (mais importante) ──
  const precMap={rua:'rua exata',bairro:'bairro',cidade:'cidade inteira',local:'local',estado:'estado'};
  const precis=precMap[n.precisao||st.precisao]||'—';
  const precCls=(n.precisao==='rua')?'pp-rua':(n.precisao==='cidade')?'pp-cidade':'pp-bairro';
  let localSec=`<div class="st-sec">
    <div class="st-sec-title">📍 Onde aconteceu</div>
    <div class="st-local"><b>${escHtml(n.label||st.local||cidade_atual)}</b>
      <span class="st-prec ${precCls}">${escHtml(precis)}</span></div>`;
  if(st.local_trecho){
    localSec+=`<div class="st-quote-label">Identificado neste trecho da matéria:</div>
      <div class="st-quote">${escHtml(st.local_trecho)}${st.local_fonte?`<div class="st-src">— ${escHtml(st.local_fonte)}</div>`:''}</div>`;
  } else {
    // tenta buscar o trecho a partir da descrição do scrape (sem bloquear a abertura)
    localSec+=`<div class="st-quote-label dim" id="st-trecho-label-${n.id}">Buscando trecho…</div>
      <div class="st-quote" id="st-trecho-${n.id}" style="display:none"></div>`;
  }
  localSec+=`</div>`;

  // ── VIA (se houver) ──
  let viaSec='';
  const rua=n.rua||st.rua;
  if(rua){
    viaSec=`<div class="st-sec"><div class="st-sec-title">🛣️ Rua/avenida do fato</div>
      <div class="st-local"><b>${escHtml(rua)}</b></div>`;
    if(st.rua_trecho){
      viaSec+=`<div class="st-quote-label">Citada neste trecho:</div>
        <div class="st-quote">${escHtml(st.rua_trecho)}${st.rua_fonte?`<div class="st-src">— ${escHtml(st.rua_fonte)}</div>`:''}</div>`;
    } else {
      // tenta buscar o trecho da via a partir da descrição do scrape (sem bloquear a abertura)
      viaSec+=`<div class="st-quote-label dim" id="st-via-trecho-label-${n.id}">Buscando trecho…</div>
        <div class="st-quote" id="st-via-trecho-${n.id}" style="display:none"></div>`;
    }
    viaSec+=`</div>`;
  }

  // ── CONFIANÇA + por que juntou (só quando há mais de uma fonte) ──
  let corrSec='';
  const c=(n.confianca_corr!=null?n.confianca_corr:st.confianca);
  if(n.multi&&c!=null){
    const pct=Math.round(c*100);
    const cls=c>=0.80?'m-alta':c>=0.60?'m-media':'m-baixa';
    const frase=c>=0.80?'Quase certeza que é a mesma notícia'
              :c>=0.60?'Provavelmente a mesma notícia'
              :'Possivelmente a mesma notícia';
    const rz=(n.razoes_corr&&n.razoes_corr.length?n.razoes_corr:st.razoes)||[];
    corrSec=`<div class="st-sec">
      <div class="st-sec-title">🔗 Por que juntamos ${(n.fontes||[]).length} fontes</div>
      <div class="st-conf-frase">${frase} <b>(${pct}%)</b></div>
      <div class="st-meter"><div class="st-meter-fill ${cls}" style="width:${pct}%"></div></div>
      ${rz.length?`<ul class="st-list">${rz.map(r=>`<li>${escHtml(r)}</li>`).join('')}</ul>`:''}
    </div>`;
  }

  // ── FONTES ──
  const fontesSec=`<div class="st-sec"><div class="st-sec-title">📰 Fontes (${(n.fontes||[]).length})</div>
    <div class="st-srclist">${(n.fontes||[]).map((f,j)=>`<a href="${escAttr(n.links[j]||'#')}" target="_blank" class="st-srctag">${escHtml(nomeFonte(n,j))}</a>`).join('')}</div></div>`;

  let ov=document.getElementById('stats-overlay');
  if(!ov){ov=document.createElement('div');ov.id='stats-overlay';
    ov.addEventListener('click',e=>{if(e.target===ov)fecharStats();});
    document.body.appendChild(ov);}
  ov.innerHTML=`<div class="stats-box">
      <button class="midia-close" onclick="fecharStats()"><svg viewBox="0 0 14 14" fill="none" xmlns="http://www.w3.org/2000/svg"><path d="M1 1L13 13M13 1L1 13" stroke="currentColor" stroke-width="1.6" stroke-linecap="round"/></svg></button>
      <div class="midia-head">📊 Como identificamos esta notícia</div>
      <div class="stats-sub">${escHtml(n.titulo)}</div>
      <div class="stats-body">
        ${localSec}${viaSec}${corrSec}${fontesSec}
        <div class="st-note">Tudo é feito automaticamente, sem IA: o local vem da leitura do texto e o agrupamento, da semelhança entre as matérias.</div>
      </div>
    </div>`;
  ov.style.display='flex';
  document.addEventListener('keydown',_statsKey);
  // se algum trecho estava ausente (local e/ou via), tenta buscá-lo via scrape em background
  if((!st.local_trecho || (rua && !st.rua_trecho)) && n.links && n.links.length){
    _buscarTrechoAsync(n);
  }
}
async function _buscarTrechoAsync(n){
  try{
    const st=n.estatisticas||{};
    const data=await _scrapeAll(n);
    if(!data) return;
    const haystack=((data.description||'')+' '+(data.title||'')).trim();
    const bairroNome=(n.label||(n.bairros&&n.bairros[0]&&n.bairros[0].nome)||'');
    const ruaNome=(n.rua||st.rua||'');
    if(!st.local_trecho){
      _aplicarTrechoBuscado(n,haystack,data,bairroNome,
        `st-trecho-label-${n.id}`,`st-trecho-${n.id}`,'local_trecho');
    }
    if(ruaNome && !st.rua_trecho){
      _aplicarTrechoBuscado(n,haystack,data,ruaNome,
        `st-via-trecho-label-${n.id}`,`st-via-trecho-${n.id}`,'rua_trecho');
    }
  }catch(e){}
}
function _aplicarTrechoBuscado(n,haystack,data,termoOriginal,labelElId,quoteElId,campoSalvar){
  // busca no haystack (descrição/título da matéria) um trecho de ~160 chars ao redor do termo.
  // Compara de forma normalizada (sem acento/caixa) para não falhar por causa de
  // acentuação diferente entre o nome do bairro e o texto da fonte, mas o trecho
  // exibido sempre usa o texto ORIGINAL (com acento).
  // IMPORTANTE: nunca cair para um trecho genérico (ex.: início da descrição) quando o
  // termo não é encontrado — isso mostraria um trecho sem relação com o bairro/rua.
  const termo=_normJs(termoOriginal);
  let trecho='';
  if(termo){
    const idx=_normJs(haystack).indexOf(termo);
    if(idx>=0){
      const ini=Math.max(0,idx-80);
      const fim=Math.min(haystack.length,idx+termo.length+80);
      trecho='…'+haystack.slice(ini,fim).replace(/\s+/g,' ').trim()+'…';
    }
  }
  const labelEl=document.getElementById(labelElId);
  const quoteEl=document.getElementById(quoteElId);
  if(!labelEl||!quoteEl) return; // modal já fechou
  if(trecho){
    labelEl.className='st-quote-label';
    labelEl.textContent='Trecho encontrado na matéria:';
    quoteEl.textContent=trecho;
    quoteEl.style.display='';
    // salva para próximas aberturas
    if(!n.estatisticas) n.estatisticas={};
    n.estatisticas[campoSalvar]=trecho;
  } else {
    labelEl.className='st-quote-label dim';
    labelEl.textContent='Trecho de origem não disponível para esta fonte.';
  }
}
function _galeriaHtml(n,data){
  if(!data) return '<div class="preview-empty">Erro ao carregar mídia.</div>';
  _midiaImgs=(data.images||[]).map(x=> (typeof x==='string')?{src:x,fonte:''}:x);
  _midiaVids=data.videos||[];
  const nF=(n.links||[]).length;
  let h='';
  if(data.description) h+=`<div class="preview-desc">${escHtml(data.description.slice(0,320))}</div>`;
  if(_midiaVids.length){
    h+=`<div class="preview-cap">🎬 ${_midiaVids.length} vídeo(s)</div><div class="midia-grid">`;
    _midiaVids.forEach((v,i)=>{
      h+=`<div class="midia-item vid" onclick="verVideo(${i})" title="Assistir aqui">
        ${v.poster?`<img src="${escAttr(v.poster)}" onerror="this.style.display='none'">`:''}
        <span class="midia-play">▶</span>
        <span class="midia-fonte">${escHtml(v.fonte||v.type||'vídeo')}</span></div>`;
    });
    h+='</div>';
  }
  if(_midiaImgs.length){
    h+=`<div class="preview-cap">🖼 ${_midiaImgs.length} imagem(ns) de ${nF} fonte(s)</div><div class="midia-grid">`;
    _midiaImgs.forEach((im,i)=>{
      h+=`<div class="midia-item" onclick="verImagem(${i})" title="Ver em tamanho real">
        <img src="${escAttr(im.src)}" loading="lazy" onerror="this.closest('.midia-item').remove()">
        ${im.fonte?`<span class="midia-fonte">${escHtml(im.fonte)}</span>`:''}</div>`;
    });
    h+='</div>';
  }
  return h||'<div class="preview-empty">Nenhuma mídia relacionada encontrada.</div>';
}
function verImagem(i){
  if(i<0||i>=_midiaImgs.length) return;
  _lbIndex=i;
  _renderImagemLightbox();
}
function _lbNav(delta){
  if(!_midiaImgs.length) return;
  _lbIndex=(_lbIndex+delta+_midiaImgs.length)%_midiaImgs.length;
  _renderImagemLightbox();
}
function _renderImagemLightbox(){
  const im=_midiaImgs[_lbIndex]; if(!im) return;
  const total=_midiaImgs.length;
  const navBtns = total>1
    ? `<button class="lb-nav lb-prev" onclick="event.stopPropagation();_lbNav(-1)" title="Anterior (←)">‹</button>
       <button class="lb-nav lb-next" onclick="event.stopPropagation();_lbNav(1)" title="Próxima (→)">›</button>
       <div class="lb-counter">${_lbIndex+1} / ${total}</div>`
    : '';
  _abrirLightbox(
    `<img class="lb-img" src="${escAttr(im.src)}">`+
    navBtns+
    `<div class="lb-cap">${im.fonte?'📰 '+escHtml(im.fonte)+' — ':''}<a href="${escAttr(im.src)}" target="_blank">abrir original</a></div>`);
}
function verVideo(i){
  const v=_midiaVids[i]; if(!v) return;
  _lbIndex=-1;   // vídeo não entra na navegação de imagens
  let inner='';
  if(v.type==='youtube') inner=`<iframe class="lb-video" src="${escAttr(_embedYoutube(v.url))}" frameborder="0" allow="autoplay; encrypted-media; fullscreen" allowfullscreen></iframe>`;
  else if(v.type==='vimeo') inner=`<iframe class="lb-video" src="${escAttr(_embedVimeo(v.url))}" frameborder="0" allow="autoplay; fullscreen" allowfullscreen></iframe>`;
  else if(v.type==='dailymotion') inner=`<iframe class="lb-video" src="${escAttr(v.url)}" frameborder="0" allow="autoplay; fullscreen" allowfullscreen></iframe>`;
  else inner=`<video class="lb-video" src="${escAttr(v.url)}" controls autoplay ${v.poster?`poster="${escAttr(v.poster)}"`:''}></video>`;
  _abrirLightbox(inner+`<div class="lb-cap">${v.fonte?'📰 '+escHtml(v.fonte):''}</div>`);
}
function _abrirLightbox(html){
  let lb=document.getElementById('midia-lightbox');
  if(!lb){lb=document.createElement('div');lb.id='midia-lightbox';
    lb.addEventListener('click',e=>{if(e.target===lb)_fecharLightbox();});
    document.body.appendChild(lb);}
  lb.innerHTML=`<button class="lb-close" onclick="_fecharLightbox()"><svg viewBox="0 0 14 14" fill="none" xmlns="http://www.w3.org/2000/svg"><path d="M1 1L13 13M13 1L1 13" stroke="currentColor" stroke-width="1.6" stroke-linecap="round"/></svg></button><div class="lb-inner">${html}</div>`;
  lb.style.display='flex';
  // zoom na imagem: click + scroll de roda + pinch
  const img=lb.querySelector('.lb-img');
  if(img) _ativarZoomLb(img);
}
function _fecharLightbox(){
  const lb=document.getElementById('midia-lightbox');
  if(lb){lb.style.display='none';lb.innerHTML='';}
  _lbZoom=1; _lbPanX=0; _lbPanY=0;
}
let _lbZoom=1, _lbPanX=0, _lbPanY=0;
function _lbAplicarTransform(img){
  img.style.transform=`scale(${_lbZoom}) translate(${_lbPanX/_lbZoom}px,${_lbPanY/_lbZoom}px)`;
  img.classList.toggle('zoomed',_lbZoom>1);
}
function _ativarZoomLb(img){
  _lbZoom=1; _lbPanX=0; _lbPanY=0;
  // click: toggle 1x / 2.5x
  img.addEventListener('click',e=>{
    e.stopPropagation();
    if(_lbZoom>1){_lbZoom=1;_lbPanX=0;_lbPanY=0;}
    else{
      const r=img.getBoundingClientRect();
      const ox=e.clientX-r.left-r.width/2;
      const oy=e.clientY-r.top-r.height/2;
      _lbZoom=2.5; _lbPanX=ox*(_lbZoom-1)*-1; _lbPanY=oy*(_lbZoom-1)*-1;
    }
    _lbAplicarTransform(img);
  });
  // scroll de roda: zoom livre
  img.addEventListener('wheel',e=>{
    e.preventDefault();
    const fator=e.deltaY<0?1.15:0.87;
    _lbZoom=Math.min(6,Math.max(1,_lbZoom*fator));
    if(_lbZoom===1){_lbPanX=0;_lbPanY=0;}
    _lbAplicarTransform(img);
  },{passive:false});
  // pinch (touch)
  let _ptch=null;
  img.addEventListener('touchstart',e=>{
    if(e.touches.length===2){
      _ptch={d:Math.hypot(e.touches[0].clientX-e.touches[1].clientX,e.touches[0].clientY-e.touches[1].clientY),z:_lbZoom};
      e.preventDefault();
    }
  },{passive:false});
  img.addEventListener('touchmove',e=>{
    if(e.touches.length===2&&_ptch){
      const d=Math.hypot(e.touches[0].clientX-e.touches[1].clientX,e.touches[0].clientY-e.touches[1].clientY);
      _lbZoom=Math.min(6,Math.max(1,_ptch.z*(d/_ptch.d)));
      if(_lbZoom===1){_lbPanX=0;_lbPanY=0;}
      _lbAplicarTransform(img); e.preventDefault();
    }
  },{passive:false});
  img.addEventListener('touchend',()=>{_ptch=null;});
}

function _removerMarcadores(id){
  const arr=markers[id];
  if(arr){
    arr.forEach(m=>{
      // libera o ponto usado (anti-sobreposição)
      if(m._coordKey&&_coordUso[m._coordKey]){_coordUso[m._coordKey]--;}
      map.removeLayer(m);
    });
    delete markers[id];
  }
}

// Afasta o marcador num espiral quando outro já ocupa (quase) o mesmo ponto.
function _posSemSobreposicao(lat,lon){
  // chave ~111 m (toFixed(3)): agrupa pontos do mesmo bairro/centroide
  const key=lat.toFixed(3)+','+lon.toFixed(3);
  const usados=_coordUso[key]||0;
  _coordUso[key]=usados+1;
  if(usados===0) return {lat,lon,key};
  // espiral com ângulo áureo; ~180 m por anel — visível mesmo em zoom afastado
  const ang=usados*2.39996;
  const anel=Math.ceil(usados/6);
  const raio=0.0016*anel;
  return {
    lat: lat + raio*Math.cos(ang),
    lon: lon + raio*Math.sin(ang)/Math.cos(lat*Math.PI/180),
    key,
  };
}

function _criarMarcadores(n, bairros){
  _removerMarcadores(n.id);
  if(!bairros||!bairros.length) return;
  // plota SOMENTE o local principal do fato (rua quando houver, senão bairro)
  const principal=bairros[0];
  const pos=_posSemSobreposicao(principal.lat,principal.lon);
  const m=L.marker([pos.lat,pos.lon],{icon:makeIcon(n.multi,n.precisao,n.geo_refinado)}).addTo(map);
  m._coordKey=pos.key;
  m.bindPopup(makePopupHtml(n,false,null,principal.nome),{maxWidth:300,minWidth:240});
  m.on('click',()=>selectCard(n.id));
  m.on('popupopen',async()=>{
    const img=await _getPopupImg(n);
    if(img){m.setPopupContent(makePopupHtml(newsById[n.id]||n,false,img,principal.nome));}
  });
  markers[n.id]=[m];
}

function adicionarMarcador(n){
  if(markers[n.id]) return;
  const bairros=n.bairros&&n.bairros.length?_marcarPrincipal(n.bairros):null;
  if(bairros){
    _criarMarcadores(n,bairros);
  }
  // sem bairro = não plota marcador; a notícia fica no card lateral e,
  // ao ser clicada, destaca a cidade inteira (ver selectCard).
}

function atualizarMarcador(n){
  _removerMarcadores(n.id);
  adicionarMarcador(n);
}

// ─── Destaque da cidade inteira (para notícias sem bairro) ───
function _limparDestaqueCidade(){
  if(cityHighlight){map.removeLayer(cityHighlight);cityHighlight=null;}
}

async function destacarCidade(){
  _limparDestaqueCidade();
  let zona=_zonaCache[cidade_atual];
  if(!zona){
    try{
      const r=await fetch(`${API}/api/cidade_zona?cidade=${encodeURIComponent(cidade_atual)}`);
      zona=await r.json();
      _zonaCache[cidade_atual]=zona;
    }catch(e){zona=null;}
  }
  if(!zona) return;
  const estilo={color:'#6366f1',weight:2,fillColor:'#6366f1',fillOpacity:0.10,dashArray:'6 4'};
  if(zona.tipo==='poligono'&&zona.geojson){
    cityHighlight=L.geoJSON(zona.geojson,{style:estilo}).addTo(map);
    try{map.fitBounds(cityHighlight.getBounds(),{padding:[40,40],maxZoom:14});}catch(e){
      if(zona.lat!=null)map.flyTo([zona.lat,zona.lon],12,{duration:1});
    }
  } else if(zona.lat!=null){
    cityHighlight=L.circle([zona.lat,zona.lon],{radius:zona.raio_m||5000,...estilo}).addTo(map);
    try{map.fitBounds(cityHighlight.getBounds(),{padding:[40,40],maxZoom:14});}catch(e){
      map.flyTo([zona.lat,zona.lon],12,{duration:1});
    }
  }
}

function renderCard(n){
  const bairros=n.bairros&&n.bairros.length?n.bairros:null;
  let bairrosHtml='';
  if(bairros){
    const nomes=bairros.map(bairroChip).join('');
    bairrosHtml=`<div class="bairros-encontrados">${nomes}</div>`;
  } else {
    bairrosHtml=`<div class="bairros-sem">🏙️ só cidade — clique para destacar a área</div>`;
  }
  return `<div class="card" id="card-${n.id}" onclick="selectCard('${n.id}')">
    <div class="card-city">
      ${escHtml(cidade_atual)}
      ${n.multi?'<span class="badge-multi">MÚLTIPLAS FONTES</span>':''}
    </div>
    ${bairrosHtml}
    <div class="card-title">${escHtml(n.titulo)}</div>
    <div class="card-meta">📅 ${escHtml(n.data)} · <span class="card-rel" data-iso="${escAttr(n.data_iso||'')}">${escHtml(tempoRelativo(n.data_iso))}</span><span class="card-stats" onclick="event.stopPropagation();abrirEstatisticas('${n.id}')" title="Como esta notícia foi identificada">📊</span></div>
    <div class="card-links">${n.links.map((l,j)=>`<a href="${escAttr(l)}" target="_blank">🔗 ${escHtml(nomeFonte(n,j))}</a>`).join('')}</div>
  </div>`;
}

function renderTudo(data){
  const badge=document.getElementById('count-badge');
  newsCache=data.noticias||[];
  newsById={};newsCache.forEach(n=>{newsById[n.id]=n;});
  badge.textContent=`${newsCache.length} notícia${newsCache.length!==1?'s':''}`;
  if(data.ultima_busca){_ultimaBuscaTs=_parseDataBR(data.ultima_busca);}
  document.getElementById('last-update').textContent=data.ultima_busca?`Atualizado ${data.ultima_busca.slice(11)}`:'—';
  const dot=document.getElementById('dot');
  dot.className='dot'+(data.buscando?' loading':'');
  document.getElementById('status-text').textContent=data.buscando?'buscando...':`${data.total_visto} vistas | ${data.cidade}`;
  newsCache.forEach(adicionarMarcador);
  aplicarLista();
  atualizarCountdown();
}

// "dd/mm/aaaa hh:mm:ss" → ms
function _parseDataBR(s){
  try{const m=s.match(/(\d{2})\/(\d{2})\/(\d{4})\s+(\d{2}):(\d{2}):(\d{2})/);
    if(!m)return null;return new Date(+m[3],+m[2]-1,+m[1],+m[4],+m[5],+m[6]).getTime();
  }catch(e){return null;}
}

function temLocal(n){return !!(n.bairros&&n.bairros.length);}

// aplica busca + ordenação + filtro "só no mapa" e renderiza a lista
function aplicarLista(){
  const list=document.getElementById('news-list');
  if(!list)return;
  let arr=newsCache.slice();
  const q=(_listaCfg.q||'').trim().toLowerCase();
  if(q) arr=arr.filter(n=>(
    (n.titulo||'').toLowerCase().includes(q) ||
    (n.label||'').toLowerCase().includes(q) ||
    (n.fontes||[]).join(' ').toLowerCase().includes(q)
  ));
  if(_listaCfg.soMapa) arr=arr.filter(temLocal);
  const precScore=p=>({rua:3,bairro:2,local:2,cidade:1}[p]||0);
  if(_listaCfg.sort==='recentes') arr.sort((a,b)=>(Date.parse(b.data_iso||0)||0)-(Date.parse(a.data_iso||0)||0));
  else if(_listaCfg.sort==='antigas') arr.sort((a,b)=>(Date.parse(a.data_iso||0)||0)-(Date.parse(b.data_iso||0)||0));
  else if(_listaCfg.sort==='confianca') arr.sort((a,b)=>(b.confianca_corr||0)-(a.confianca_corr||0));
  else if(_listaCfg.sort==='precisao') arr.sort((a,b)=>precScore(b.precisao)-precScore(a.precisao));

  // resumo de cobertura
  const total=newsCache.length;
  const comLocal=newsCache.filter(temLocal).length;
  const comRua=newsCache.filter(n=>n.precisao==='rua').length;
  const resumo=document.getElementById('sidebar-resumo');
  if(resumo){
    if(total){resumo.classList.add('show');
      resumo.textContent=`${comLocal} no mapa · ${comRua} com rua exata · ${total-comLocal} só cidade`;}
    else resumo.classList.remove('show');
  }

  if(!arr.length){
    list.innerHTML=`<div id="empty-state">🔎<p>${total?'Nenhuma notícia bate com o filtro.':'Aguardando notícias...'}</p></div>`;
    return;
  }
  list.innerHTML=arr.map(n=>renderCard(n)).join('');
  // marca visualmente as recém-chegadas
  _novosIds.forEach(id=>{const c=document.getElementById(`card-${id}`);if(c){c.classList.add('card-new');setTimeout(()=>c.classList.remove('card-new'),800);}});
  _novosIds.clear();
  if(selectedId){const c=document.getElementById(`card-${selectedId}`);if(c)c.classList.add('active');}
}

function onListaCfg(){
  _listaCfg.q=document.getElementById('lista-busca').value;
  _listaCfg.sort=document.getElementById('lista-sort').value;
  _salvarPrefs();
  aplicarLista();
}
function toggleSoMapa(){
  _listaCfg.soMapa=!_listaCfg.soMapa;
  document.getElementById('lista-mapa').classList.toggle('ativo',_listaCfg.soMapa);
  _salvarPrefs();
  aplicarLista();
}

// Ajusta o mapa para enquadrar todos os pins plotados
function ajustarATodos(){
  const pts=[];
  Object.values(markers).forEach(arr=>{if(Array.isArray(arr))arr.forEach(m=>pts.push(m.getLatLng()));});
  if(!pts.length){
    fetch(`${API}/api/geocode?q=${encodeURIComponent(cidade_atual)}&cidade=${encodeURIComponent(cidade_atual)}`)
      .then(r=>r.json()).then(g=>{if(g&&g.lat!=null)map.flyTo([g.lat,g.lon],12,{duration:1});}).catch(()=>{});
    return;
  }
  try{map.fitBounds(L.latLngBounds(pts),{padding:[60,60],maxZoom:15});}catch(e){}
}

function toggleLegenda(){
  const el=document.getElementById('map-legend');
  el.classList.toggle('collapsed');
  document.getElementById('leg-toggle').textContent=el.classList.contains('collapsed')?'▸':'▾';
}

// Contagem regressiva até a próxima busca automática
function atualizarCountdown(){
  const el=document.getElementById('proxima-busca'); if(!el)return;
  const sel=document.getElementById('intervalo-select');
  const intervalo=sel?parseInt(sel.value):0;
  if(!_ultimaBuscaTs||!intervalo){el.textContent='';return;}
  let resto=Math.round((_ultimaBuscaTs+intervalo*60000-Date.now())/1000);
  if(resto<0) resto=0;
  const mm=String(Math.floor(resto/60)).padStart(2,'0');
  const ss=String(resto%60).padStart(2,'0');
  el.textContent=`próxima em ${mm}:${ss}`;
}

// Persistência local de preferências (cidade/intervalo/filtro/lista/terminal/legenda)
function _salvarPrefs(){
  try{
    localStorage.setItem('arkadia_prefs', JSON.stringify({
      cidade: document.getElementById('cidade-input')?.value,
      intervalo: document.getElementById('intervalo-select')?.value,
      horas: document.getElementById('horas-select')?.value,
      lista: _listaCfg,
      legendaCollapsed: document.getElementById('map-legend')?.classList.contains('collapsed'),
    }));
  }catch(e){}
}
function _restaurarPrefs(){
  let p; try{p=JSON.parse(localStorage.getItem('arkadia_prefs')||'{}');}catch(e){p={};}
  if(!p)return;
  const set=(id,v)=>{const el=document.getElementById(id);if(el&&v!=null)el.value=v;};
  set('intervalo-select',p.intervalo); set('horas-select',p.horas);
  if(p.lista){_listaCfg={...{q:'',sort:'recentes',soMapa:false},...p.lista};
    set('lista-busca',_listaCfg.q); set('lista-sort',_listaCfg.sort);
    const bm=document.getElementById('lista-mapa');if(bm)bm.classList.toggle('ativo',!!_listaCfg.soMapa);}
  if(p.legendaCollapsed){const el=document.getElementById('map-legend');if(el){el.classList.add('collapsed');document.getElementById('leg-toggle').textContent='▸';}}
}

function selectCard(id){
  if(selectedId){const p=document.getElementById(`card-${selectedId}`);if(p)p.classList.remove('active');}
  selectedId=id;
  const card=document.getElementById(`card-${id}`);
  if(card){card.classList.add('active');card.scrollIntoView({behavior:'smooth',block:'nearest'});}
  const n=newsById[id];
  const bairros=n&&n.bairros&&n.bairros.length?n.bairros:null;
  if(bairros&&markers[id]&&markers[id][0]){
    // notícia com local: vai ao ponto e abre o popup
    _limparDestaqueCidade();
    const m0=markers[id][0];
    map.flyTo(m0.getLatLng(),15,{duration:1});
    m0.openPopup();
  } else {
    // só cidade: destaca a cidade inteira em vez de plotar um ponto
    destacarCidade();
  }
}

async function geocodificarCard(id){
  const n=newsById[id];if(!n)return;
  const btn=document.querySelector(`#card-${id} .btn-locate`);
  if(btn){btn.textContent='🔍 …';btn.disabled=true;}
  try{
    const res=await fetch(`${API}/api/geocode?q=${encodeURIComponent(n.titulo)}&cidade=${encodeURIComponent(cidade_atual)}`);
    const geo=await res.json();
    if(geo&&geo.bairros&&geo.bairros.length){
      newsById[id].bairros=geo.bairros;
      newsById[id].label=geo.bairros[0].nome;
      newsById[id].lat=geo.bairros[0].lat;
      newsById[id].lon=geo.bairros[0].lon;
      newsById[id].precisao='bairro';
      _limparDestaqueCidade();
      atualizarMarcador(newsById[id]);
      const m0=markers[id]&&markers[id][0];
      if(m0)map.flyTo(m0.getLatLng(),15,{duration:1.5});
      if(btn){btn.textContent=`🏘️ ${geo.bairros.length} bairro(s)`;setTimeout(()=>{btn.textContent='🔍 Localizar';btn.disabled=false;},2500);}
    } else {
      // sem bairro: não fixa ponto — destaca a cidade inteira
      destacarCidade();
      if(btn){btn.textContent='🏙️ Cidade';setTimeout(()=>{btn.textContent='🔍 Localizar';btn.disabled=false;},2500);}
    }
  }catch(e){if(btn)btn.textContent='🔍 Erro';setTimeout(()=>{if(btn){btn.textContent='🔍 Localizar';btn.disabled=false;}},2000);}
}

function togglePreview(id){ abrirMidia(id); }   // compat: agora abre a galeria/lightbox

async function aplicarConfig(){
  const cidade=document.getElementById('cidade-input').value.trim();
  const intervalo=parseInt(document.getElementById('intervalo-select').value);
  const horas=parseInt(document.getElementById('horas-select').value);
  if(!cidade)return;
  _salvarPrefs();
  const btn=document.getElementById('btn-aplicar');
  if(btn){btn.textContent='⏳ Aplicando…';btn.disabled=true;}
  try{
    const res=await fetch(`${API}/api/config`,{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({cidade,intervalo,horas_filtro:horas})});
    const data=await res.json();
    if(data.cidade&&data.cidade!==cidade_atual) limparEstadoLocal(data.cidade);
  }catch(e){console.error(e);}finally{if(btn){btn.textContent='Aplicar';btn.disabled=false;}}
}

function limparEstadoLocal(novaCidade){
  newsCache=[];newsById={};selectedId=null;
  Object.keys(openPreviews).forEach(k=>delete openPreviews[k]);
  Object.keys(_coordUso).forEach(k=>delete _coordUso[k]);
  _limparDestaqueCidade();
  document.getElementById('news-list').innerHTML=`<div id="empty-state">🔍<p>Buscando em <strong>${escHtml(novaCidade)}</strong>…</p></div>`;
  document.getElementById('count-badge').textContent='0 notícias';
  document.getElementById('last-update').textContent='—';
  Object.values(markers).forEach(arr=>{if(Array.isArray(arr))arr.forEach(m=>map.removeLayer(m));else map.removeLayer(arr);});markers={};
  if(novaCidade){
    cidade_atual=novaCidade;
    fetch(`${API}/api/geocode?q=${encodeURIComponent(novaCidade)}&cidade=${encodeURIComponent(novaCidade)}`)
      .then(r=>r.json()).then(geo=>{if(geo&&geo.lat!=null)map.flyTo([geo.lat,geo.lon],12,{duration:1.2});}).catch(()=>{});
  }
}

async function limpar(){
  try{await fetch(`${API}/api/limpar`,{method:'POST'});}catch(e){}
  limparEstadoLocal(cidade_atual);
  document.getElementById('news-list').innerHTML='<div id="empty-state">🗑️<p>Lista limpa.</p></div>';
}

let sseReconnectDelay=2000;
function conectarSSE(){
  const es=new EventSource(`${API}/api/stream`);
  es.addEventListener('snapshot',e=>{
    const data=JSON.parse(e.data);cidade_atual=data.cidade||'';
    (data.noticias||[]).forEach(n=>_marcarPrincipal(n.bairros));
    data.noticias.forEach(n=>{if(!newsById[n.id]){newsById[n.id]=n;}});
    renderTudo(data);sseReconnectDelay=2000;
  });
  es.addEventListener('noticia',e=>{
    const n=JSON.parse(e.data);if(newsById[n.id])return;
    _marcarPrincipal(n.bairros);
    newsById[n.id]=n;newsCache.unshift(n);
    _novosIds.add(n.id);
    const empty=document.getElementById('empty-state');if(empty)empty.remove();
    adicionarMarcador(n);
    aplicarLista();
    document.getElementById('count-badge').textContent=`${newsCache.length} notícia${newsCache.length!==1?'s':''}`;
  });
  es.addEventListener('limpar',e=>{const d=JSON.parse(e.data);limparEstadoLocal(d.cidade||cidade_atual);});
  es.addEventListener('geo_update',e=>{
    const u=JSON.parse(e.data);if(!newsById[u.id])return;
    if(u.bairros&&u.bairros.length){
      _marcarPrincipal(u.bairros);
      newsById[u.id].bairros=u.bairros;
      newsById[u.id].lat=u.bairros[0].lat;newsById[u.id].lon=u.bairros[0].lon;
      newsById[u.id].label=u.label||u.bairros[0].nome;
    } else {
      newsById[u.id].lat=u.lat;newsById[u.id].lon=u.lon;newsById[u.id].label=u.label;
    }
    newsById[u.id].precisao=u.precisao;newsById[u.id].geo_refinado=true;
    if(u.geo_score!=null)newsById[u.id].geo_score=u.geo_score;
    // mantém as estatísticas coerentes com o pino após o refino
    const _n=newsById[u.id];
    if(!_n.estatisticas) _n.estatisticas={};
    _n.estatisticas.local=_n.label;
    _n.estatisticas.precisao=_n.precisao;
    const _ruaUpdate=(u.bairros&&u.bairros[0]&&u.bairros[0].rua)||u.rua||null;
    if(_ruaUpdate){ _n.rua=_ruaUpdate; _n.estatisticas.rua=_ruaUpdate; }
    atualizarMarcador(newsById[u.id]);

    // atualizar bairros no card
    if(u.bairros&&u.bairros.length){
      const bairrosDiv=document.querySelector(`#card-${u.id} .bairros-encontrados`)||document.querySelector(`#card-${u.id} .bairros-sem`);
      if(bairrosDiv){
        const nomes=u.bairros.map(bairroChip).join('');
        bairrosDiv.className='bairros-encontrados';
        bairrosDiv.innerHTML=nomes;
      }
    }
    // se a visão depende do local (filtro "só no mapa" ou ordenação por precisão), re-renderiza
    if(_listaCfg.soMapa || _listaCfg.sort==='precisao') aplicarLista();
  });
  es.addEventListener('geo_progresso',e=>{
    const d=JSON.parse(e.data);const el=document.getElementById('geo-refinando');if(!el)return;
    if(d.processando){el.className='ativo';el.textContent=d.fila>0?`refinando geo… (${d.fila} na fila)`:'refinando geo…';}
    else{el.className='';el.textContent='refinando geo…';}
  });
  es.addEventListener('corpos_progresso',e=>{
    const d=JSON.parse(e.data);const dot=document.getElementById('dot');const st=document.getElementById('status-text');
    if(d.lendo){if(dot)dot.className='dot loading';if(st)st.textContent=`lendo corpos ${d.feitos}/${d.total}…`;}
  });
  es.addEventListener('buscando',e=>{
    const d=JSON.parse(e.data);const dot=document.getElementById('dot');
    if(d.buscando){dot.className='dot loading';document.getElementById('status-text').textContent=d.cidade?`buscando ${d.cidade}…`:'buscando…';}
    else{dot.className='dot';if(d.ultima_busca){document.getElementById('last-update').textContent=`Atualizado ${d.ultima_busca.slice(11)}`;_ultimaBuscaTs=_parseDataBR(d.ultima_busca);atualizarCountdown();}
      if(d.total_visto!=null)document.getElementById('status-text').textContent=`${d.total_visto} vistas | ${d.cidade||cidade_atual}`;
      if(d.cidade)cidade_atual=d.cidade;}
  });
  es.onerror=()=>{es.close();document.getElementById('dot').className='dot off';document.getElementById('status-text').textContent='reconectando…';setTimeout(conectarSSE,sseReconnectDelay);sseReconnectDelay=Math.min(sseReconnectDelay*2,30000);};
  es.addEventListener('log_snapshot',e=>{const d=JSON.parse(e.data);(d.logs||[]).forEach(l=>_termAppend(l));});
  es.addEventListener('log',e=>{const d=JSON.parse(e.data);_termAppend(d);});
}

const _termLogs=[];let _termFilter='ALL',_termOpen=false;
const _termLevelIcons={INFO:'ℹ️ INFO',OK:'✅ OK',WARN:'⚠️  WARN',ERR:'✗  ERR',GEO:'📍 GEO',SCRAPE:'🌐 SCRP',SEARCH:'🔍 SRCH'};
function _termLine(log){
  const div=document.createElement('div');div.className='term-line term-new';div.dataset.level=log.level;
  div.innerHTML=`<span class="term-ts">${escHtml(log.ts)}</span><span class="term-lvl">${escHtml(_termLevelIcons[log.level]||log.level)}</span><span class="term-msg">${escHtml(log.msg)}</span>`;
  setTimeout(()=>div.classList.remove('term-new'),450);return div;
}
function _termMatchFilter(log){return _termFilter==='ALL'||log.level===_termFilter;}
function _termAppend(log){
  _termLogs.push(log);if(_termLogs.length>500)_termLogs.shift();
  const termDot=document.getElementById('term-dot');
  const lastMsg=document.getElementById('terminal-last-msg');
  const countEl=document.getElementById('terminal-count');
  if(termDot){termDot.style.background=log.level==='ERR'?'#ef4444':log.level==='WARN'?'#f59e0b':'#22c55e';}
  if(lastMsg)lastMsg.textContent=`[${log.ts}] ${log.msg.slice(0,80)}`;
  if(countEl)countEl.textContent=`${_termLogs.length} linhas`;
  if(!_termOpen)return;if(!_termMatchFilter(log))return;
  const out=document.getElementById('terminal-output');if(!out)return;
  out.appendChild(_termLine(log));
  const auto=document.getElementById('term-autoscroll');if(!auto||auto.checked)out.scrollTop=out.scrollHeight;
  while(out.children.length>300)out.removeChild(out.firstChild);
}
function _termRedraw(){
  const out=document.getElementById('terminal-output');if(!out)return;
  out.innerHTML='';const frag=document.createDocumentFragment();
  _termLogs.filter(_termMatchFilter).forEach(l=>frag.appendChild(_termLine(l)));
  out.appendChild(frag);out.scrollTop=out.scrollHeight;
}
function toggleTerminal(){
  const panel=document.getElementById('terminal-panel');const label=document.getElementById('terminal-label');
  _termOpen=!_termOpen;
  if(_termOpen){panel.classList.add('open');if(label)label.textContent='▼ Terminal';_termRedraw();}
  else{panel.classList.remove('open');if(label)label.textContent='▶ Terminal';}
}
function termClear(){_termLogs.length=0;const out=document.getElementById('terminal-output');if(out)out.innerHTML='';const c=document.getElementById('terminal-count');if(c)c.textContent='0 linhas';}
document.addEventListener('DOMContentLoaded',()=>{
  document.querySelectorAll('.term-filter-btn').forEach(btn=>{
    btn.addEventListener('click',e=>{
      e.stopPropagation();
      document.querySelectorAll('.term-filter-btn').forEach(b=>b.classList.remove('active'));
      btn.classList.add('active');_termFilter=btn.dataset.level;if(_termOpen)_termRedraw();
    });
  });
  _restaurarPrefs();
});
conectarSSE();
setInterval(atualizarTemposRelativos, 60000);
setInterval(atualizarCountdown, 1000);
</script>
</body>
</html>"""

# ─────────────────────────────────────────────
#  MAIN
# ─────────────────────────────────────────────
def open_when_ready():
    import urllib.request as _ur
    print("⏳ Aguardando servidor iniciar...")
    for _ in range(50):
        try:
            _ur.urlopen(f"http://localhost:{PORT}/api/health", timeout=1)
            print(f"✅ Servidor online! Abrindo Arkadia em http://localhost:{PORT}")
            webbrowser.open(f"http://localhost:{PORT}")
            return
        except Exception:
            time.sleep(0.5)
    print(f"⚠️  Servidor não respondeu. Abra: http://localhost:{PORT}")

def main():
    print("=" * 57)
    print("  Arkadia v4 – Monitor de Notícias com PNL + geo_brasil")
    print("=" * 57)
    print(f"  Base geográfica: {len(GEO_ESTADOS)} estados | {len(GEO_CIDADES)} cidades | {len(GEO_BAIRROS)} bairros")
    print("=" * 57)

    cidade = input("📍 Cidade a monitorar (Enter = Guarapari): ").strip()
    if cidade:
        estado["cidade"] = cidade

    intervalo_input = input(f"⏰ Intervalo em minutos (Enter = {DEFAULT_INTERVALO}): ").strip()
    if intervalo_input.isdigit():
        estado["intervalo"] = max(1, int(intervalo_input))

    horas_input = input(f"🕐 Filtrar últimas N horas (Enter = {DEFAULT_HORAS_FILTRO}): ").strip()
    if horas_input.isdigit():
        estado["horas_filtro"] = max(1, min(2160, int(horas_input)))

    print(f"\n✅ Monitorando '{estado['cidade']}' a cada {estado['intervalo']} min | filtro {estado['horas_filtro']}h")
    if not _DEPS_OK:
        print("⚠️  Scraping desativado (instale requests + beautifulsoup4)")
    print("   Pressione Ctrl+C para parar.\n")

    threading.Thread(target=open_when_ready, daemon=True).start()
    threading.Thread(target=ciclo_busca, daemon=True).start()
    threading.Thread(target=_worker_geo_refinamento, daemon=True).start()
    threading.Thread(target=_worker_coord_precisa, daemon=True).start()
    threading.Thread(target=_worker_media_prefetch, daemon=True).start()
    app.run(host="0.0.0.0", port=PORT, debug=False, use_reloader=False)

if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\n\n🛑 Arkadia encerrado.")
        print(f"📊 Total de notícias vistas: {estado['total_visto']}")
        print("👋 Até logo!")