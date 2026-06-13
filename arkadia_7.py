"""
Arkadia v3 – Monitor de Notícias com Mapa ao Vivo
Servidor local + mapa interativo com geocodificação de ruas,
pré-visualização de mídia e fixação manual de marcadores.

Novidades v3:
  - Filtro de até 3 meses (90 dias) de histórico
  - Leitura do corpo da notícia para geocodificação de rua com precisão máxima
  - Thread de refinamento de geocodificação em segundo plano
  - Sistema avançado de correlação de fatos (entidades, evento, local, tempo)
  - Score de confiança e razões para agrupamentos multi-fonte
  - Badge de confiança na correlação de fontes

Dependências:
    pip install feedparser flask flask-cors requests beautifulsoup4

Uso:
    python arkadia_3.py
"""

import feedparser
import threading
import time
import re
import hashlib
import webbrowser
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
    print("   (Scraping de mídia e Nominatim desativados)\n")

# ─────────────────────────────────────────────
#  CONFIGURAÇÃO
# ─────────────────────────────────────────────
DEFAULT_CIDADE       = "Guarapari"
DEFAULT_INTERVALO    = 5
DEFAULT_HORAS_FILTRO = 24          # padrão 24h (opções vão até 2160h = 90 dias)
SIMILARIDADE_MINIMA  = 0.55        # limiar base (complementado por entidades)
PORT                 = 5050

# Pesos para o score de correlação avançado
PESO_SEQ     = 0.40   # similaridade sequencial (SequenceMatcher)
PESO_JACCARD = 0.30   # Jaccard sobre palavras-chave
PESO_EVENTO  = 0.15   # mesmo tipo de evento
PESO_LOCAL   = 0.15   # mesmo local identificado

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
    "busca_imediata": False,   # True = próxima iteração não espera o intervalo
}
lock = threading.Lock()

# Fila de refinamento de geocodificação (itens = dicts com id+url)
_geo_refine_queue  = []
_geo_refine_lock   = threading.Lock()

# ─────────────────────────────────────────────
#  DICIONÁRIO DE BAIRROS E LOCALIDADES (ES e região)
# ─────────────────────────────────────────────
BAIRROS_COORDS = {
    # ── Guarapari – bairros urbanos centrais ────────────────────────────────
    "centro":                    (-20.6717, -40.5085),
    "muquiçaba":                 (-20.6658, -40.5055),
    "praia do morro":            (-20.6602, -40.5018),
    "praia da areia preta":      (-20.6757, -40.5128),
    "praia das castanheiras":    (-20.6730, -40.5095),
    "praia do rádio":            (-20.6695, -40.5110),
    "praia do tomé":             (-20.6740, -40.5130),
    "praia do riacho":           (-20.6640, -40.5010),
    "nova guarapari":            (-20.6583, -40.4980),
    "enseada azul":              (-20.6530, -40.4940),
    "perocão":                   (-20.6570, -40.4960),
    "portal":                    (-20.6610, -40.5000),
    "santa mônica":              (-20.6790, -40.5160),
    "pontal de santa mônica":    (-20.6850, -40.5200),
    "village da praia":          (-20.6560, -40.4970),
    "recanto da sereia":         (-20.6510, -40.4920),
    "condados":                  (-20.6490, -40.4900),
    # ── Guarapari – bairros no mapa (visíveis na screenshot) ────────────────
    "kubitschek":                (-20.6840, -40.5250),
    "ipiranga":                  (-20.6870, -40.5280),
    "santa margarida":           (-20.6900, -40.5310),
    "são judas tadeu":           (-20.6800, -40.5200),
    "coroado":                   (-20.6780, -40.5380),
    "olaria":                    (-20.6760, -40.5340),
    "lagoa funda":               (-20.6650, -40.5280),
    "sol nascente":              (-20.6620, -40.5250),
    "são gabriel":               (-20.6480, -40.5310),
    "são josé":                  (-20.6520, -40.5290),
    "adalberto simão nader":     (-20.6430, -40.5200),
    "jardim boa vista":          (-20.6390, -40.5180),
    "bela vista":                (-20.6410, -40.5160),
    "camurugi":                  (-20.6700, -40.5400),
    "fátima cidade jardim":      (-20.6730, -40.5370),
    "elza nader":                (-20.6460, -40.5140),
    # ── Guarapari – bairros rurais / comunidades ─────────────────────────────
    "jaboticaba":                (-20.7050, -40.5600),
    "lameirão":                  (-20.7100, -40.5650),
    "itapebussu":                (-20.7200, -40.5700),
    "porto grande":              (-20.7300, -40.5750),
    "paturá":                    (-20.7400, -40.5800),
    "una":                       (-20.7500, -40.5900),
    "concha d'ostra":            (-20.7800, -40.6100),
    "bacutia":                   (-20.6820, -40.5480),
    "jardim santa rosa":         (-20.6860, -40.5460),
    "peracanga":                 (-20.6950, -40.5500),
    # ── Guarapari – praias ao sul ─────────────────────────────────────────────
    "meaípe":                    (-20.7050, -40.5350),
    "setiba":                    (-20.7200, -40.5500),
    "aldeia":                    (-20.7350, -40.5620),
    "parque de jacaraípe":       (-20.7400, -40.5640),
    # Vila Velha
    "itapuã": (-20.3333, -40.2833),
    "praia da costa": (-20.3300, -40.2800),
    "barra do jucu": (-20.3500, -40.2900),
    "coqueiral de itaparica": (-20.3400, -40.2850),
    "ibes": (-20.3550, -40.3000),
    # Vitória
    "camburi": (-20.3000, -40.3000),
    "praia do canto": (-20.3050, -40.3050),
    "curva da jurema": (-20.3100, -40.3100),
    "jardim da penha": (-20.3150, -40.3150),
    "mata da praia": (-20.3080, -40.3080),
    "ilha do boi": (-20.3020, -40.3020),
    "ilha do frade": (-20.3040, -40.3040),
    "santa lucia": (-20.3200, -40.3200),
    # Serra
    "manguinhos": (-20.1500, -40.2500),
    "bicanga": (-20.1550, -40.2550),
    "jacaraípe": (-20.1600, -40.2600),
    "nova almeida": (-20.1700, -40.2700),
    # Cariacica
    "campo grande": (-20.2667, -40.4167),
    "itacibá": (-20.2700, -40.4200),
    "jardim américa": (-20.2750, -40.4250),
    # Aracruz
    "barra do sahy": (-19.8000, -40.2000),
    "coqueiral": (-19.8100, -40.2100),
    "praia de parati": (-19.8200, -40.2200),
    # Linhares
    "pontal do ipiranga": (-19.4000, -40.0500),
    "barra seca": (-19.4100, -40.0600),
    "regência": (-19.4200, -40.0700),
    # Anchieta
    "praia do castelhanos": (-20.7800, -40.6400),
    "irií": (-20.7900, -40.6500),
    # Piúma
    "praia do litorâneo": (-20.8333, -40.7333),
    "pontal": (-20.8400, -40.7400),
}

ESTADOS_COORDS = {
    "AC": (-9.02,  -70.81), "AL": (-9.57,  -36.78), "AM": (-3.47,  -65.10),
    "AP": ( 1.41,  -51.77), "BA": (-12.97, -38.51), "CE": (-5.49,  -39.32),
    "DF": (-15.78, -47.93), "ES": (-19.19, -40.34), "GO": (-15.93, -49.79),
    "MA": (-5.42,  -45.44), "MG": (-18.10, -44.38), "MS": (-20.51, -54.54),
    "MT": (-12.64, -55.42), "PA": (-3.42,  -52.29), "PB": (-7.24,  -36.78),
    "PE": (-8.38,  -37.86), "PI": (-7.72,  -42.73), "PR": (-24.89, -51.55),
    "RJ": (-22.91, -43.17), "RN": (-5.81,  -36.59), "RO": (-11.22, -62.80),
    "RR": ( 1.99,  -61.33), "RS": (-30.03, -51.22), "SC": (-27.45, -50.95),
    "SE": (-10.57, -37.45), "SP": (-22.25, -48.63), "TO": (-10.25, -48.25),
}

CIDADES_COORDS = {
    # ES
    "guarapari":               (-20.67, -40.51),
    "vitória":                 (-20.31, -40.31),
    "vila velha":              (-20.33, -40.29),
    "cariacica":               (-20.27, -40.42),
    "serra":                   (-20.13, -40.31),
    "cachoeiro de itapemirim": (-20.85, -41.11),
    "linhares":                (-19.39, -40.07),
    "colatina":                (-19.54, -40.63),
    "são mateus":              (-18.72, -39.86),
    "aracruz":                 (-19.82, -40.27),
    "anchieta":                (-20.80, -40.64),
    "piúma":                   (-20.83, -40.73),
    "marataízes":              (-21.04, -40.83),
    "presidente kennedy":      (-21.10, -41.05),
    "itapemirim":              (-21.01, -40.83),
    "iconha":                  (-20.79, -40.81),
    "rio novo do sul":         (-20.87, -40.94),
    "alfredo chaves":          (-20.63, -40.75),
    "fundão":                  (-19.93, -40.41),
    "ibiraçu":                 (-19.83, -40.37),
    # RJ
    "rio de janeiro":          (-22.90, -43.17),
    "niterói":                 (-22.88, -43.10),
    "angra dos reis":          (-23.00, -44.32),
    "paraty":                  (-23.22, -44.71),
    "petrópolis":              (-22.51, -43.18),
    "volta redonda":           (-22.52, -44.10),
    "campos dos goytacazes":   (-21.76, -41.33),
    "macaé":                   (-22.37, -41.79),
    # SP
    "são paulo":               (-23.55, -46.63),
    "campinas":                (-22.91, -47.06),
    "santos":                  (-23.96, -46.33),
    "guarulhos":               (-23.46, -46.53),
    "sorocaba":                (-23.50, -47.46),
    "ribeirão preto":          (-21.17, -47.81),
    "são josé dos campos":     (-23.18, -45.88),
    # MG
    "belo horizonte":          (-19.92, -43.94),
    "uberlândia":              (-18.92, -48.28),
    "contagem":                (-19.93, -44.05),
    "juiz de fora":            (-21.76, -43.35),
    "montes claros":           (-16.73, -43.86),
    # BA
    "salvador":                (-12.97, -38.50),
    "feira de santana":        (-12.25, -38.97),
    "ilhéus":                  (-14.79, -39.05),
    "porto seguro":            (-16.44, -39.06),
    # PE
    "recife":                  (-8.06,  -34.88),
    "olinda":                  (-8.01,  -34.86),
    "caruaru":                 (-8.28,  -35.97),
    "petrolina":               (-9.39,  -40.50),
    # CE
    "fortaleza":               (-3.72,  -38.54),
    "juazeiro do norte":       (-7.21,  -39.32),
    "caucaia":                 (-3.74,  -38.66),
}

def normalizar(texto):
    import unicodedata
    return unicodedata.normalize("NFD", str(texto).lower()).encode("ascii", "ignore").decode()

# ─────────────────────────────────────────────
#  EXTRAÇÃO MELHORADA DE LOCALIZAÇÃO
# ─────────────────────────────────────────────
def extrair_local_melhorado(titulo):
    """
    Extrai menção de localização (rua, bairro, cidade, ponto de referência) do título.
    Prioridade: logradouro explícito > bairro conhecido > cidade > padrão preposicional.

    Melhorias:
    - Detecta padrões "em <Cidade> (<UF>)" sem retornar a sigla UF como local
    - Captura logradouros com número (ex: "Av. Beira Mar, 230")
    - Descarta falsos positivos curtos e palavras de parada comuns
    """
    titulo_lower = titulo.lower()

    # ── 1. Bairro conhecido no dicionário ───────────────────────────────
    for bairro in sorted(BAIRROS_COORDS.keys(), key=len, reverse=True):
        if bairro in titulo_lower:
            return bairro

    # ── 2. Logradouro explícito ──────────────────────
    # Mesmas regras: formas longas no texto lower; r./av. exigem maiúscula.
    _PR_T_L = [
        '\\brua\\s+[\\w][\\w\\s]{3,40}?(?=\\s*(?:,|;|\\. |\\. *\\n|\\u2013|-|\\d|\\s+(?:deixa|mata|\\u00e9|foi|fica|causa|com\\s|em\\s|no\\s|na\\s|do\\s|da\\s|pelo\\s|para\\s|ap\\u00f3s\\s|entre\\s)|$))',
        '\\bavenida\\s+[\\w][\\w\\s]{3,40}?(?=\\s*(?:,|;|\\. |\\. *\\n|\\u2013|-|\\d|\\s+(?:deixa|mata|\\u00e9|foi|fica|causa|com\\s|em\\s|no\\s|na\\s|do\\s|da\\s|pelo\\s|para\\s|ap\\u00f3s\\s|entre\\s)|$))',
        '\\btravessa\\s+[\\w][\\w\\s]{3,35}?(?=\\s*(?:,|;|\\. |\\. *\\n|\\u2013|-|\\d|\\s+(?:deixa|mata|\\u00e9|foi|fica|causa|com\\s|em\\s|no\\s|na\\s|do\\s|da\\s|pelo\\s|para\\s|ap\\u00f3s\\s|entre\\s)|$))',
        '\\bpraça\\s+[\\w][\\w\\s]{3,35}?(?=\\s*(?:,|;|\\. |\\. *\\n|\\u2013|-|\\d|\\s+(?:deixa|mata|\\u00e9|foi|fica|causa|com\\s|em\\s|no\\s|na\\s|do\\s|da\\s|pelo\\s|para\\s|ap\\u00f3s\\s|entre\\s)|$))',
        '\\balameda\\s+[\\w][\\w\\s]{3,35}?(?=\\s*(?:,|;|\\. |\\. *\\n|\\u2013|-|\\d|\\s+(?:deixa|mata|\\u00e9|foi|fica|causa|com\\s|em\\s|no\\s|na\\s|do\\s|da\\s|pelo\\s|para\\s|ap\\u00f3s\\s|entre\\s)|$))',
        '\\b(?:estrada|rodovia)\\s+[\\w][\\w\\s\\-]{3,40}?(?=\\s*(?:,|;|\\. |\\. *\\n|\\u2013|-|\\d|\\s+(?:deixa|mata|\\u00e9|foi|fica|causa|com\\s|em\\s|no\\s|na\\s|do\\s|da\\s|pelo\\s|para\\s|ap\\u00f3s\\s|entre\\s)|$))',
        '\\b(?:br|es)[-\\s]?\\d{2,3}\\b',
    ]
    _PR_T_O = [
        '(?<!\\w)r\\. [A-Z\\u00c0-\\u00da][\\w\\s]{4,40}?(?=\\s*(?:,|;|\\. |\\. *\\n|\\u2013|-|\\d|\\s+(?:deixa|mata|\\u00e9|foi|fica|causa|com\\s|em\\s|no\\s|na\\s|do\\s|da\\s|pelo\\s|para\\s|ap\\u00f3s\\s|entre\\s)|$))',
        '(?<!\\w)[Aa][Vv]\\. [A-Z\\u00c0-\\u00da][\\w\\s]{3,35}?(?=\\s*(?:,|;|\\. |\\. *\\n|\\u2013|-|\\d|\\s+(?:deixa|mata|\\u00e9|foi|fica|causa|com\\s|em\\s|no\\s|na\\s|do\\s|da\\s|pelo\\s|para\\s|ap\\u00f3s\\s|entre\\s)|$))',
        '(?<!\\w)R\\. [A-Z\\u00c0-\\u00da][\\w\\s]{3,35}?(?=\\s*(?:,|;|\\. |\\. *\\n|\\u2013|-|\\d|\\s+(?:deixa|mata|\\u00e9|foi|fica|causa|com\\s|em\\s|no\\s|na\\s|do\\s|da\\s|pelo\\s|para\\s|ap\\u00f3s\\s|entre\\s)|$))',
    ]
    for padrao in _PR_T_L:
        m = re.search(padrao, titulo_lower)
        if m:
            trecho = m.group(0).strip()
            trecho = re.sub(r'\s+(?:no|na|em|de|do|da)\s*$', '', trecho).strip()
            if len(trecho) > 5:
                return trecho
    for padrao in _PR_T_O:
        m = re.search(padrao, titulo)
        if m:
            trecho = m.group(0).strip().lower()
            trecho = re.sub(r'\s+(?:no|na|em|de|do|da)\s*$', '', trecho).strip()
            if len(trecho) > 5:
                return trecho
    # ── 3. Cidade mencionada explicitamente ─────────────────────────────
    cidades_encontradas = []
    for cidade in sorted(CIDADES_COORDS.keys(), key=len, reverse=True):
        if normalizar(cidade) in normalizar(titulo):
            cidades_encontradas.append(cidade)
    if cidades_encontradas:
        return cidades_encontradas[0]

    # ── 4. Padrão "em <Local>" / "no <Local>" / "na <Local>" ────────────
    #    Ignora se o "local" capturado for apenas uma sigla de estado (ES, RJ…)
    #    ou uma abreviatura muito curta.
    _STOPS_LOCAL = {
        'es','rj','sp','mg','ba','pr','sc','rs','ce','pe','go','df','am','pa',
        'tv','km','br','trânsito','vítima','suspeito','polícia','bombeiros',
        'acidente','incêndio','morte','morto','preso','crime',
    }
    padrao_prep = re.compile(
        r'(?:^|[\s,])(?:no|na|em|pelo|pela)\s+([A-ZÀ-Ú][a-zà-ú]+(?:\s+[A-ZÀ-Úa-zà-ú]+){0,4})',
        re.UNICODE,
    )
    for m in padrao_prep.finditer(titulo):
        local = m.group(1).strip()
        local_n = normalizar(local)
        if len(local_n) <= 2 or local_n in _STOPS_LOCAL:
            continue
        # Ignora se termina com sigla de estado entre parênteses
        if re.fullmatch(r'[a-z]{2,}', local_n) and len(local_n) == 2:
            continue
        if len(local) > 3:
            return local

    return None

def geocodificar_offline_melhorado(texto):
    """Geocodificação por dicionário com prioridade para bairros.
    
    CORREÇÃO: O regex anterior r'\\b([A-Z]{2})\\b' capturava qualquer sigla de
    duas letras maiúsculas — inclusive a sigla de estado entre parênteses que
    aparece em títulos de notícias como "...em Guarapari (ES)...". Isso fazia
    todas as notícias de Guarapari serem plotadas no centróide do ES em vez da
    cidade correta. Agora o estado só é usado quando NÃO há cidade/bairro
    detectado, e somente se a sigla vier literalmente entre parênteses.
    """
    if not texto:
        return None
    
    t = normalizar(texto)
    
    # Primeiro: verifica se é um bairro conhecido
    for bairro, coords in BAIRROS_COORDS.items():
        if normalizar(bairro) in t or bairro.replace(' ', '') in t.replace(' ', ''):
            return {"lat": coords[0], "lon": coords[1],
                    "label": bairro.title(), "precisao": "bairro"}
    
    # Segundo: verifica se é uma cidade conhecida
    for cidade, coords in CIDADES_COORDS.items():
        if normalizar(cidade) in t:
            return {"lat": coords[0], "lon": coords[1],
                    "label": cidade.title(), "precisao": "cidade"}
    
    # Terceiro: estado — SOMENTE se a sigla vier entre parênteses, ex: "(ES)".
    # Isso evita que abreviaturas comuns (TV, ES no meio de uma frase, etc.)
    # disparem um falso positivo estadual que desloca o pino para longe do local real.
    uf = re.search(r'\(([A-Z]{2})\)', texto)
    if uf and uf.group(1) in ESTADOS_COORDS:
        code = uf.group(1)
        lat, lon = ESTADOS_COORDS[code]
        return {"lat": round(lat, 4), "lon": round(lon, 4),
                "label": code, "precisao": "estado"}
    return None

# ─────────────────────────────────────────────
#  PADRÕES DE LOGRADOURO CENTRALIZADOS
#  Usados por geocodificar_inteligente E _extrair_local_do_corpo.
#  Regra: logradouro real → nome próprio com maiúscula logo após o tipo.
#  "r. a doença" ou "rua onde mora" → rejeitados pela stop-word check.
# ─────────────────────────────────────────────
_GEO_STOP_NOMES = {
    'a','o','e','os','as','um','uma','uns','umas',
    'de','da','do','das','dos','em','na','no','nas','nos',
    'por','para','com','sem','sob','sobre','entre','após',
    'segundo','conforme','porque','quando','onde','como',
    'que','se','já','ainda','também','mas','pois','então',
    'foi','era','são','está','há','teve','tem','vai','vem',
    'isso','isto','aqui','ali','lá','hoje','ontem',
}
_NP = r'(?:(?:d[aeo]s?\s+)?[A-ZÀ-Ú]\w{1,}(?:\s+(?:d[aeo]s?\s+)?[A-ZÀ-Úa-zà-ú]\w{0,}){0,5})'
_PAD_LOGRADOURO_GEO = [
    rf'\b[Rr]ua\s+{_NP}',
    rf'\b[Aa]venida\s+{_NP}',
    rf'\b[Tt]ravessa\s+{_NP}',
    rf'\b[Pp]raça\s+{_NP}',
    rf'\b[Aa]lameda\s+{_NP}',
    rf'\b[Ee]strada\s+{_NP}',
    rf'\b[Rr]odovia\s+{_NP}',
    r'(?<!\w)[Rr]\.\s+[A-ZÀ-Ú]\w[\w\s]{3,35}',
    r'(?<!\w)[Aa][Vv]\.\s+[A-ZÀ-Ú]\w[\w\s]{2,35}',
    r'\b(?:[Bb][Rr]|[Ee][Ss])[-\s]?\d{2,3}\b',
]

# ─────────────────────────────────────────────
#  GEOCODIFICAÇÃO NOMINATIM (online, precisão de rua)
# ─────────────────────────────────────────────
_geo_lock  = threading.Lock()
_geo_last  = 0.0
_geo_cache = {}

def geocodificar_nominatim(query):
    """Geocodificação online via Nominatim – limita a 1 req/s e usa cache."""
    global _geo_last
    if not _DEPS_OK:
        return None
    key = normalizar(query)
    if key in _geo_cache:
        return _geo_cache[key]
    with _geo_lock:
        elapsed = time.time() - _geo_last
        if elapsed < 1.1:
            time.sleep(1.1 - elapsed)
        try:
            r = _http.get(
                "https://nominatim.openstreetmap.org/search",
                params={"q": query, "format": "json", "limit": 1, "countrycodes": "br"},
                headers={"User-Agent": "Arkadia/1.0 (monitor-noticias-mapa)"},
                timeout=7,
            )
            _geo_last = time.time()
            data = r.json()
            if data:
                d = data[0]
                tp = d.get("type", "")
                # Classifica a precisão baseado no tipo OSM
                if tp in ("way", "node", "building", "road", "residential",
                         "secondary", "tertiary", "street", "address"):
                    precisao = "rua"
                elif tp in ("suburb", "quarter", "neighbourhood"):
                    precisao = "bairro"
                elif tp in ("city", "town", "village"):
                    precisao = "cidade"
                else:
                    precisao = "local"
                
                result = {
                    "lat":      float(d["lat"]),
                    "lon":      float(d["lon"]),
                    "label":    d.get("display_name", "").split(",")[0].strip(),
                    "precisao": precisao,
                }
                _geo_cache[key] = result
                return result
        except Exception as exc:
            print(f"  ✗ Nominatim: {exc}")
        _geo_cache[key] = None
        return None

def geocodificar_inteligente(titulo, cidade_monitorada):
    """
    Geocodificação conservadora: só afirma o que sabe com certeza.

    Regra de ouro: é melhor plotar na cidade certa do que numa rua errada.

    Pipeline:
      1. Logradouro explícito no título (Rua X / Av Y / Rodovia BR-xxx)
         → único caso em que Nominatim é chamado (com viewbox na cidade)
         → se Nominatim retornar algo fora da cidade monitorada, descarta
      2. Bairro no dicionário offline (match exato)
      3. Cidade mencionada no título (dicionário offline)
      4. Fallback: coordenadas da cidade monitorada (precisao="cidade")
         → toda notícia SEMPRE recebe um pino; nunca retorna None
    """

    # ── 0. Coordenadas base da cidade monitorada ──────────────────────────
    def _coords_cidade(nome):
        n = normalizar(nome)
        for c, xy in CIDADES_COORDS.items():
            if normalizar(c) in n or n in normalizar(c):
                return xy
        return None

    base = _coords_cidade(cidade_monitorada)
    if base is None:
        # Cidade não está no dicionário: tenta Nominatim uma única vez
        if _DEPS_OK:
            g = geocodificar_nominatim(f"{cidade_monitorada}, Brasil")
            base = (g["lat"], g["lon"]) if g else (-20.67, -40.51)
        else:
            base = (-20.67, -40.51)
    clat, clon = base

    FALLBACK_CIDADE = {
        "lat": clat, "lon": clon,
        "label": cidade_monitorada.title(),
        "precisao": "cidade",
    }

    # ── 1. Logradouro explícito → Nominatim com viewbox ──────────────────
    # Só usamos Nominatim quando há um logradouro no texto, porque aí a query
    # é específica o suficiente para ser confiável. Para qualquer outra coisa
    # (ex: "em Guarapari") o Nominatim devolve o centróide da cidade ou pior,
    # Reutiliza os padrões robustos centralizados _PAD_LOGRADOURO_GEO
    # (exigem nome próprio com maiúscula — evita falsos positivos como "r. a doença")
    logradouro = None
    for _pat in _PAD_LOGRADOURO_GEO:
        _m = re.search(_pat, titulo)        # texto ORIGINAL (preserva caixa)
        if _m:
            _tr = _m.group(0).strip()
            _partes = _tr.split(None, 1)
            _nome   = _partes[1].strip() if len(_partes) > 1 else _tr
            _nome_n = normalizar(_nome).split()[0] if _nome else ""
            if _nome_n in {'da', 'do', 'de', 'das', 'dos'}:
                _toks = normalizar(_nome).split()
                _nome_n = _toks[1] if len(_toks) > 1 else _nome_n
            if _nome_n in _GEO_STOP_NOMES:
                continue
            if len(_nome) >= 4:
                logradouro = _tr.lower()
                break


    if logradouro and _DEPS_OK:
        global _geo_last
        query = f"{logradouro}, {cidade_monitorada}, Brasil"
        key   = normalizar(query) + f"@{clat:.2f},{clon:.2f}"
        geo   = _geo_cache.get(key)
        if geo is None:           # não está em cache ainda
            with _geo_lock:
                elapsed = time.time() - _geo_last
                if elapsed < 1.1:
                    time.sleep(1.1 - elapsed)
                try:
                    dlon = 0.25
                    dlat = 0.25
                    r = _http.get(
                        "https://nominatim.openstreetmap.org/search",
                        params={
                            "q":           query,
                            "format":      "json",
                            "limit":       3,
                            "countrycodes":"br",
                            "viewbox":     f"{clon-dlon},{clat+dlat},{clon+dlon},{clat-dlat}",
                            "bounded":     0,
                        },
                        headers={"User-Agent": "Arkadia/1.0 (monitor-noticias-mapa)"},
                        timeout=7,
                    )
                    _geo_last = time.time()
                    results = r.json()
                    if results:
                        # Escolhe o resultado mais próximo ao centro da cidade
                        results.sort(
                            key=lambda d: (float(d["lat"]) - clat)**2
                                        + (float(d["lon"]) - clon)**2
                        )
                        d  = results[0]
                        tp = d.get("type", "")
                        cl = d.get("class", "")
                        if tp in ("way","node","building","road","residential",
                                  "secondary","tertiary","street","address") \
                           or cl in ("highway","building"):
                            precisao = "rua"
                        elif tp in ("suburb","quarter","neighbourhood"):
                            precisao = "bairro"
                        else:
                            precisao = "local"
                        geo = {
                            "lat":      float(d["lat"]),
                            "lon":      float(d["lon"]),
                            "label":    d.get("display_name","").split(",")[0].strip(),
                            "precisao": precisao,
                        }
                        # Valida: resultado deve estar dentro de ~30 km da cidade
                        dist_graus = ((geo["lat"]-clat)**2 + (geo["lon"]-clon)**2)**0.5
                        if dist_graus > 0.30:   # ~33 km — descarta se for longe demais
                            geo = None
                except Exception as exc:
                    print(f"  ✗ Nominatim (logradouro): {exc}")
                    geo = None
            _geo_cache[key] = geo  # guarda mesmo se None, para não repetir

        if geo:
            return geo
        # Nominatim falhou ou ficou longe → continua para dicionário offline

    # ── 2. Bairro no dicionário offline ──────────────────────────────────
    t = normalizar(titulo)
    for bairro in sorted(BAIRROS_COORDS.keys(), key=len, reverse=True):
        if normalizar(bairro) in t:
            lat, lon = BAIRROS_COORDS[bairro]
            return {"lat": lat, "lon": lon,
                    "label": bairro.title(), "precisao": "bairro"}

    # ── 3. Cidade mencionada no título ────────────────────────────────────
    for cidade in sorted(CIDADES_COORDS.keys(), key=len, reverse=True):
        if normalizar(cidade) in t:
            lat, lon = CIDADES_COORDS[cidade]
            return {"lat": lat, "lon": lon,
                    "label": cidade.title(), "precisao": "cidade"}

    # ── 4. Fallback: cidade monitorada ────────────────────────────────────
    return FALLBACK_CIDADE

# ─────────────────────────────────────────────
#  GEOCODIFICAÇÃO POR CORPO DA NOTÍCIA (v3)
# ─────────────────────────────────────────────

def _resolver_url_real(url):
    """
    Resolve redirecionamentos do Google News e similares para o URL real da notícia.
    Chamada antes de qualquer leitura de corpo de artigo.
    """
    if not _DEPS_OK:
        return url
    if "news.google.com" not in url:
        return url
    try:
        r = _http.get(url, timeout=8, headers={
            "User-Agent": (
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                "AppleWebKit/537.36 (KHTML, like Gecko) "
                "Chrome/124.0.0.0 Safari/537.36"
            ),
            "Accept-Language": "pt-BR,pt;q=0.9",
        }, allow_redirects=True)
        final = r.url
        if "news.google.com" not in final:
            return final
        soup2 = _bs4.BeautifulSoup(r.text, "html.parser")
        for tag, attr in [
            ("link",  {"rel": "canonical"}),
            ("meta",  {"property": "og:url"}),
        ]:
            el = soup2.find(tag, attr)
            if el:
                href = el.get("href") or el.get("content", "")
                if href and href.startswith("http") and "news.google.com" not in href:
                    return href
        for a in soup2.select("article a[href], .article a[href], h3 a[href]"):
            href = a.get("href", "")
            if href.startswith("http") and "news.google.com" not in href:
                return href
    except Exception:
        pass
    return url


def _extrair_texto_puro(url):
    """
    Baixa a página e extrai texto limpo do artigo.
    Resolve URLs do Google News antes de acessar.
    Retorna string com ~3000 chars do corpo, ou None em caso de falha.
    """
    if not _DEPS_OK:
        return None
    # Resolve URL real (Google News → portal original)
    url_real = _resolver_url_real(url)
    try:
        r = _http.get(url_real, timeout=10, headers={
            "User-Agent": (
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                "AppleWebKit/537.36 (KHTML, like Gecko) "
                "Chrome/124.0.0.0 Safari/537.36"
            ),
            "Accept-Language": "pt-BR,pt;q=0.9",
        })
        soup = _bs4.BeautifulSoup(r.text, "html.parser")

        # Remove scripts, estilos, navs
        for tag in soup(["script","style","nav","footer","header","aside"]):
            tag.decompose()

        # Prioriza parágrafos de artigo
        for sel in ["article p", ".article-body p", ".content p",
                    "main p", ".materia p", "p"]:
            paragrafos = soup.select(sel)
            if paragrafos:
                texto = " ".join(p.get_text(" ", strip=True) for p in paragrafos[:20])
                if len(texto) > 150:
                    return texto[:3000]

        return soup.get_text(" ", strip=True)[:3000]
    except Exception as exc:
        _log(f"Erro ao ler corpo ({url_real[:60]}): {exc}", "WARN")
        return None


def _extrair_local_do_corpo(corpo, cidade_monitorada):
    """
    Procura menções de localização ESPECÍFICA no corpo do artigo.
    Prioridade: logradouro > bairro > cruzamento/referência.
    Retorna (local_str, precisao) ou (None, None).
    """
    if not corpo:
        return None, None

    corpo_lower = corpo.lower()
    corpo_norm  = normalizar(corpo)

    # ── 1. Logradouro explícito (rua, av, rodovia…) ─────────────────────
    #
    # REGRA FUNDAMENTAL: um logradouro real sempre tem um NOME PRÓPRIO logo
    # após o tipo (Rua, Avenida…). Nome próprio = começa com letra maiúscula
    # e NÃO é uma palavra funcional comum (artigo, preposição, conjunção).
    #
    # Estratégia: rodar todos os padrões sobre o texto ORIGINAL (com caixa),
    # exigindo [A-ZÀ-Ú] imediatamente após o tipo de logradouro.
    # Assim "r. a doença não era novidade" e "r. segundo o presidente"
    # jamais passam — "a" e "segundo" não são maiúsculas.
    #
    # Palavras-bloqueio: mesmo que a palavra seguinte seja maiúscula por
    # estar no início de frase, descartamos se for uma stop-word comum.
    # Usa os padrões robustos globais _PAD_LOGRADOURO_GEO / _GEO_STOP_NOMES
    for _pat in _PAD_LOGRADOURO_GEO:
        _m = re.search(_pat, corpo)   # texto ORIGINAL (preserva caixa)
        if _m:
            _trecho = _m.group(0).strip()
            _partes = _trecho.split(None, 1)
            _nome   = _partes[1].strip() if len(_partes) > 1 else _trecho
            _nome_n = normalizar(_nome).split()[0] if _nome else ""
            if _nome_n in {'da', 'do', 'de', 'das', 'dos'}:
                _toks = normalizar(_nome).split()
                _nome_n = _toks[1] if len(_toks) > 1 else _nome_n
            if _nome_n in _GEO_STOP_NOMES:
                continue
            if len(_nome) >= 4:
                return _trecho.lower(), "rua"

    # ── 2. Bairro conhecido ───────────────────────────────────────────────
    for bairro in sorted(BAIRROS_COORDS.keys(), key=len, reverse=True):
        if normalizar(bairro) in corpo_norm:
            return bairro, "bairro"

    # ── 3. Menção explícita de bairro ("no bairro X", "bairro X") ───────────
    # Captura o nome após "bairro" e verifica no dicionário antes de chamar
    # Nominatim — evita falsos positivos e já retorna precisao="bairro".
    padrao_bairro_explicito = re.compile(
        r'(?:no bairro|na região do bairro|bairro)\s+([\w\s]{3,40})',
        re.IGNORECASE,
    )
    for m in padrao_bairro_explicito.finditer(corpo_lower):
        nome = m.group(1).strip().rstrip('.,;')
        nome_n = normalizar(nome)
        # Tenta match exato ou parcial no dicionário
        for bairro in sorted(BAIRROS_COORDS.keys(), key=len, reverse=True):
            if normalizar(bairro) in nome_n or nome_n in normalizar(bairro):
                return bairro, "bairro"
        # Não estava no dicionário mas é menção explícita → retorna como referência
        if len(nome) > 3:
            return nome, "referencia"

    # ── 4. "Próximo a / em frente ao / esquina com" ───────────────────────
    padroes_ref = [
        r'(?:próximo a|perto de|em frente a[o]?|em frente à|esquina com|altura d[ao])\s+([\w\s]{4,50})',
        r'(?:na região d[oa]|no centro d[oa])\s+([\w\s]{4,40})',
    ]
    for pat in padroes_ref:
        m = re.search(pat, corpo_lower)
        if m:
            ref = m.group(1).strip()
            if len(ref) > 3:
                return ref, "referencia"

    # ── 5. "às margens de" / "às margens da" (ex: "às margens de uma estrada no bairro X") ──
    m = re.search(r'às margens d[aeo]\s+[\w\s]{3,50}', corpo_lower)
    if m:
        trecho = m.group(0)
        # Tenta extrair bairro dentro do trecho
        for bairro in sorted(BAIRROS_COORDS.keys(), key=len, reverse=True):
            if normalizar(bairro) in normalizar(trecho):
                return bairro, "bairro"

    return None, None


def _extrair_local_por_ia(corpo, titulo, cidade):
    """
    Usa a API da Anthropic para interpretar o corpo da notícia e extrair
    o local exato do evento descrito. Chamada somente quando o parsing
    regex não encontrou um local preciso.
    Retorna (local_str, tipo) onde tipo é 'rua', 'bairro' ou 'referencia'.
    """
    if not _DEPS_OK:
        return None, None
    try:
        import json as _json
        import urllib.request as _ur
        import urllib.error

        prompt = (
            f"Título da notícia: {titulo}\n\n"
            f"Corpo da notícia:\n{corpo[:2000]}\n\n"
            f"Cidade monitorada: {cidade}\n\n"
            "Tarefa: identifique o LOCAL EXATO onde o evento descrito ocorreu. "
            "Retorne SOMENTE um objeto JSON com os campos:\n"
            '  "local": string com o nome do logradouro, bairro ou ponto de referência '
            '(ex: "Rua das Flores", "Bairro Adalberto Simão Nader", "Praça Central"), '
            'ou null se não houver local específico mencionado.\n'
            '  "tipo": "rua" se for logradouro explícito, "bairro" se for bairro/região, '
            '"referencia" se for ponto de referência, ou null.\n'
            '  "confianca": número de 0.0 a 1.0 indicando certeza.\n'
            "Não inclua texto fora do JSON. Responda SOMENTE o JSON."
        )

        payload = _json.dumps({
            "model": "claude-haiku-4-5-20251001",
            "max_tokens": 120,
            "messages": [{"role": "user", "content": prompt}],
        }).encode()

        req = _ur.Request(
            "https://api.anthropic.com/v1/messages",
            data=payload,
            headers={
                "Content-Type": "application/json",
                "anthropic-version": "2023-06-01",
            },
            method="POST",
        )
        with _ur.urlopen(req, timeout=12) as resp:
            data = _json.loads(resp.read())

        text = ""
        for block in data.get("content", []):
            if block.get("type") == "text":
                text += block.get("text", "")

        # Limpa possíveis backticks de markdown
        text = text.strip().lstrip("```json").lstrip("```").rstrip("```").strip()
        resultado = _json.loads(text)

        local = resultado.get("local")
        tipo  = resultado.get("tipo")
        conf  = float(resultado.get("confianca", 0.0))

        if local and tipo and conf >= 0.55:
            _log(f"IA-GEO [{tipo}] confiança {conf:.0%}: '{local[:60]}'", "GEO")
            return local, tipo

    except Exception as exc:
        _log(f"IA-GEO erro: {exc}", "WARN")

    return None, None


def geocodificar_com_corpo(titulo, url, cidade):
    """
    Geocodificação de dois estágios:
      1. Baixa corpo do artigo e extrai menção de local específico via regex
      2. Se regex falhar → usa IA (Haiku) para interpretar o texto
      3. Geocodifica o local via dicionário offline (bairro) ou Nominatim (rua/ref)
    Retorna dict com lat/lon/label/precisao ou None se não melhorou.
    """
    corpo = _extrair_texto_puro(url)
    if not corpo:
        return None

    # Tentativa 1: extração por regex
    local_str, tipo = _extrair_local_do_corpo(corpo, cidade)

    # Tentativa 2: se regex falhou, usa IA
    if not local_str:
        local_str, tipo = _extrair_local_por_ia(corpo, titulo, cidade)

    if not local_str:
        return None

    _log(f"GEO-CORPO [{tipo}] detectado: '{local_str[:50]}'", "GEO")

    if tipo == "bairro":
        # Busca no dicionário offline (match normalizado)
        local_n = normalizar(local_str)
        for bairro, coords in BAIRROS_COORDS.items():
            if normalizar(bairro) in local_n or local_n in normalizar(bairro):
                return {"lat": coords[0], "lon": coords[1],
                        "label": bairro.title(), "precisao": "bairro"}
        # Bairro não está no dicionário → tenta Nominatim
        if _DEPS_OK:
            tipo = "referencia"   # continua para Nominatim abaixo

    # Para logradouro ou referência → Nominatim com viewbox na cidade
    if tipo in ("rua", "referencia") and _DEPS_OK:
        # Obtém coordenadas base da cidade
        def _city_coords(nome):
            n = normalizar(nome)
            for c, xy in CIDADES_COORDS.items():
                if normalizar(c) in n or n in normalizar(c):
                    return xy
            return None

        base = _city_coords(cidade) or (-20.67, -40.51)
        clat, clon = base

        query = f"{local_str}, {cidade}, Brasil"
        key   = "corpo:" + normalizar(query)
        global _geo_last
        cached = _geo_cache.get(key)
        if cached is not None:
            return cached

        with _geo_lock:
            elapsed = time.time() - _geo_last
            if elapsed < 1.2:
                time.sleep(1.2 - elapsed)
            try:
                dlon, dlat = 0.30, 0.30
                resp = _http.get(
                    "https://nominatim.openstreetmap.org/search",
                    params={
                        "q":           query,
                        "format":      "json",
                        "limit":       5,
                        "countrycodes":"br",
                        "viewbox":     f"{clon-dlon},{clat+dlat},{clon+dlon},{clat-dlat}",
                        "bounded":     0,
                    },
                    headers={"User-Agent": "Arkadia/3.0 (monitor-noticias-mapa)"},
                    timeout=8,
                )
                _geo_last = time.time()
                results   = resp.json()
                if results:
                    results.sort(
                        key=lambda d: (float(d["lat"]) - clat)**2
                                    + (float(d["lon"]) - clon)**2
                    )
                    d  = results[0]
                    tp = d.get("type", "")
                    cl = d.get("class", "")
                    if tp in ("way","node","building","road","residential",
                              "secondary","tertiary","street","address",
                              "footway","cycleway","path") or cl in ("highway","building"):
                        prec = "rua"
                    elif tp in ("suburb","quarter","neighbourhood"):
                        prec = "bairro"
                    else:
                        prec = "local"

                    geo = {
                        "lat":      float(d["lat"]),
                        "lon":      float(d["lon"]),
                        "label":    d.get("display_name","").split(",")[0].strip(),
                        "precisao": prec,
                    }
                    # Valida: deve estar a menos de 35 km da cidade
                    dist = ((geo["lat"] - clat)**2 + (geo["lon"] - clon)**2)**0.5
                    if dist > 0.35:
                        geo = None
                else:
                    geo = None
            except Exception as exc:
                _log(f"Nominatim (corpo): {exc}", "WARN")
                geo = None

        _geo_cache[key] = geo
        return geo

    return None


def _worker_geo_refinamento():
    """
    Thread em segundo plano: pega itens da fila _geo_refine_queue,
    lê o corpo do artigo, refina a geocodificação e envia SSE geo_update
    caso encontre localização mais precisa.

    Correções v4:
    - Passa título correto para geocodificar_com_corpo (antes era string vazia)
    - Emite SSE geo_progresso para atualização em tempo real no frontend
    - sleep movido para o fim do loop (não atrasa o primeiro item da fila)
    """
    while True:
        with _geo_refine_lock:
            fila_len = len(_geo_refine_queue)
            if not fila_len:
                time.sleep(2)
                continue
            item = _geo_refine_queue.pop(0)
            fila_restante = len(_geo_refine_queue)

        news_id    = item.get("id")
        url        = item.get("url")
        cidade     = item.get("cidade", "")
        prec_atual = item.get("precisao", "")
        titulo     = item.get("titulo", "")

        # Só refina se ainda não é precisão máxima
        if prec_atual in ("rua", "manual"):
            continue

        # Emite progresso para o frontend
        _publicar_sse("geo_progresso", {
            "processando": True,
            "fila":        fila_restante,
            "id":          news_id,
        })

        _log(f"Refinando geo [{fila_restante} na fila] '{titulo[:60]}'…", "GEO")
        geo = geocodificar_com_corpo(titulo, url, cidade)

        if not geo:
            _publicar_sse("geo_progresso", {
                "processando": fila_restante > 0,
                "fila":        fila_restante,
                "id":          news_id,
            })
            time.sleep(0.5)
            continue

        # Atualiza estado global
        with lock:
            for n in estado["noticias"]:
                if n["id"] == news_id:
                    old_prec = n.get("precisao", "")
                    _prec_rank = {"estado": 0, "cidade": 1, "local": 2,
                                  "bairro": 3, "referencia": 3, "rua": 4, "manual": 5}
                    _GEO_SCORE_UPD = {
                            "rua": 0.92, "bairro": 0.78, "referencia": 0.70,
                            "local": 0.60, "cidade": 0.45, "estado": 0.20,
                        }
                    if _prec_rank.get(geo["precisao"], 0) > _prec_rank.get(old_prec, 0):
                        new_geo_score = round(_GEO_SCORE_UPD.get(geo["precisao"], 0.30), 2)
                        n["lat"]          = geo["lat"]
                        n["lon"]          = geo["lon"]
                        n["label"]        = geo["label"]
                        n["precisao"]     = geo["precisao"]
                        n["geo_refinado"] = True
                        n["geo_score"]    = new_geo_score
                        _log(f"GEO refinado [{old_prec}→{geo['precisao']}]: "
                             f"{geo['label']} para '{titulo[:50]}'", "GEO")
                        _publicar_sse("geo_update", {
                            "id":       news_id,
                            "lat":      geo["lat"],
                            "lon":      geo["lon"],
                            "label":    geo["label"],
                            "precisao": geo["precisao"],
                            "geo_score": new_geo_score,
                        })
                    break

        _publicar_sse("geo_progresso", {
            "processando": fila_restante > 0,
            "fila":        fila_restante,
            "id":          news_id,
        })
        time.sleep(0.5)

# ─────────────────────────────────────────────
#  LÓGICA DE BUSCA (mantida igual)
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

# ─────────────────────────────────────────────
#  SISTEMA AVANÇADO DE CORRELAÇÃO DE FATOS
# ─────────────────────────────────────────────

# Palavras-chave de tipos de evento para matching semântico
_EVENTOS_KEYWORDS = {
    "incêndio":       ["incendio","fogo","chamas","queimou","ardeu","fumaca"],
    "acidente":       ["acidente","batida","colisao","capotou","capotamento","engavetamento"],
    "crime":          ["crime","policia","preso","detido","criminoso","bandido","suspeito","flagrante"],
    "homicídio":      ["homicidio","morte","morto","morreu","vitima","cadaver","corpo","matar","matou"],
    "tráfico":        ["trafico","drogas","entorpecente","cocaina","maconha","crack"],
    "furto/roubo":    ["roubo","furto","assalto","roubou","furtou","assaltou"],
    "atropelamento":  ["atropelamento","atropelou","atropelado","pedestre"],
    "desaparecimento":["desaparecido","desapareceu","sumiu","procurado"],
    "enchente":       ["enchente","alagamento","inundacao","transbordou","chuva","temporal","deslizamento"],
    "explosão":       ["explosao","explodiu","detonou","bomba"],
    "tiroteio":       ["tiroteio","tiros","balaco","disparos","fuzilamento"],
    "obra/trânsito":  ["obras","transito","interdito","bloqueio","semaforo"],
    "saúde":          ["hospital","ubs","medico","paciente","surto","dengue","covid","virus"],
    "política":       ["prefeitura","vereador","prefeito","governador","lei","projeto","aprovado"],
}

def _detectar_eventos(texto_norm):
    """Retorna set de tipos de evento presentes no texto normalizado."""
    encontrados = set()
    for tipo, palavras in _EVENTOS_KEYWORDS.items():
        for p in palavras:
            if p in texto_norm:
                encontrados.add(tipo)
                break
    return encontrados

def _extrair_entidades_proprias(texto_norm):
    """
    Extrai palavras com 4+ chars que NÃO sejam stop-words — candidatas a entidades.
    Inclui bairros/cidades conhecidos encontrados no texto.
    """
    stops_ext = {
        'acidente','incendio','crime','policia','bombeiros','morto','morte',
        'vitima','suspeito','preso','detido','noticia','aconteceu','sera',
        'para','com','que','uma','mais','como','esta','isso','aquele','esse',
        'guarapari','vitoria','espirito','santo','brasil',  # cidades genéricas
    }
    palavras = set()
    for w in texto_norm.split():
        if len(w) >= 4 and w not in stops_ext:
            palavras.add(w)

    # Bairros/logradouros conhecidos
    locais = set()
    for bairro in BAIRROS_COORDS:
        if normalizar(bairro) in texto_norm:
            locais.add(normalizar(bairro))
    return palavras, locais

def mesmo_fato_avancado(t1, t2, f1="", f2="", dt1=None, dt2=None):
    """
    Verifica se dois títulos relatam o MESMO fato.

    Retorna: (is_same: bool, score: float, razoes: list[str])

    Sistema multi-critério:
      1. Similaridade sequencial (SequenceMatcher)
      2. Jaccard sobre palavras-chave
      3. Interseção de tipos de evento (incêndio, crime, acidente…)
      4. Interseção de locais conhecidos (bairros, ruas)
      5. Proximidade temporal (< 48h → mesmas fontes podem cobrir o mesmo fato)
      6. Regra forte: evento + local idênticos → sempre é o mesmo fato

    Garante que fontes iguais nunca são agrupadas.
    """
    # Fontes iguais = nunca o mesmo grupo
    if f1 and f2 and f1 == f2:
        return False, 0.0, []

    n1, n2 = normalizar_texto(t1), normalizar_texto(t2)

    # ── 1. Similaridade sequencial ────────────────────────────────────────
    seq_sim = similaridade(n1, n2)

    # Correspondência quase-exata: encerra rápido
    if seq_sim >= 0.90:
        return True, seq_sim, [f"Título quase idêntico ({seq_sim:.0%})"]

    # ── 2. Jaccard sobre palavras-chave ───────────────────────────────────
    p1, p2 = set(extrair_palavras(n1)), set(extrair_palavras(n2))
    jaccard = len(p1 & p2) / len(p1 | p2) if p1 | p2 else 0

    # ── 3. Tipos de evento ────────────────────────────────────────────────
    ev1, ev2   = _detectar_eventos(n1), _detectar_eventos(n2)
    ev_comuns  = ev1 & ev2
    evento_ok  = len(ev_comuns) > 0

    # ── 4. Locais conhecidos ──────────────────────────────────────────────
    _, loc1    = _extrair_entidades_proprias(n1)
    _, loc2    = _extrair_entidades_proprias(n2)
    loc_comuns = loc1 & loc2
    local_ok   = len(loc_comuns) > 0

    # ── 5. Proximidade temporal ───────────────────────────────────────────
    time_ok = False
    if dt1 and dt2:
        diff_h = abs((dt1 - dt2).total_seconds()) / 3600
        time_ok = diff_h < 72          # dentro de 72h

    # ── 6. Regra forte: evento + local ───────────────────────────────────
    # Dois artigos sobre o mesmo tipo de evento no mesmo lugar
    # são quase certamente o mesmo fato.
    if evento_ok and local_ok:
        score   = max(0.82 + jaccard * 0.18, 0.82)
        razoes  = [
            f"Mesmo evento ({', '.join(ev_comuns)})",
            f"Mesmo local ({', '.join(list(loc_comuns)[:2])})",
        ]
        if time_ok:
            razoes.append("Publicados próximos no tempo")
        return True, min(score, 1.0), razoes

    # ── Score ponderado base ──────────────────────────────────────────────
    score = (
        seq_sim  * PESO_SEQ +
        jaccard  * PESO_JACCARD +
        (PESO_EVENTO if evento_ok else 0) +
        (PESO_LOCAL  if local_ok  else 0)
    )
    if time_ok:
        score += 0.05

    razoes = []
    if seq_sim > 0.60:
        razoes.append(f"Texto similar ({seq_sim:.0%})")
    if jaccard > 0.35:
        razoes.append(f"Palavras-chave em comum ({jaccard:.0%})")
    if ev_comuns:
        razoes.append(f"Evento: {', '.join(ev_comuns)}")
    if loc_comuns:
        razoes.append(f"Local: {', '.join(list(loc_comuns)[:2])}")
    if time_ok:
        razoes.append("Publicados próximos")

    return score >= SIMILARIDADE_MINIMA, round(min(score, 1.0), 3), razoes

def mesmo_fato(t1, t2):
    """Wrapper de compatibilidade."""
    ok, _, _ = mesmo_fato_avancado(t1, t2)
    return ok

def _fontes_rss(cidade):
    """URLs RSS de múltiplas fontes para a cidade monitorada."""
    q  = cidade.replace(" ", "+")
    qp = cidade.replace(" ", "%20")
    return [
        # Google News – queries temáticas separadas para ampliar cobertura
        f"https://news.google.com/rss/search?q={q}&hl=pt-BR&gl=BR&ceid=BR:pt-419",
        f"https://news.google.com/rss/search?q={q}+acidente&hl=pt-BR&gl=BR&ceid=BR:pt-419",
        f"https://news.google.com/rss/search?q={q}+crime+policia&hl=pt-BR&gl=BR&ceid=BR:pt-419",
        f"https://news.google.com/rss/search?q={q}+incendio+transito+obra&hl=pt-BR&gl=BR&ceid=BR:pt-419",
        f"https://news.google.com/rss/search?q={q}+prefeitura+saude+educacao&hl=pt-BR&gl=BR&ceid=BR:pt-419",
        f"https://news.google.com/rss/search?q={q}+defesa+civil+temporal+enchente&hl=pt-BR&gl=BR&ceid=BR:pt-419",
        # Portais regionais ES
        f"https://www.folhaonline.es/feed/?s={qp}",
        f"https://www.aquinoticias.com/?s={qp}&feed=rss2",
        "https://www.folhavitoria.com.br/rss.xml",
        "https://tribunaonline.com.br/feed",
        "https://www.seculodiario.com.br/feed",
        "https://www.gazetaonline.com.br/rss.xml",
        "https://www.a-gazeta.com.br/rss.xml",
        # G1 ES
        "https://g1.globo.com/rss/g1/espirito-santo/",
        # Agência Brasil
        "https://agenciabrasil.ebc.com.br/rss/ultimasnoticias/feed.xml",
        # Busca extra: TV/rádio local
        f"https://news.google.com/rss/search?q={q}+site:es.agenciabrasil.ebc.com.br&hl=pt-BR&gl=BR&ceid=BR:pt-419",
    ]

def _parsear_feed(url, cidade_lower, limite):
    """Baixa e parseia um feed; filtra por cidade e data. Thread-safe."""
    try:
        feed = feedparser.parse(
            url,
            request_headers={"User-Agent": "Arkadia/2.0 (monitor-noticias-mapa)"},
        )
    except Exception:
        return []
    noticias = []
    for item in feed.entries:
        titulo = getattr(item, "title", "") or ""
        if not titulo:
            continue
        resumo = getattr(item, "summary", "") or ""
        # Filtra: notícia deve mencionar a cidade no título ou resumo
        if cidade_lower not in titulo.lower() and cidade_lower not in resumo.lower():
            continue
        link  = getattr(item, "link", "") or ""
        fonte = (
            item.source.title
            if hasattr(item, "source") and hasattr(item.source, "title")
            else (feed.feed.get("title", "") or "Fonte desconhecida")
        )
        dp = getattr(item, "published_parsed", None)
        if dp:
            dt = datetime(*dp[:6])
            if dt < limite:
                continue
            data_fmt = dt.strftime("%d/%m %H:%M")
        else:
            dt, data_fmt = None, "—"
        noticias.append((titulo, link, fonte, data_fmt, dt))
    return noticias

def buscar_noticias(cidade, horas_filtro):
    """Busca em TODAS as fontes em paralelo e retorna lista unificada sem duplicatas."""
    from concurrent.futures import ThreadPoolExecutor, as_completed
    limite       = datetime.now() - timedelta(hours=horas_filtro)
    cidade_lower = cidade.lower()
    urls         = _fontes_rss(cidade)

    todas, vistas = [], set()

    with ThreadPoolExecutor(max_workers=10) as ex:
        futuros = {ex.submit(_parsear_feed, u, cidade_lower, limite): u for u in urls}
        for fut in as_completed(futuros, timeout=25):
            try:
                for item in fut.result():
                    chave = normalizar(item[0])[:80]
                    if chave not in vistas:
                        vistas.add(chave)
                        todas.append(item)
            except Exception:
                pass

    todas.sort(key=lambda x: x[4] or datetime.min, reverse=True)
    return todas

def agrupar_fatos(noticias):
    """
    Agrupa notícias sobre o mesmo fato usando a correlação avançada.
    Cada grupo inclui score de confiança e razões da correlação.
    """
    grupos, usadas = [], set()
    for i, (t1, l1, f1, d1, dt1) in enumerate(noticias):
        if t1 in usadas:
            continue
        grupo        = [(t1, l1, f1, d1, dt1)]
        grupo_scores = []   # (score, razoes) por pares adicionados
        for j, (t2, l2, f2, d2, dt2) in enumerate(noticias):
            if i == j or t2 in usadas or f1 == f2:
                continue
            ok, score, razoes = mesmo_fato_avancado(t1, t2, f1, f2, dt1, dt2)
            if ok:
                grupo.append((t2, l2, f2, d2, dt2))
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
    return hashlib.md5(titulo.encode("utf-8", "ignore")).hexdigest()[:10]

def montar_noticia(grupo_tuple, cidade):
    """
    Monta dict de notícia a partir de um grupo (lista, lista_scores).
    Inclui dados de correlação: confiança e razões por fonte adicional.
    """
    grupo, grupo_scores = grupo_tuple
    titulo_base = max(grupo, key=lambda x: len(x[0]))[0]
    geo = geocodificar_inteligente(titulo_base, cidade)

    # Score de confiança da correlação (média dos pares, se houver)
    confianca_corr = 0.0
    if grupo_scores:
        confianca_corr = sum(s["score"] for s in grupo_scores) / len(grupo_scores)

    # Todas as razões de correlação únicas
    razoes_unicas = []
    for gs in grupo_scores:
        for r in gs.get("razoes", []):
            if r not in razoes_unicas:
                razoes_unicas.append(r)

    news_id = make_id(titulo_base)

    # Score de confiança geográfica: baseado na precisão obtida
    _GEO_SCORE = {
        "rua": 0.92, "bairro": 0.78, "referencia": 0.70,
        "local": 0.60, "cidade": 0.45, "estado": 0.20,
    }
    geo_score = _GEO_SCORE.get(geo["precisao"], 0.30) if geo else 0.10

    return {
        "id":              news_id,
        "titulo":          titulo_base,
        "fontes":          [x[2] for x in grupo],
        "links":           [x[1] for x in grupo],
        "data":            grupo[0][3],
        "multi":           len(grupo) >= 2,
        "confianca_corr":  round(confianca_corr, 2),
        "razoes_corr":     razoes_unicas,
        "lat":             geo["lat"]      if geo else None,
        "lon":             geo["lon"]      if geo else None,
        "label":           geo["label"]    if geo else cidade,
        "precisao":        geo["precisao"] if geo else None,
        "geo_refinado":    False,          # será True após refinamento com corpo
        "geo_score":       round(geo_score, 2),
        "detalhes": [
            {
                "titulo": x[0], "fonte": x[2], "link": x[1], "data": x[3],
                "score":  (grupo_scores[i-1]["score"]   if i > 0 else 1.0),
                "razoes": (grupo_scores[i-1]["razoes"]  if i > 0 else []),
            }
            for i, x in enumerate(grupo)
        ],
    }

# Fila de eventos SSE: cada item é uma string "data: ...\n\n"
_sse_queue    = []
_sse_lock     = threading.Lock()
_sse_clients  = []          # lista de Queue por cliente conectado
_sse_clients_lock = threading.Lock()

# ── Terminal de logs ─────────────────────────────────────────────────────────
_log_buffer = []   # histórico dos últimos 200 logs
_log_lock   = threading.Lock()

def _log(msg, level="INFO"):
    """Registra uma linha no terminal do frontend e no stdout."""
    import json
    ts   = datetime.now().strftime("%H:%M:%S")
    line = {"ts": ts, "level": level, "msg": msg}
    with _log_lock:
        _log_buffer.append(line)
        if len(_log_buffer) > 200:
            _log_buffer.pop(0)
    # Também imprime no terminal do sistema
    prefix = {"INFO": "ℹ️ ", "OK": "✅ ", "WARN": "⚠️  ", "ERR": "✗  ", "SEARCH": "🔍 ", "GEO": "📍 ", "SCRAPE": "🌐 "}.get(level, "   ")
    print(f"[{ts}] {prefix}{msg}")
    _publicar_sse("log", line)

def _publicar_sse(evento, payload_dict):
    """Envia um evento SSE para todos os clientes conectados."""
    import json
    msg = f"event: {evento}\ndata: {json.dumps(payload_dict, ensure_ascii=False)}\n\n"
    with _sse_clients_lock:
        mortos = []
        for q in _sse_clients:
            try:
                q.put_nowait(msg)
            except Exception:
                mortos.append(q)
        for q in mortos:
            _sse_clients.remove(q)

def ciclo_busca():
    """Loop principal de busca. Relê o estado a cada iteração para pegar
    mudanças de cidade/intervalo feitas pelo botão Aplicar em tempo real.
    """
    ultimo_ciclo = 0.0   # timestamp da última busca concluída

    while True:
        # ── Lê estado atual (pode ter mudado via /api/config) ─────────────
        with lock:
            cidade         = estado["cidade"]
            horas          = estado["horas_filtro"]
            intervalo      = estado["intervalo"]
            buscando       = estado["buscando"]
            busca_imediata = estado.get("busca_imediata", False)

        agora = time.time()
        tempo_desde_ultimo = agora - ultimo_ciclo
        deve_buscar = busca_imediata or (tempo_desde_ultimo >= intervalo * 60)

        if buscando or not deve_buscar:
            time.sleep(2)
            continue

        # ── Inicia busca ──────────────────────────────────────────────────
        with lock:
            estado["buscando"]       = True
            estado["busca_imediata"] = False

        try:
            _log(f"Iniciando busca sobre '{cidade}'…", "SEARCH")
            _publicar_sse("buscando", {"buscando": True, "cidade": cidade})

            raw    = buscar_noticias(cidade, horas)
            _log(f"{len(raw)} itens brutos coletados de todos os feeds", "INFO")
            grupos = agrupar_fatos(raw)
            _log(f"{len(grupos)} grupos de fatos identificados (dedup)", "INFO")
            n_novas = 0

            for grupo_tuple in grupos:
                n = montar_noticia(grupo_tuple, cidade)
                chave = normalizar_texto(n["titulo"])

                with lock:
                    # Verifica se a cidade mudou durante a geocodificação
                    if estado["cidade"] != cidade:
                        _log(f"Cidade mudou para '{estado['cidade']}', abortando ciclo", "WARN")
                        break
                    if chave in estado["historico"]:
                        continue
                    estado["historico"].add(chave)
                    estado["noticias"] = [n] + estado["noticias"]
                    estado["noticias"] = estado["noticias"][:200]
                    estado["total_visto"] += 1
                    estado["ultima_busca"] = datetime.now().strftime("%d/%m/%Y %H:%M:%S")

                prec = n.get("precisao","?")
                fontes_str = ", ".join(n.get("fontes", []))[:60]
                _log(f"[{prec}] {n['titulo'][:70]}… | {fontes_str}", "OK")
                _publicar_sse("noticia", n)
                n_novas += 1

                # Enfileira refinamento de geocodificação:
                # - Sempre para precisão imprecisa (cidade/estado/local)
                # - Também para bairro quando o link é Google News (o bairro
                #   do título pode não ser o local do evento — ex: "Adalberto"
                #   aparece no título mas o evento é em outra rua)
                link0 = n.get("links", [""])[0]
                _precisa_refinar = (
                    prec in ("cidade", "estado", "local") or
                    (prec == "bairro" and "news.google.com" in link0)
                )
                if _precisa_refinar and link0:
                    with _geo_refine_lock:
                        _geo_refine_queue.append({
                            "id":       n["id"],
                            "url":      link0,
                            "cidade":   cidade,
                            "precisao": prec,
                            "titulo":   n.get("titulo", ""),
                        })

            with lock:
                estado["buscando"]   = False
                estado["ultima_busca"] = datetime.now().strftime("%d/%m/%Y %H:%M:%S")

            _publicar_sse("buscando", {
                "buscando":     False,
                "ultima_busca": estado["ultima_busca"],
                "total_visto":  estado["total_visto"],
                "cidade":       cidade,
            })
            _log(f"Ciclo concluído: {n_novas} nova(s) / {len(estado['noticias'])} total", "OK")
            ultimo_ciclo = time.time()

        except Exception as exc:
            import traceback; traceback.print_exc()
            _log(f"Erro na busca: {exc}", "ERR")
            with lock:
                estado["buscando"] = False
            _publicar_sse("buscando", {"buscando": False})
            ultimo_ciclo = time.time()

# ─────────────────────────────────────────────
#  FLASK API (mantida igual)
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
            "noticias":     estado["noticias"],
            "ultima_busca": estado["ultima_busca"],
            "buscando":     estado["buscando"],
            "total_visto":  estado["total_visto"],
            "cidade":       estado["cidade"],
        })

@app.route("/api/config", methods=["POST"])
def api_config():
    data = flask_req.json or {}
    mudou_cidade = False
    with lock:
        if "cidade" in data:
            nova = data["cidade"].strip()
            if nova and nova != estado["cidade"]:
                estado["cidade"]    = nova
                estado["noticias"]  = []
                estado["historico"] = set()
                mudou_cidade        = True
        if "intervalo" in data:
            estado["intervalo"]    = max(1, int(data["intervalo"]))
        if "horas_filtro" in data:
            estado["horas_filtro"] = max(1, int(data["horas_filtro"]))
        # Sinaliza que o ciclo deve buscar imediatamente na próxima iteração
        estado["busca_imediata"] = True
        estado["buscando"]       = False   # interrompe ciclo atual se pendurado
    if mudou_cidade:
        # Notifica o frontend para limpar o mapa antes das novas notícias chegarem
        _publicar_sse("limpar", {"cidade": estado["cidade"]})
    return jsonify({"ok": True, "cidade": estado["cidade"]})

@app.route("/api/limpar", methods=["POST"])
def api_limpar():
    with lock:
        estado["noticias"]      = []
        estado["historico"]     = set()
        estado["busca_imediata"] = True
        estado["buscando"]      = False
    _publicar_sse("limpar", {"cidade": estado["cidade"]})
    return jsonify({"ok": True})

@app.route("/api/stream")
def api_stream():
    """SSE endpoint: empurra notícias novas em tempo real para o frontend."""
    import queue, json
    q = queue.Queue(maxsize=200)
    with _sse_clients_lock:
        _sse_clients.append(q)

    # Envia estado atual imediatamente ao conectar
    with lock:
        snapshot = {
            "noticias":     estado["noticias"],
            "ultima_busca": estado["ultima_busca"],
            "buscando":     estado["buscando"],
            "total_visto":  estado["total_visto"],
            "cidade":       estado["cidade"],
        }
    with _log_lock:
        log_snap = list(_log_buffer)
    init_msg  = f"event: snapshot\ndata: {json.dumps(snapshot, ensure_ascii=False)}\n\n"
    log_msg   = f"event: log_snapshot\ndata: {json.dumps({'logs': log_snap}, ensure_ascii=False)}\n\n"

    def stream():
        yield init_msg
        yield log_msg
        while True:
            try:
                msg = q.get(timeout=20)
                yield msg
            except Exception:
                # heartbeat para manter conexão viva
                yield ": heartbeat\n\n"

    resp = app.response_class(stream(), mimetype="text/event-stream")
    resp.headers["Cache-Control"]  = "no-cache"
    resp.headers["X-Accel-Buffering"] = "no"
    return resp

@app.route("/api/geocode")
def api_geocode():
    q      = flask_req.args.get("q", "").strip()
    cidade = flask_req.args.get("cidade", estado["cidade"]).strip()
    if not q:
        return jsonify({"error": "query obrigatória"}), 400

    geo = geocodificar_inteligente(q, cidade)
    return jsonify(geo or {"error": "Localização não encontrada"})

@app.route("/api/logs")
def api_logs():
    """Retorna histórico de logs do terminal."""
    with _log_lock:
        return jsonify({"logs": list(_log_buffer)})

@app.route("/api/scrape")
def api_scrape():
    url = flask_req.args.get("url", "").strip()
    # Suporte a múltiplas URLs separadas por vírgula (para scraping de todas as fontes)
    urls_extra = flask_req.args.get("urls", "").strip()
    if not url:
        return jsonify({"error": "URL obrigatória", "images": [], "videos": [], "fontes": []})
    if not _DEPS_OK:
        return jsonify({"error": "requests/bs4 não instalados", "images": [], "videos": [], "fontes": []})

    todas_urls = [url]
    if urls_extra:
        todas_urls += [u.strip() for u in urls_extra.split(",") if u.strip()]

    # Domínios conhecidos de logos/ícones que NUNCA são imagem de notícia
    _LOGO_DOMAINS = {
        "news.google.com", "gstatic.com", "google.com", "googleapis.com",
        "googleusercontent.com", "gravatar.com", "feedburner.com",
        "wp.com/i/", "s.w.org", "wordpress.com/i/", "disqus.com",
        "facebook.com/tr", "twitter.com/i/", "addthis.com",
    }
    def _is_logo_url(src):
        """Retorna True se a URL parece ser de logo/ícone genérico."""
        sl = src.lower()
        if any(d in sl for d in _LOGO_DOMAINS):
            return True
        # Padrões de nome de arquivo comuns em logos/ícones
        if re.search(r'(?:logo|icon|favicon|avatar|sprite|placeholder|noimage|default'
                     r'|loading|blank|spacer|pixel|badge|button)\b', sl):
            return True
        # SVG inline ou data URI
        if sl.startswith("data:"):
            return True
        return False

    def _resolver_url_googlenews(u):
        """
        Links do Google News (news.google.com/articles/… ou /rss/articles/…)
        são redirecionamentos. Resolve o URL real da notícia seguindo o redirect
        ou extraindo o link canônico da página.
        """
        import urllib.parse as _up
        if "news.google.com" not in u:
            return u
        try:
            r2 = _http.get(u, timeout=8, headers={
                "User-Agent": (
                    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                    "AppleWebKit/537.36 (KHTML, like Gecko) "
                    "Chrome/124.0.0.0 Safari/537.36"
                ),
                "Accept-Language": "pt-BR,pt;q=0.9",
            }, allow_redirects=True)
            # Se o redirect levou a outro domínio, usa esse URL
            final = r2.url
            if "news.google.com" not in final:
                return final
            # Caso contrário, procura canonical ou og:url na página
            soup2 = _bs4.BeautifulSoup(r2.text, "html.parser")
            for tag, attr in [
                ("link",  {"rel": "canonical"}),
                ("meta",  {"property": "og:url"}),
            ]:
                el = soup2.find(tag, attr)
                if el:
                    href = el.get("href") or el.get("content", "")
                    if href and href.startswith("http") and "news.google.com" not in href:
                        return href
            # Último recurso: tenta extrair da tag <a> do artigo principal
            for a in soup2.select("article a[href], .article a[href]"):
                href = a.get("href", "")
                if href.startswith("http") and "news.google.com" not in href:
                    return href
        except Exception:
            pass
        return u  # fallback: url original

    def _normalizar_src(src, base_url):
        """Resolve URLs relativas e extrai a melhor URL de srcset."""
        import urllib.parse as _up
        if not src:
            return ""
        src = src.strip()
        # Resolve relativas
        if src.startswith("//"):
            src = "https:" + src
        elif src.startswith("/") and not src.startswith("//"):
            parsed = _up.urlparse(base_url)
            src = f"{parsed.scheme}://{parsed.netloc}{src}"
        return src

    def _melhor_src_de_srcset(srcset_str, base_url):
        """Extrai a imagem de maior resolução de um atributo srcset."""
        import urllib.parse as _up
        melhor_src, melhor_w = "", 0
        for parte in srcset_str.split(","):
            parte = parte.strip()
            if not parte:
                continue
            tokens = parte.split()
            src_raw = tokens[0]
            w = 0
            if len(tokens) > 1:
                try:
                    w = int(tokens[1].lower().replace("w", "").replace("x", ""))
                except Exception:
                    w = 0
            if w > melhor_w:
                melhor_w = w
                melhor_src = src_raw
        return _normalizar_src(melhor_src, base_url) if melhor_src else ""

    def scrape_one(u):
        try:
            # Resolve redirecionamento do Google News antes de qualquer coisa
            u_real = _resolver_url_googlenews(u)
            _log(f"Scraping: {u_real[:80]}", "SCRAPE")
            r = _http.get(u_real, timeout=10, headers={
                "User-Agent": (
                    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                    "AppleWebKit/537.36 (KHTML, like Gecko) "
                    "Chrome/124.0.0.0 Safari/537.36"
                ),
                "Accept-Language": "pt-BR,pt;q=0.9",
                "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8",
                "Referer": "https://www.google.com/",
            }, allow_redirects=True)

            soup   = _bs4.BeautifulSoup(r.text, "html.parser")
            base_url = r.url
            images, videos = [], []

            def _add_img(src):
                src = _normalizar_src(src, base_url)
                if src and src.startswith("http") and not _is_logo_url(src) and src not in images:
                    images.append(src)
                    return True
                return False

            # ── 1. Meta tags Open Graph / Twitter / Schema.org ─────────────────
            for attr, val in [
                ("property", "og:image"),
                ("property", "og:image:url"),
                ("name",     "twitter:image"),
                ("name",     "twitter:image:src"),
                ("itemprop", "image"),
            ]:
                for tag in soup.find_all("meta", {attr: val}):
                    src = tag.get("content", "") or tag.get("src", "")
                    _add_img(src)

            # ── 2. JSON-LD schema.org (muito comum em portais de notícias) ──────
            import json as _json2
            for script in soup.find_all("script", type="application/ld+json"):
                try:
                    ld = _json2.loads(script.string or "")
                    # Aceita array ou dict
                    items = ld if isinstance(ld, list) else [ld]
                    for item in items:
                        img = item.get("image")
                        if isinstance(img, str):
                            _add_img(img)
                        elif isinstance(img, dict):
                            _add_img(img.get("url", ""))
                        elif isinstance(img, list):
                            for i in img:
                                _add_img(i if isinstance(i, str) else i.get("url",""))
                except Exception:
                    pass

            # ── 3. link rel=image_src (alguns portais usam isso) ─────────────────
            for lnk in soup.find_all("link", rel=lambda r: r and "image_src" in r):
                _add_img(lnk.get("href",""))

            # ── 4. Imagens do corpo do artigo (seletores ampliados + srcset) ───
            selectors = [
                "article img", ".article-body img", ".article img",
                ".content img", "main img", ".materia img",
                "[class*='article'] img", "[class*='content'] img",
                "figure img", ".post-content img", ".entry-content img",
                "[class*='news'] img", "[class*='post'] img",
                "[class*='gallery'] img", "[class*='foto'] img",
                ".imagem img", ".foto img", ".thumb img",
                # Portais brasileiros comuns
                ".g-foto img", ".foto-noticia img", ".imagem-destaque img",
                ".img-responsiva img", ".image-container img",
            ]
            _vistas = set(images)
            for sel in selectors:
                for img_tag in soup.select(sel)[:15]:
                    # Tenta todas as formas de src — inclusive lazy-load
                    src_candidates = [
                        img_tag.get("srcset", ""),          # srcset (pega melhor resolução)
                        img_tag.get("data-srcset", ""),
                        img_tag.get("src", ""),
                        img_tag.get("data-src", ""),
                        img_tag.get("data-lazy-src", ""),
                        img_tag.get("data-original", ""),
                        img_tag.get("data-lazy", ""),
                        img_tag.get("data-hi-res-src", ""),
                        img_tag.get("data-full-src", ""),
                        img_tag.get("data-image", ""),
                    ]
                    # Prioriza srcset se disponível
                    src = ""
                    for cand in src_candidates:
                        if not cand:
                            continue
                        if "," in cand and " " in cand:
                            # É um srcset
                            src = _melhor_src_de_srcset(cand, base_url)
                        else:
                            src = _normalizar_src(cand, base_url)
                        if src:
                            break

                    if not src or not src.startswith("http"):
                        continue
                    if _is_logo_url(src) or src in _vistas:
                        continue

                    # Filtra ícones pequenos por dimensão declarada
                    w = img_tag.get("width", "")
                    h = img_tag.get("height", "")
                    try:
                        if int(w) < 100 or int(h) < 60:
                            continue
                    except Exception:
                        pass

                    _vistas.add(src)
                    images.append(src)
                    if len(images) >= 8:
                        break
                if len(images) >= 8:
                    break

            # ── 5. Fallback: qualquer <img> grande na página ─────────────────────
            if not images:
                for img_tag in soup.find_all("img")[:30]:
                    for attr in ("srcset", "data-srcset", "src", "data-src",
                                 "data-lazy-src", "data-original", "data-image"):
                        cand = img_tag.get(attr, "")
                        if not cand:
                            continue
                        if "," in cand and " " in cand:
                            src = _melhor_src_de_srcset(cand, base_url)
                        else:
                            src = _normalizar_src(cand, base_url)
                        if src and src.startswith("http") and not _is_logo_url(src) and src not in images:
                            w = img_tag.get("width","")
                            h = img_tag.get("height","")
                            try:
                                if int(w) < 150 or int(h) < 100:
                                    continue
                            except Exception:
                                pass
                            images.append(src)
                            break
                    if len(images) >= 4:
                        break

            _log(f"Scrape OK — {len(images)} imgs em {base_url[:60]}", "SCRAPE")

            # YouTube iframes
            for iframe in soup.find_all("iframe", src=True):
                src = iframe["src"]
                if "youtube" in src or "youtu.be" in src:
                    if not src.startswith("http"):
                        src = "https:" + src
                    videos.append({"type": "youtube", "url": src})

            # og:video
            og_vid = soup.find("meta", property="og:video")
            if og_vid and og_vid.get("content"):
                videos.append({"type": "video", "url": og_vid["content"]})

            # Descrição e título
            desc = ""
            for attr, val in [
                ("property", "og:description"),
                ("name", "description"),
                ("name", "twitter:description"),
            ]:
                tag = soup.find("meta", {attr: val})
                if tag and tag.get("content"):
                    desc = tag["content"]
                    break

            og_title = soup.find("meta", property="og:title")
            title = (og_title["content"] if og_title
                     else (soup.title.string if soup.title else ""))

            # Detecta nome do site/veículo a partir de og:site_name ou domínio
            site_name = ""
            og_site = soup.find("meta", property="og:site_name")
            if og_site and og_site.get("content"):
                site_name = og_site["content"]
            else:
                import urllib.parse as _up
                site_name = _up.urlparse(u).netloc.replace("www.", "")

            return {
                "url":         u,
                "site_name":   site_name,
                "images":      images[:8],
                "videos":      videos[:2],
                "title":       (title or "").strip(),
                "description": (desc or "").strip(),
                "ok":          True,
            }
        except Exception as exc:
            _log(f"Scrape erro {u[:50]}: {exc}", "WARN")
            return {"url": u, "site_name": "", "images": [], "videos": [], "title": "", "description": "", "ok": False}

    from concurrent.futures import ThreadPoolExecutor, as_completed
    resultados = []
    with ThreadPoolExecutor(max_workers=4) as ex:
        futuros = {ex.submit(scrape_one, u): u for u in todas_urls}
        for fut in as_completed(futuros, timeout=15):
            try:
                resultados.append(fut.result())
            except Exception:
                pass

    # Ordena: URL principal primeiro
    resultados.sort(key=lambda x: 0 if x["url"] == url else 1)

    # Agrega resultado global
    all_images = []
    all_videos = []
    desc_global = ""
    title_global = ""
    for r in resultados:
        if not desc_global and r.get("description"):
            desc_global = r["description"]
        if not title_global and r.get("title"):
            title_global = r["title"]
        for img in r.get("images", []):
            if img not in all_images:
                all_images.append(img)
        for v in r.get("videos", []):
            if v not in all_videos:
                all_videos.append(v)

    return jsonify({
        "images":      all_images[:8],
        "videos":      all_videos[:3],
        "title":       title_global,
        "description": desc_global,
        "fontes":      resultados,   # resultado por fonte individual
    })



@app.route("/")
def index():
    return HTML_PAGE

# ─────────────────────────────────────────────
#  FRONTEND (HTML embutido - Arkadia v2)
# ─────────────────────────────────────────────
HTML_PAGE = """<!DOCTYPE html>
<html lang="pt-BR">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Arkadia v3 – Notícias ao Vivo</title>
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
#header h1 { font-size: 14px; font-weight: 700; color: #fff; white-space: nowrap; letter-spacing: .3px; }
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

#pin-indicator {
  display: none; position: absolute; bottom: 14px; left: 50%;
  transform: translateX(-50%); z-index: 999;
  background: rgba(239,68,68,.96); color: #fff;
  padding: 7px 18px; border-radius: 20px; font-size: 12px; font-weight: 600;
  pointer-events: none; white-space: nowrap;
  box-shadow: 0 2px 16px rgba(239,68,68,.45);
  animation: fadeInUp .2s ease;
}
@keyframes fadeInUp {
  from { opacity: 0; transform: translateX(-50%) translateY(6px); }
  to   { opacity: 1; transform: translateX(-50%) translateY(0); }
}

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
.card-new {
  animation: cardSlideIn .5s ease;
  border-left: 3px solid #22c55e !important;
}
@keyframes cardSlideIn {
  from { opacity: 0; transform: translateY(-8px); background: #0f2e1a; }
  to   { opacity: 1; transform: translateY(0);    background: transparent; }
}
.card.active { background: #1e2044; border-left: 3px solid #6366f1; }
.card-city {
  font-size: 10px; font-weight: 600; text-transform: uppercase; letter-spacing: .5px;
  color: #818cf8; margin-bottom: 3px; display: flex; align-items: center; gap: 5px; flex-wrap: wrap;
}
.badge-multi {
  background: #ef4444; color: #fff; border-radius: 10px;
  padding: 1px 6px; font-size: 9px; font-weight: 700;
}
.precisao-badge {
  font-size: 9px; padding: 1px 6px; border-radius: 8px; font-weight: 700; white-space: nowrap;
}
.precisao-rua    { background: #064e3b; color: #6ee7b7; }
.precisao-bairro { background: #1e3a5f; color: #93c5fd; }
.precisao-cidade { background: #1e3a5f; color: #93c5fd; }
.precisao-estado { background: #3b2f00; color: #fcd34d; }
.precisao-manual { background: #4c1d3f; color: #f9a8d4; }
.precisao-local  { background: #2d3748; color: #a0aec0; }
.precisao-referencia { background: #1a3a2a; color: #86efac; }

/* Correlação de fontes */
.badge-confianca {
  font-size: 9px; padding: 1px 7px; border-radius: 10px; font-weight: 700;
  white-space: nowrap;
}
.conf-alta   { background: #064e3b; color: #6ee7b7; }
.conf-media  { background: #1e3a5f; color: #93c5fd; }
.conf-baixa  { background: #2d3748; color: #a0aec0; }

.razoes-corr {
  margin-top: 4px; font-size: 10px; color: #64748b; line-height: 1.5;
  border-left: 2px solid #3d4266; padding-left: 6px;
}

/* Geo score (probabilidade de localidade) */
.badge-geo-score {
  font-size: 9px; padding: 1px 7px; border-radius: 10px; font-weight: 700;
  white-space: nowrap;
}
.geo-score-alta  { background: #064e3b; color: #6ee7b7; }
.geo-score-media { background: #1e3a5f; color: #93c5fd; }
.geo-score-baixa { background: #3b2f00; color: #fcd34d; }

/* Geo refinamento em progresso */
@keyframes geo-pulse {
  0%,100% { box-shadow: 0 0 0 0px rgba(251,191,36,.6); }
  50%      { box-shadow: 0 0 0 6px rgba(251,191,36,.0); }
}
.marker-refinando {
  animation: geo-pulse 1.5s infinite;
}

.card-title { font-size: 12px; color: #e2e8f0; line-height: 1.45; margin-bottom: 5px; }
.card-meta  { font-size: 11px; color: #64748b; }
.card-sources { display: flex; gap: 4px; flex-wrap: wrap; margin-top: 4px; }
.src-tag {
  font-size: 10px; padding: 1px 7px; border-radius: 10px;
  background: #252836; border: 1px solid #3d4266; color: #94a3b8;
}
.card-links { display: flex; gap: 6px; margin-top: 6px; flex-wrap: wrap; }
.card-links a {
  font-size: 10px; color: #818cf8; text-decoration: none;
  border: 1px solid #3d4266; border-radius: 4px; padding: 1px 6px;
}
.card-links a:hover { color: #a5b4fc; border-color: #6366f1; }

.card-actions {
  display: flex; gap: 5px; margin-top: 7px; flex-wrap: wrap; align-items: center;
}
.btn-action {
  font-size: 10px; padding: 2px 8px; border-radius: 4px; cursor: pointer;
  border: 1px solid #3d4266; background: #252836; color: #94a3b8;
  font-weight: 500; transition: all .15s; white-space: nowrap; line-height: 1.6;
}
.btn-action:hover  { border-color: #6366f1; color: #a5b4fc; background: #1e2044; }
.btn-action.active { border-color: #6366f1; color: #818cf8; background: #1e2044; }
.btn-pin.pinned    { border-color: #ef4444 !important; color: #ef4444 !important; }

.preview-panel {
  display: none; margin-top: 8px; border-top: 1px solid #2d3148; padding-top: 8px;
}
.preview-loading, .preview-empty {
  color: #64748b; font-size: 11px; font-style: italic; padding: 2px 0;
}
.preview-desc {
  font-size: 11px; color: #94a3b8; line-height: 1.5; margin-bottom: 7px;
  max-height: 52px; overflow: hidden;
}
.preview-images { display: flex; gap: 4px; flex-wrap: wrap; margin-bottom: 6px; }
.preview-images img {
  width: 84px; height: 56px; object-fit: cover; border-radius: 4px; cursor: pointer;
  border: 1px solid #3d4266; transition: border-color .15s, transform .1s;
  background: #252836;
}
.preview-images img:hover { border-color: #6366f1; transform: scale(1.05); }
.preview-videos iframe {
  width: 100%; height: 128px; border-radius: 4px;
  border: 1px solid #3d4266; margin-bottom: 4px; display: block;
}

#empty-state { padding: 40px 20px; text-align: center; color: #475569; font-size: 13px; }
#empty-state p { margin-top: 8px; font-size: 12px; }

.leaflet-popup-content-wrapper {
  background: #1a1d27; color: #e2e8f0; border: 1px solid #3d4266; border-radius: 8px;
  min-width: 240px;
}
.leaflet-popup-tip { background: #1a1d27; }
.leaflet-popup-content { margin: 10px 14px; font-size: 12px; line-height: 1.5; }
.leaflet-popup-content strong { color: #818cf8; display: block; margin-bottom: 6px; }
.popup-fonte  { color: #64748b; font-size: 11px; }
.popup-link   { color: #818cf8; font-size: 11px; }

/* ── Terminal de logs ──────────────────────────────────────────── */
#terminal-bar {
  display: flex; align-items: center; gap: 8px;
  padding: 5px 14px; background: #111318;
  border-top: 1px solid #2d3148; flex-shrink: 0;
  cursor: pointer; user-select: none;
}
#terminal-bar:hover { background: #15181f; }
#terminal-toggle-btn {
  font-size: 11px; color: #64748b; white-space: nowrap;
  display: flex; align-items: center; gap: 5px;
}
#terminal-bar .term-dot {
  width:6px; height:6px; border-radius:50%; background:#22c55e; flex-shrink:0;
  animation: blink 2s infinite;
}
#terminal-bar .term-dot.idle { background:#475569; animation:none; }
#terminal-last-msg {
  font-size: 11px; color: #475569; font-family: monospace;
  overflow: hidden; text-overflow: ellipsis; white-space: nowrap; flex:1;
}
#terminal-count {
  font-size: 10px; color: #475569; white-space: nowrap;
}

#terminal-panel {
  display: none; flex-direction: column;
  height: 220px; background: #0a0c10;
  border-top: 1px solid #2d3148; flex-shrink: 0; overflow: hidden;
}
#terminal-panel.open { display: flex; }
#terminal-toolbar {
  display: flex; align-items: center; gap: 8px;
  padding: 5px 12px; background: #111318;
  border-bottom: 1px solid #1e2334; flex-shrink: 0;
}
#terminal-toolbar span { font-size: 11px; color: #475569; }
#terminal-filter {
  display: flex; gap: 4px; flex-wrap: wrap;
}
.term-filter-btn {
  font-size: 10px; padding: 2px 8px; border-radius: 10px; cursor: pointer;
  border: 1px solid #2d3148; background: transparent; color: #475569;
  transition: all .12s; font-weight: 500;
}
.term-filter-btn.active { border-color: #6366f1; color: #818cf8; background: #1e2044; }
.term-filter-btn[data-level="OK"].active    { border-color:#22c55e; color:#22c55e; background:#0f2e1a; }
.term-filter-btn[data-level="WARN"].active  { border-color:#f59e0b; color:#f59e0b; background:#2a1e00; }
.term-filter-btn[data-level="ERR"].active   { border-color:#ef4444; color:#ef4444; background:#2a0000; }
.term-filter-btn[data-level="GEO"].active   { border-color:#10b981; color:#10b981; background:#0a1e16; }
.term-filter-btn[data-level="SCRAPE"].active{ border-color:#818cf8; color:#818cf8; background:#1a1d40; }
.term-filter-btn[data-level="SEARCH"].active{ border-color:#60a5fa; color:#60a5fa; background:#0f1e30; }
.spacer-term { flex:1; }
#terminal-clear-btn {
  font-size: 10px; padding: 2px 8px; border-radius: 6px; cursor: pointer;
  border: 1px solid #3d4266; background: transparent; color: #64748b;
}
#terminal-clear-btn:hover { color: #ef4444; border-color: #ef4444; }

#terminal-output {
  flex: 1; overflow-y: auto; font-family: 'SFMono-Regular', 'Consolas', monospace;
  font-size: 11px; padding: 6px 10px; line-height: 1.7;
}
#terminal-output::-webkit-scrollbar { width: 4px; }
#terminal-output::-webkit-scrollbar-track { background: #0a0c10; }
#terminal-output::-webkit-scrollbar-thumb { background: #2d3148; border-radius: 2px; }

.term-line {
  display: flex; gap: 8px; align-items: baseline;
  padding: 1px 0; border-bottom: 1px solid transparent;
  transition: background .08s;
}
.term-line:hover { background: #111318; }
.term-ts   { color: #334155; white-space: nowrap; flex-shrink: 0; }
.term-lvl  { font-weight: 700; white-space: nowrap; flex-shrink: 0; min-width: 46px; }
.term-msg  { color: #94a3b8; word-break: break-all; }
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
@keyframes termFade {
  from { background: #1a1d30; }
  to   { background: transparent; }
}

</style>
</head>
<body>

<div id="wrapper">
<div id="header">
  <div class="dot" id="dot"></div>
  <h1>Arkadia <span style="font-size:10px;color:#6366f1;font-weight:400;">v3</span></h1>

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
    <option value="360">15 dias</option>
    <option value="720">1 mês</option>
    <option value="1440">2 meses</option>
    <option value="2160">3 meses</option>
  </select>

  <button id="btn-aplicar" onclick="aplicarConfig()">Aplicar</button>
  <button class="danger" onclick="limpar()">Limpar</button>

  <div class="spacer"></div>
  <span id="status-text">—</span>
  <span id="geo-refinando">refinando geo…</span>
  <div id="count-badge">0 notícias</div>
</div>

<div id="main">
  <div id="map-wrapper">
    <div id="map"></div>
    <div id="pin-indicator">📌 Clique no mapa para posicionar a notícia</div>
  </div>

  <div id="sidebar">
    <div id="sidebar-header">
      <span>Feed de notícias</span>
      <span id="last-update">—</span>
    </div>
    <div id="news-list">
      <div id="empty-state">
        📡
        <p>Aguardando primeira busca...</p>
      </div>
    </div>
  </div>
</div>

<!-- ── Terminal de logs em tempo real ─────────────────────────── -->
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
</div><!-- #wrapper -->

<script>
const API = 'http://localhost:5050';

let newsCache   = [];
let newsById    = {};
let selectedId  = null;
let cidade_atual = 'Guarapari';
let markers     = {};
const openPreviews    = {};
const pinnedLocations = {};
let   pinMode         = null;

function escHtml(s) {
  if (s == null) return '';
  return String(s)
    .replace(/&/g,'&amp;').replace(/</g,'&lt;')
    .replace(/>/g,'&gt;').replace(/"/g,'&quot;');
}
function escAttr(s) {
  if (s == null) return '';
  return String(s).replace(/"/g,'&quot;').replace(/'/g,'&#39;');
}

const map = L.map('map', { center: [-20.67, -40.51], zoom: 12 });
L.tileLayer('https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png', {
  attribution: '© OpenStreetMap', maxZoom: 19,
}).addTo(map);

function makeIcon(multi, precisao, refinado) {
  let color = '#6366f1';
  if (multi)              color = '#ef4444';
  if (precisao === 'rua') color = '#f59e0b';
  else if (precisao === 'bairro' || precisao === 'referencia') color = '#10b981';
  const size  = multi ? 18 : 14;
  const pulse = refinado ? '' : (precisao === 'cidade' || precisao === 'estado'
    ? 'animation:geo-pulse 1.5s infinite;' : '');
  return L.divIcon({
    className: '',
    html: `<div style="
      width:${size}px;height:${size}px;border-radius:50%;
      background:${color};border:2px solid #fff;
      box-shadow:0 0 0 3px ${color}44;${pulse}"></div>`,
    iconSize:   [size, size],
    iconAnchor: [size/2, size/2],
  });
}

function makePopupHtml(n, manual, imgSrc) {
  const pref = manual ? '📌' : (n.precisao === 'rua' ? '📍' : n.precisao === 'bairro' ? '🏘️' : '📍');
  const precisaoText = {
    'rua': '📍 Rua',
    'bairro': '🏘️ Bairro',
    'cidade': '🏙️ Cidade',
    'estado': '🗺️ Estado',
    'manual': '📌 Fixado',
    'referencia': '📍 Ref.',
  }[n.precisao] || '📍 Local';

  let corrInfo = '';
  if (n.multi && n.confianca_corr != null) {
    const pct = (n.confianca_corr * 100).toFixed(0);
    corrInfo = `<br><span style="color:#94a3b8;font-size:10px;">🔗 Correlação: ${pct}% — ${n.fontes.length} fontes</span>`;
    if (n.razoes_corr && n.razoes_corr.length) {
      corrInfo += `<br><span style="color:#64748b;font-size:10px;">${escHtml(n.razoes_corr.join(' · '))}</span>`;
    }
  }

  let geoScoreHtml = '';
  if (n.geo_score != null) {
    const gs = n.geo_score;
    const color = gs >= 0.80 ? '#6ee7b7' : gs >= 0.60 ? '#93c5fd' : '#fcd34d';
    geoScoreHtml = `<span style="color:${color};font-size:10px;">🎯 Localidade: ${(gs*100).toFixed(0)}%</span><br>`;
  }

  let imgHtml = '';
  if (imgSrc) {
    imgHtml = `<img src="${escAttr(imgSrc)}" onerror="this.style.display='none'"
      style="width:100%;max-height:120px;object-fit:cover;border-radius:5px;margin-bottom:7px;display:block;border:1px solid #3d4266;">`;
  }

  return `
    ${imgHtml}
    <strong>${pref} ${escHtml(n.label)} (${precisaoText})</strong><br>
    ${escHtml(n.titulo)}${corrInfo}<br>
    ${geoScoreHtml}
    <span class="popup-fonte">${n.fontes.map(escHtml).join(', ')}</span><br>
    ${n.links.map((l,j) => `<a class="popup-link" href="${escAttr(l)}" target="_blank">Fonte ${j+1}</a>`).join(' · ')}
  `;
}

// Cache de imagens por notícia (para evitar requests duplicados)
const _popupImgCache = {};

async function _getPopupImg(n) {
  if (_popupImgCache[n.id] !== undefined) return _popupImgCache[n.id];
  if (!n.links || !n.links[0]) { _popupImgCache[n.id] = null; return null; }
  try {
    const res  = await fetch(`${API}/api/scrape?url=${encodeURIComponent(n.links[0])}`);
    const data = await res.json();
    const img  = (data.images && data.images[0]) || null;
    _popupImgCache[n.id] = img;
    return img;
  } catch(e) {
    _popupImgCache[n.id] = null;
    return null;
  }
}

map.on('click', function(e) {
  if (pinMode !== null) {
    const id = pinMode;
    pinMode = null;
    document.getElementById('map').style.cursor = '';
    document.getElementById('pin-indicator').style.display = 'none';
    fixarNoMapa(id, e.latlng.lat, e.latlng.lng);
  }
});

document.addEventListener('keydown', e => {
  if (e.key === 'Escape' && pinMode !== null) {
    pinMode = null;
    document.getElementById('map').style.cursor = '';
    document.getElementById('pin-indicator').style.display = 'none';
  }
});

function iniciarPin(id) {
  pinMode = id;
  document.getElementById('map').style.cursor = 'crosshair';
  const titulo = (newsById[id]?.titulo || '').slice(0, 38);
  document.getElementById('pin-indicator').textContent =
    `📌 Clique no mapa — "${titulo}${titulo.length >= 38 ? '…' : ''}"`;
  document.getElementById('pin-indicator').style.display = 'block';
}

function fixarNoMapa(id, lat, lon) {
  const n = newsById[id];
  if (!n) return;
  pinnedLocations[id] = { lat, lon };

  if (markers[id]) map.removeLayer(markers[id]);

  const m = L.marker([lat, lon], { icon: makeIcon(n.multi, 'manual') }).addTo(map);
  m.bindPopup(makePopupHtml(n, true, _popupImgCache[id] || null), { maxWidth: 280 });
  m.on('popupopen', async () => {
    const img = await _getPopupImg(n);
    if (img) m.setPopupContent(makePopupHtml(newsById[id] || n, true, img));
  });
  m.on('click', () => selectCard(id));
  markers[id] = m;
  map.flyTo([lat, lon], 15, { duration: 1 });
  m.openPopup();

  const btn = document.getElementById(`pin-btn-${id}`);
  if (btn) { btn.classList.add('pinned'); btn.textContent = '📌 Fixado'; }

  const badge = document.querySelector(`#card-${id} .prec-badge`);
  if (badge) {
    badge.className = 'precisao-badge precisao-manual prec-badge';
    badge.textContent = '📌 Fixado';
  }
}

function adicionarMarcador(n) {
  if (markers[n.id]) return;
  const pin = pinnedLocations[n.id];
  const lat = pin ? pin.lat : n.lat;
  const lon = pin ? pin.lon : n.lon;
  if (lat == null || lon == null) return;
  const m = L.marker([lat, lon], { icon: makeIcon(n.multi, n.precisao, n.geo_refinado) }).addTo(map);
  // Popup inicial leve (sem imagem ainda)
  m.bindPopup(makePopupHtml(n, !!pin, null), { maxWidth: 280 });
  m.on('click', () => selectCard(n.id));
  m.on('popupopen', async () => {
    // Carrega imagem ao abrir o popup (somente uma vez por notícia)
    const img = await _getPopupImg(n);
    if (img) {
      const updated = makePopupHtml(newsById[n.id] || n, !!pinnedLocations[n.id], img);
      m.setPopupContent(updated);
    }
  });
  markers[n.id] = m;
}

function atualizarMarcador(n) {
  if (!markers[n.id]) { adicionarMarcador(n); return; }
  const pin = pinnedLocations[n.id];
  if (pin) return;  // não sobrescreve pinos manuais
  // Atualiza popup com dados mais recentes (inclui img do cache se já carregada)
  markers[n.id].setIcon(makeIcon(n.multi, n.precisao, n.geo_refinado));
  markers[n.id].setPopupContent(makePopupHtml(n, false, _popupImgCache[n.id] || null));
  // Se o popup estiver aberto, atualiza posição
  if (markers[n.id].isPopupOpen()) {
    map.removeLayer(markers[n.id]);
    delete markers[n.id];
    adicionarMarcador(n);
  }
}

function updateMarkers(noticias) {
  const currentIds = new Set(noticias.map(n => n.id));
  Object.keys(markers).forEach(id => {
    if (!currentIds.has(id)) { map.removeLayer(markers[id]); delete markers[id]; }
  });
  noticias.forEach(adicionarMarcador);
}

function renderCard(n) {
  const prec      = n.precisao || '';
  const precMap   = { rua:'📍 Rua', bairro:'🏘️ Bairro', cidade:'🏙️ Cidade',
                      estado:'🗺️ Estado', manual:'📌 Fixado', referencia:'📍 Ref.' };
  const precLabel = precMap[prec] || '';
  const pinned    = !!pinnedLocations[n.id];

  // Badge de confiança da correlação
  let confBadge = '';
  if (n.multi && n.confianca_corr != null) {
    const c = n.confianca_corr;
    const cls   = c >= 0.80 ? 'conf-alta' : c >= 0.60 ? 'conf-media' : 'conf-baixa';
    const label = c >= 0.80 ? `✓ Confirmado ${(c*100).toFixed(0)}%`
                : c >= 0.60 ? `≈ Provável ${(c*100).toFixed(0)}%`
                :              `? Possível ${(c*100).toFixed(0)}%`;
    confBadge = `<span class="badge-confianca ${cls}">${label}</span>`;
  }

  // Razões da correlação
  let razoesHtml = '';
  if (n.multi && n.razoes_corr && n.razoes_corr.length) {
    razoesHtml = `<div class="razoes-corr">🔗 ${escHtml(n.razoes_corr.join(' · '))}</div>`;
  }

  // Badge de geo_score (probabilidade de localidade)
  let geoScoreHtml = '';
  if (n.geo_score != null && n.precisao) {
    const gs = n.geo_score;
    const gsCls = gs >= 0.80 ? 'geo-score-alta' : gs >= 0.60 ? 'geo-score-media' : 'geo-score-baixa';
    const gsLabel = `🎯 ${(gs*100).toFixed(0)}% local`;
    geoScoreHtml = `<span class="badge-geo-score ${gsCls}">${gsLabel}</span>`;
  }

  // Indicador de refinamento em progresso — só aparece se NÃO refinado e precisão imprecisa
  const emRefinamento = !n.geo_refinado && (prec === 'cidade' || prec === 'estado');
  const refineTag = emRefinamento
    ? `<span class="precisao-badge prec-refinando" style="background:#2d2000;color:#fcd34d;font-size:9px;padding:1px 6px;border-radius:8px;">⏳ Refinando…</span>`
    : '';

  return `<div class="card" id="card-${n.id}" onclick="selectCard('${n.id}')">
    <div class="card-city">
      ${prec === 'bairro' ? '🏘️' : (prec === 'rua' ? '📍' : (prec === 'referencia' ? '📍' : '📍'))} ${escHtml(n.label || n.titulo.slice(0,30))}
      ${n.multi ? '<span class="badge-multi">MÚLTIPLAS FONTES</span>' : ''}
      ${confBadge}
      ${precLabel ? `<span class="precisao-badge precisao-${prec} prec-badge">${precLabel}</span>` : ''}
      ${geoScoreHtml}
      ${refineTag}
    </div>
    ${razoesHtml}
    <div class="card-title">${escHtml(n.titulo)}</div>
    <div class="card-meta">${escHtml(n.data)}</div>
    <div class="card-sources">${n.fontes.map(f => `<span class="src-tag">${escHtml(f)}</span>`).join('')}</div>
    <div class="card-links">${n.links.map((l,j) => `<a href="${escAttr(l)}" target="_blank">🔗 Fonte ${j+1}</a>`).join('')}</div>
    <div class="card-actions">
      <button class="btn-action btn-preview" onclick="event.stopPropagation();togglePreview('${n.id}')">🖼 Mídia</button>
      <button class="btn-action btn-pin${pinned?' pinned':''}" id="pin-btn-${n.id}" onclick="event.stopPropagation();iniciarPin('${n.id}')">${pinned?'📌 Fixado':'📌 Fixar'}</button>
      <button class="btn-action btn-locate" onclick="event.stopPropagation();geocodificarCard('${n.id}')">🔍 Localizar</button>
    </div>
    <div class="preview-panel" id="preview-${n.id}"></div>
  </div>`;
}

function renderNoticias(data) {
  const list  = document.getElementById('news-list');
  const badge = document.getElementById('count-badge');
  cidade_atual = data.cidade || '';
  newsCache    = data.noticias || [];
  newsById     = {};
  newsCache.forEach(n => { newsById[n.id] = n; });

  badge.textContent = `${newsCache.length} notícia${newsCache.length !== 1 ? 's' : ''}`;
  document.getElementById('last-update').textContent = data.ultima_busca
    ? `Atualizado ${data.ultima_busca.slice(11)}` : '—';

  const dot = document.getElementById('dot');
  dot.className = 'dot' + (data.buscando ? ' loading' : '');
  document.getElementById('status-text').textContent = data.buscando
    ? 'buscando...'
    : `${data.total_visto} vistas | cidade: ${data.cidade}`;

  updateMarkers(newsCache);

  if (!newsCache.length) {
    list.innerHTML = '<div id="empty-state">📡<p>Aguardando notícias...</p></div>';
    return;
  }

  const savedPreviews = {};
  newsCache.forEach(n => {
    const panel = document.getElementById(`preview-${n.id}`);
    if (panel && panel.style.display === 'block') {
      savedPreviews[n.id] = panel.innerHTML;
    }
  });

  list.innerHTML = newsCache.map(n => renderCard(n)).join('');

  if (selectedId) {
    const card = document.getElementById(`card-${selectedId}`);
    if (card) card.classList.add('active');
  }

  Object.entries(savedPreviews).forEach(([id, html]) => {
    const panel = document.getElementById(`preview-${id}`);
    if (panel) { panel.style.display = 'block'; panel.innerHTML = html; }
    const btn = document.querySelector(`#card-${id} .btn-preview`);
    if (btn) btn.classList.add('active');
    openPreviews[id] = html;
  });

  Object.keys(pinnedLocations).forEach(id => {
    const btn = document.getElementById(`pin-btn-${id}`);
    if (btn) { btn.classList.add('pinned'); btn.textContent = '📌 Fixado'; }
  });
}

function selectCard(id) {
  if (selectedId) {
    const prev = document.getElementById(`card-${selectedId}`);
    if (prev) prev.classList.remove('active');
  }
  selectedId = id;
  const card = document.getElementById(`card-${id}`);
  if (card) { card.classList.add('active'); card.scrollIntoView({ behavior:'smooth', block:'nearest' }); }
  const n   = newsById[id];
  const pin = pinnedLocations[id];
  const lat = pin ? pin.lat : n?.lat;
  const lon = pin ? pin.lon : n?.lon;
  if (lat != null && markers[id]) {
    map.flyTo([lat, lon], 14, { duration: 1 });
    markers[id].openPopup();
  }
}

async function geocodificarCard(id) {
  const n = newsById[id];
  if (!n) return;
  const btn = document.querySelector(`#card-${id} .btn-locate`);
  if (btn) { btn.textContent = '🔍 …'; btn.disabled = true; }
  try {
    const res = await fetch(
      `${API}/api/geocode?q=${encodeURIComponent(n.titulo)}&cidade=${encodeURIComponent(cidade_atual)}`
    );
    const geo = await res.json();
    if (geo && geo.lat != null) {
      fixarNoMapa(id, geo.lat, geo.lon);
      if (geo.label)   newsById[id].label   = geo.label;
      if (geo.precisao) {
        newsById[id].precisao = geo.precisao;
        const badge = document.querySelector(`#card-${id} .prec-badge`);
        if (badge) {
          const labels = { rua:'📍 Rua', bairro:'🏘️ Bairro', cidade:'🏙️ Cidade', estado:'🗺️ Estado', manual:'📌 Fixado' };
          badge.textContent = labels[geo.precisao] || geo.precisao;
          badge.className = `precisao-badge precisao-${geo.precisao} prec-badge`;
        }
      }
      map.flyTo([geo.lat, geo.lon], 15, { duration: 1.5 });
    } else {
      if (btn) btn.textContent = '🔍 Não achado';
      setTimeout(() => { if (btn) { btn.textContent='🔍 Localizar'; btn.disabled=false; } }, 2500);
      return;
    }
  } catch(e) {
    if (btn) btn.textContent = '🔍 Erro';
  }
  setTimeout(() => { if (btn) { btn.textContent='🔍 Localizar'; btn.disabled=false; } }, 2000);
}

async function togglePreview(id) {
  const panel = document.getElementById(`preview-${id}`);
  const btn   = document.querySelector(`#card-${id} .btn-preview`);
  if (!panel) return;

  if (panel.style.display === 'block') {
    panel.style.display = 'none';
    if (btn) btn.classList.remove('active');
    delete openPreviews[id];
    return;
  }

  panel.style.display = 'block';
  if (btn) btn.classList.add('active');

  if (openPreviews[id]) { panel.innerHTML = openPreviews[id]; return; }

  panel.innerHTML = '<div class="preview-loading">⏳ Carregando mídia…</div>';

  const url = newsById[id]?.links?.[0];
  if (!url) {
    panel.innerHTML = '<div class="preview-empty">Sem URL disponível.</div>';
    return;
  }

  try {
    const res  = await fetch(`${API}/api/scrape?url=${encodeURIComponent(url)}`);
    const data = await res.json();
    let html   = '';

    if (data.description) {
      html += `<div class="preview-desc">${escHtml(data.description.slice(0,240))}</div>`;
    }
    if (data.images && data.images.length) {
      html += '<div class="preview-images">';
      data.images.slice(0,4).forEach(src => {
        html += `<img src="${escAttr(src)}"
          onerror="this.style.display='none'"
          onclick="window.open('${escAttr(url)}','_blank')"
          title="Clique para abrir a fonte">`;
      });
      html += '</div>';
    }
    if (data.videos && data.videos.length) {
      data.videos.slice(0,1).forEach(v => {
        if (v.type === 'youtube' && v.url) {
          let embed = v.url;
          if (!embed.includes('/embed/')) {
            embed = embed.replace('watch?v=','embed/').replace('youtu.be/','youtube.com/embed/');
          }
          if (!embed.startsWith('http')) embed = 'https:' + embed;
          html += `<div class="preview-videos">
            <iframe src="${escAttr(embed)}" frameborder="0" allowfullscreen loading="lazy"></iframe>
          </div>`;
        }
      });
    }
    if (!html) {
      html = '<div class="preview-empty">Nenhuma mídia encontrada nesta página.</div>';
    }
    panel.innerHTML  = html;
    openPreviews[id] = html;
  } catch(e) {
    panel.innerHTML = '<div class="preview-empty">Erro ao carregar mídia.</div>';
    delete openPreviews[id];
  }
}

async function aplicarConfig() {
  const cidade    = document.getElementById('cidade-input').value.trim();
  const intervalo = parseInt(document.getElementById('intervalo-select').value);
  const horas     = parseInt(document.getElementById('horas-select').value);
  if (!cidade) return;

  const btn = document.getElementById('btn-aplicar');
  if (btn) { btn.textContent = '⏳ Aplicando…'; btn.disabled = true; }

  try {
    const res  = await fetch(`${API}/api/config`, {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({ cidade, intervalo, horas_filtro: horas }),
    });
    const data = await res.json();
    // Se a cidade mudou, limpa o estado local imediatamente
    // (o evento SSE "limpar" fará o mesmo, mas isso garante responsividade)
    if (data.cidade && data.cidade !== cidade_atual) {
      limparEstadoLocal(data.cidade);
    }
  } catch(e) {
    console.error('Erro ao aplicar config:', e);
  } finally {
    if (btn) { btn.textContent = 'Aplicar'; btn.disabled = false; }
  }
}

function limparEstadoLocal(novaCidade) {
  newsCache = []; newsById = {}; selectedId = null;
  Object.keys(openPreviews).forEach(k => delete openPreviews[k]);
  Object.keys(pinnedLocations).forEach(k => delete pinnedLocations[k]);

  document.getElementById('news-list').innerHTML =
    `<div id="empty-state">🔍<p>Buscando notícias em <strong>${escHtml(novaCidade)}</strong>…</p></div>`;
  document.getElementById('count-badge').textContent = '0 notícias';
  document.getElementById('last-update').textContent = '—';

  Object.values(markers).forEach(m => map.removeLayer(m));
  markers = {};

  if (novaCidade) {
    cidade_atual = novaCidade;
    // Centraliza o mapa na nova cidade via geocodificação leve
    fetch(`${API}/api/geocode?q=${encodeURIComponent(novaCidade)}&cidade=${encodeURIComponent(novaCidade)}`)
      .then(r => r.json())
      .then(geo => {
        if (geo && geo.lat != null) map.flyTo([geo.lat, geo.lon], 12, { duration: 1.2 });
      })
      .catch(() => {});
  }
}

async function limpar() {
  try { await fetch(`${API}/api/limpar`, { method:'POST' }); } catch(e) { /* ignora */ }
  limparEstadoLocal(cidade_atual);
  document.getElementById('news-list').innerHTML =
    '<div id="empty-state">🗑️<p>Lista limpa. Aguardando próxima busca…</p></div>';
}

// ── SSE: recebe notícias em tempo real sem re-render total ───────────────
let sseReconnectDelay = 2000;

function conectarSSE() {
  const es = new EventSource(`${API}/api/stream`);

  // Snapshot inicial: carrega tudo de uma vez ao conectar
  es.addEventListener('snapshot', e => {
    const data = JSON.parse(e.data);
    cidade_atual = data.cidade || '';
    data.noticias.forEach(n => {
      if (!newsById[n.id]) {
        newsById[n.id] = n;
        newsCache.unshift(n);
      }
    });
    renderTudo(data);
    sseReconnectDelay = 2000;
  });

  // Notícia nova: insere card no topo e adiciona marcador sem tocar o resto
  es.addEventListener('noticia', e => {
    const n = JSON.parse(e.data);
    if (newsById[n.id]) return;           // já existe
    newsById[n.id] = n;
    newsCache.unshift(n);

    // Insere card no topo do feed
    const list = document.getElementById('news-list');
    const empty = document.getElementById('empty-state');
    if (empty) empty.remove();
    const tmp = document.createElement('div');
    tmp.innerHTML = renderCard(n);
    const card = tmp.firstChild;
    card.classList.add('card-new');
    list.prepend(card);
    setTimeout(() => card.classList.remove('card-new'), 800);

    // Adiciona marcador no mapa
    adicionarMarcador(n);

    // Atualiza badge
    document.getElementById('count-badge').textContent =
      `${newsCache.length} notícia${newsCache.length !== 1 ? 's' : ''}`;
  });

  // Servidor mandou limpar (mudança de cidade ou botão Limpar)
  es.addEventListener('limpar', e => {
    const d = JSON.parse(e.data);
    limparEstadoLocal(d.cidade || cidade_atual);
  });

  // Refinamento de geocodificação em segundo plano
  es.addEventListener('geo_update', e => {
    const u = JSON.parse(e.data);
    if (!newsById[u.id]) return;
    // Atualiza dados locais
    newsById[u.id].lat        = u.lat;
    newsById[u.id].lon        = u.lon;
    newsById[u.id].label      = u.label;
    newsById[u.id].precisao   = u.precisao;
    newsById[u.id].geo_refinado = true;
    if (u.geo_score != null) newsById[u.id].geo_score = u.geo_score;

    // Atualiza marcador no mapa (remove e readiciona com novo ícone)
    atualizarMarcador(newsById[u.id]);

    // Atualiza badge de precisão no card
    const badge = document.querySelector(`#card-${u.id} .prec-badge`);
    const precMap = { rua:'📍 Rua', bairro:'🏘️ Bairro', cidade:'🏙️ Cidade',
                      estado:'🗺️ Estado', manual:'📌 Fixado', referencia:'📍 Ref.' };
    if (badge) {
      badge.textContent  = precMap[u.precisao] || u.precisao;
      badge.className    = `precisao-badge precisao-${u.precisao} prec-badge`;
    }

    // Remove badge "refinando…" — geo refinado, não precisa mais
    const cardCity = document.querySelector(`#card-${u.id} .card-city`);
    if (cardCity) {
      cardCity.querySelectorAll('.prec-refinando').forEach(el => el.remove());
    }

    // Atualiza ou insere badge de geo_score
    if (u.geo_score != null && cardCity) {
      const gs = u.geo_score;
      const gsCls = gs >= 0.80 ? 'geo-score-alta' : gs >= 0.60 ? 'geo-score-media' : 'geo-score-baixa';
      const gsLabel = `🎯 ${(gs*100).toFixed(0)}% local`;
      let gsBadge = cardCity.querySelector('.badge-geo-score');
      if (gsBadge) {
        gsBadge.className = `badge-geo-score ${gsCls}`;
        gsBadge.textContent = gsLabel;
      } else {
        gsBadge = document.createElement('span');
        gsBadge.className = `badge-geo-score ${gsCls}`;
        gsBadge.textContent = gsLabel;
        cardCity.appendChild(gsBadge);
      }
    }

    // Atualiza label
    const titleEl = document.querySelector(`#card-${u.id} .card-city`);
    if (titleEl && u.label) {
      // Substitui o texto do local no primeiro text node
      const tn = [...titleEl.childNodes].find(n => n.nodeType === 3);
      if (tn) tn.textContent = ` ${u.label} `;
    }

    _log && console.log(`🗺️ Geo refinado [${u.precisao}]: ${u.label}`);
  });

  // Progresso de refinamento de geocodificação em segundo plano
  es.addEventListener('geo_progresso', e => {
    const d = JSON.parse(e.data);
    const el = document.getElementById('geo-refinando');
    if (!el) return;
    if (d.processando) {
      el.className = 'ativo';
      el.textContent = d.fila > 0
        ? `refinando geo… (${d.fila} na fila)`
        : 'refinando geo…';
    } else {
      el.className = '';
      el.textContent = 'refinando geo…';
    }
  });

  // Status de busca (dot + texto)
  es.addEventListener('buscando', e => {
    const d = JSON.parse(e.data);
    const dot = document.getElementById('dot');
    if (d.buscando) {
      dot.className = 'dot loading';
      document.getElementById('status-text').textContent =
        d.cidade ? `buscando ${d.cidade}…` : 'buscando…';
    } else {
      dot.className = 'dot';
      if (d.ultima_busca) {
        document.getElementById('last-update').textContent =
          `Atualizado ${d.ultima_busca.slice(11)}`;
      }
      if (d.total_visto != null) {
        document.getElementById('status-text').textContent =
          `${d.total_visto} vistas | cidade: ${d.cidade || cidade_atual}`;
      }
      if (d.cidade) cidade_atual = d.cidade;
    }
  });

  es.onerror = () => {
    es.close();
    document.getElementById('dot').className = 'dot off';
    document.getElementById('status-text').textContent = 'reconectando…';
    setTimeout(conectarSSE, sseReconnectDelay);
    sseReconnectDelay = Math.min(sseReconnectDelay * 2, 30000);
  };

  // Snapshot de logs ao reconectar
  es.addEventListener('log_snapshot', e => {
    const d = JSON.parse(e.data);
    (d.logs || []).forEach(l => _termAppend(l));
  });

  // Log em tempo real
  es.addEventListener('log', e => {
    const d = JSON.parse(e.data);
    _termAppend(d);
  });
}

// Renderização inicial completa (usada só no snapshot)
function renderTudo(data) {
  const list  = document.getElementById('news-list');
  const badge = document.getElementById('count-badge');

  badge.textContent = `${newsCache.length} notícia${newsCache.length !== 1 ? 's' : ''}`;
  document.getElementById('last-update').textContent = data.ultima_busca
    ? `Atualizado ${data.ultima_busca.slice(11)}` : '—';

  const dot = document.getElementById('dot');
  dot.className = 'dot' + (data.buscando ? ' loading' : '');
  document.getElementById('status-text').textContent = data.buscando
    ? 'buscando...'
    : `${data.total_visto} vistas | cidade: ${data.cidade}`;

  newsCache.forEach(adicionarMarcador);

  if (!newsCache.length) {
    list.innerHTML = '<div id="empty-state">📡<p>Aguardando notícias...</p></div>';
    return;
  }
  list.innerHTML = newsCache.map(n => renderCard(n)).join('');
}

// ── Terminal de logs ────────────────────────────────────────────
const _termLogs   = [];          // buffer de todas as linhas
let   _termFilter = 'ALL';       // filtro ativo
let   _termOpen   = false;

const _termLevelIcons = {
  INFO:'ℹ️ INFO', OK:'✅ OK', WARN:'⚠️  WARN', ERR:'✗  ERR',
  GEO:'📍 GEO', SCRAPE:'🌐 SCRP', SEARCH:'🔍 SRCH',
};

function _termLine(log) {
  const div = document.createElement('div');
  div.className = 'term-line term-new';
  div.dataset.level = log.level;
  div.innerHTML =
    `<span class="term-ts">${escHtml(log.ts)}</span>` +
    `<span class="term-lvl">${escHtml(_termLevelIcons[log.level] || log.level)}</span>` +
    `<span class="term-msg">${escHtml(log.msg)}</span>`;
  setTimeout(() => div.classList.remove('term-new'), 450);
  return div;
}

function _termMatchFilter(log) {
  return _termFilter === 'ALL' || log.level === _termFilter;
}

function _termAppend(log) {
  _termLogs.push(log);
  if (_termLogs.length > 500) _termLogs.shift();

  // Atualiza barra inferior
  const termDot = document.getElementById('term-dot');
  const lastMsg  = document.getElementById('terminal-last-msg');
  const countEl  = document.getElementById('terminal-count');
  if (termDot) {
    termDot.className = 'term-dot' + (log.level === 'ERR' ? ' err' :
      log.level === 'WARN' ? ' warn' : '');
    termDot.style.background = log.level === 'ERR' ? '#ef4444' :
      log.level === 'WARN' ? '#f59e0b' : '#22c55e';
    termDot.style.animation  = 'blink .5s 3';
    setTimeout(() => {
      if (termDot) { termDot.style.animation = ''; termDot.className = 'term-dot'; }
    }, 1500);
  }
  if (lastMsg) lastMsg.textContent = `[${log.ts}] ${log.msg.slice(0,80)}`;
  if (countEl) countEl.textContent = `${_termLogs.length} linhas`;

  // Se terminal aberto e linha passa no filtro, adiciona ao output
  if (!_termOpen) return;
  if (!_termMatchFilter(log)) return;
  const out = document.getElementById('terminal-output');
  if (!out) return;
  out.appendChild(_termLine(log));
  const auto = document.getElementById('term-autoscroll');
  if (!auto || auto.checked) out.scrollTop = out.scrollHeight;
  // Mantém DOM leve (máx 300 linhas visíveis)
  while (out.children.length > 300) out.removeChild(out.firstChild);
}

function _termRedraw() {
  const out = document.getElementById('terminal-output');
  if (!out) return;
  out.innerHTML = '';
  const frag = document.createDocumentFragment();
  _termLogs.filter(_termMatchFilter).forEach(l => frag.appendChild(_termLine(l)));
  out.appendChild(frag);
  out.scrollTop = out.scrollHeight;
}

function toggleTerminal() {
  const panel = document.getElementById('terminal-panel');
  const label = document.getElementById('terminal-label');
  _termOpen = !_termOpen;
  if (_termOpen) {
    panel.classList.add('open');
    if (label) label.textContent = '▼ Terminal';
    _termRedraw();
  } else {
    panel.classList.remove('open');
    if (label) label.textContent = '▶ Terminal';
  }
}

function termClear() {
  _termLogs.length = 0;
  const out = document.getElementById('terminal-output');
  if (out) out.innerHTML = '';
  const c = document.getElementById('terminal-count');
  if (c) c.textContent = '0 linhas';
}

// Botões de filtro
document.addEventListener('DOMContentLoaded', () => {
  document.querySelectorAll('.term-filter-btn').forEach(btn => {
    btn.addEventListener('click', e => {
      e.stopPropagation();
      document.querySelectorAll('.term-filter-btn').forEach(b => b.classList.remove('active'));
      btn.classList.add('active');
      _termFilter = btn.dataset.level;
      if (_termOpen) _termRedraw();
    });
  });
});

conectarSSE();
</script>
</body>
</html>
"""

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
    print(f"⚠️  Servidor não respondeu. Abra manualmente: http://localhost:{PORT}")

def main():
    print("=" * 57)
    print("  Arkadia v3 – Monitor de Notícias com Mapa ao Vivo")
    print("=" * 57)

    cidade = input("📍 Cidade a monitorar (Enter = Guarapari): ").strip()
    if cidade:
        estado["cidade"] = cidade

    intervalo_input = input(f"⏰ Intervalo em minutos (Enter = {DEFAULT_INTERVALO}): ").strip()
    if intervalo_input.isdigit():
        estado["intervalo"] = max(1, int(intervalo_input))

    horas_input = input(f"🕐 Filtrar últimas N horas (Enter = {DEFAULT_HORAS_FILTRO} | max 2160 = 3 meses): ").strip()
    if horas_input.isdigit():
        estado["horas_filtro"] = max(1, min(2160, int(horas_input)))

    print(f"\n✅ Monitorando '{estado['cidade']}' a cada {estado['intervalo']} min "
          f"| filtro {estado['horas_filtro']}h")
    if not _DEPS_OK:
        print("⚠️  Geocodificação Nominatim e scraping de mídia desativados "
              "(instale requests + beautifulsoup4)")
    print("   Pressione Ctrl+C para parar.\n")

    threading.Thread(target=open_when_ready, daemon=True).start()
    threading.Thread(target=ciclo_busca, daemon=True).start()
    threading.Thread(target=_worker_geo_refinamento, daemon=True).start()
    app.run(host="0.0.0.0", port=PORT, debug=False, use_reloader=False)

if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\n\n🛑 Arkadia encerrado.")
        print(f"📊 Total de notícias vistas: {estado['total_visto']}")
        print("\U0001f44b Até logo!")
