#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
国道走破マップ生成ツール v2

走破した区間を routes.csv に書き足して build を実行すると，
走破済み＝赤／未走破＝グレーで塗り分けた地図 (kokudo_map.html) が出来上がる。

区間の指定方法は4通り:
    全線
    新潟県                    都道府県まるごと
    新潟県長岡市              市町村まるごと
    宮内〜川崎                交差点から交差点まで

使い方:
    python kokudo_map.py init            routes.csv のひな形を作る
    python kokudo_map.py fetch           routes.csv に出てくる路線の形状を取得
    python kokudo_map.py fetch --all     全国道 (1〜507号) の形状を取得（初回のみ）
    python kokudo_map.py nodes 17        国道17号で使える交差点名の一覧を出す
    python kokudo_map.py build           地図を生成

依存ライブラリなし（標準ライブラリのみ）。
"""

from __future__ import annotations

import argparse
import csv
import heapq
import http.server
import io
import json
import math
import os
import random
import re
import sys
import threading
import time
import unicodedata
import urllib.error
import urllib.request
import webbrowser
from collections import defaultdict

# --------------------------------------------------------------------------
# 設定
# --------------------------------------------------------------------------

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
CACHE_DIR = os.path.join(BASE_DIR, "cache")
AREA_DIR = os.path.join(CACHE_DIR, "area")
NODE_DIR = os.path.join(CACHE_DIR, "nodes")
LIST_DIR = os.path.join(BASE_DIR, "交差点一覧")
JUNCTION_PATH = os.path.join(CACHE_DIR, "junctions.json")
EKI_DIR = os.path.join(CACHE_DIR, "michinoeki")
CSV_PATH = os.path.join(BASE_DIR, "routes.csv")
EKI_CSV_PATH = os.path.join(BASE_DIR, "michinoeki.csv")
OUT_PATH = os.path.join(BASE_DIR, "kokudo_map.html")

OVERPASS_ENDPOINTS = [
    "https://overpass-api.de/api/interpreter",
    "https://overpass.kumi.systems/api/interpreter",
    "https://overpass.private.coffee/api/interpreter",
]

# 1リクエストあたりの最短間隔（秒）。混雑を検知すると自動で延びる。
REQUEST_INTERVAL = 2.0
MAX_INTERVAL = 30.0
# 1路線あたりの試行回数と，全体を何周まわすか
ATTEMPTS_PER_TARGET = 6
MAX_PASSES = 6
# 1周まわり終えて未取得が残っていたときの待機時間（秒）
PASS_COOLDOWN = 90.0
# 429（レート制限）を受けたときの待ち時間の下限・上限（秒）
MIN_RATE_LIMIT_WAIT = 5.0
MAX_RATE_LIMIT_WAIT = 180.0
# 504などのときの初期待ち時間（秒）。再試行ごとに伸びる。
INITIAL_BACKOFF = 8.0
MAX_BACKOFF = 120.0

MAX_ROUTE = 507
# 59〜100号は欠番（高速道路等に振り替えられた）
MISSING_NUMBERS = set(range(59, 101))

# 地図に描くときの間引き量（度）。0.0015 ≒ 150m 相当。
SIMPLIFY_TOLERANCE = 0.0015

# 背景地図の初期設定。地図を開いてから右パネルで切り替えることもできる。
#   blank … 白地図（海岸線・行政界のみ。既定）
#   pale  … 淡色地図（地名・道路あり）
#   std   … 標準地図
#   photo … 空中写真
#   none  … 背景なし（国道だけを描く）
DEFAULT_BASEMAP = "blank"
# 背景の濃さ 0.0〜1.0。薄くするほど国道の線が目立つ。
BASEMAP_OPACITY = 0.55
# 未走破の国道を最初から表示するか
SHOW_TODO = True
# 線の色。未走破は白地図の市町村界（灰色の細線）と紛れないよう青にしている。
# 選択中の縁取りは、走破済み（赤）とも未走破（青）とも喧嘩しない琥珀色。
# 道の駅を最初から表示するか
SHOW_EKI = False
DONE_COLOR = "#d81f26"
TODO_COLOR = "#2f7fc7"
SELECT_COLOR = "#ffa000"
# 交差点名を最初から表示するか
SHOW_NODES = True
# 交差点の点を出し始めるズーム／名前を出し始めるズーム。
# 名前は重なり合わないものだけを選んで描くので、低いほど間引かれる。
NODE_MIN_ZOOM = 11
LABEL_MIN_ZOOM = 13
# 座標を突き合わせるときの丸め桁数。OSMの座標精度に合わせる。
COORD_PRECISION = 7
# グラフ上の隙間をどこまで繋ぐか [m]。OSM で隣り合う way の端点が数mずれたまま
# 接続されておらず、路線が分断されて見えることがある（国道158号 飛騨清見IC付近など）。
GAP_BRIDGE_M = 50.0
# 行き止まり「同士」が向かい合っているだけなら、もっと広い隙間も繋いでよい。
# 片方が道の途中だと立体交差を掴む危険があるが、両方が行き止まりならまず隙間。
GAP_BRIDGE_END_M = 300.0

PREFECTURES = [
    "北海道", "青森県", "岩手県", "宮城県", "秋田県", "山形県", "福島県",
    "茨城県", "栃木県", "群馬県", "埼玉県", "千葉県", "東京都", "神奈川県",
    "新潟県", "富山県", "石川県", "福井県", "山梨県", "長野県", "岐阜県",
    "静岡県", "愛知県", "三重県", "滋賀県", "京都府", "大阪府", "兵庫県",
    "奈良県", "和歌山県", "鳥取県", "島根県", "岡山県", "広島県", "山口県",
    "徳島県", "香川県", "愛媛県", "高知県", "福岡県", "佐賀県", "長崎県",
    "熊本県", "大分県", "宮崎県", "鹿児島県", "沖縄県",
]

# 地点の種類（地図の描き分けと、区間欄に書ける名前の由来）
KIND_PLAIN = 0      # OSM の名前付きノード（信号なし）
KIND_SIGNAL = 1     # OSM の信号交差点
KIND_CROSS = 2      # 国道どうしの交点（こちらで算出）
KIND_END = 3        # 路線の端（こちらで算出）
# 同じ交差点が数m刻みで何点も立つので、この距離以内の同名はまとめる [km]
CROSS_MERGE_KM = 0.15
# 同じ地点に複数の呼び名が付くときの区切り。区間欄にはどちらの名前でも書ける
# （`match_named_nodes` の部分一致で拾える）ので、この文字は名前に使わないこと。
NAME_SEP = "／"

FULL = "全線"
# 交差点区間の区切り文字
SEPARATORS = "〜～~－―-–—→"
SEP_RE = re.compile(f"[{re.escape(SEPARATORS)}]")


# --------------------------------------------------------------------------
# 幾何計算
# --------------------------------------------------------------------------

def haversine_km(lat1, lon1, lat2, lon2):
    r = 6371.0
    p1, p2 = math.radians(lat1), math.radians(lat2)
    a = (math.sin((p2 - p1) / 2) ** 2
         + math.cos(p1) * math.cos(p2) * math.sin(math.radians(lon2 - lon1) / 2) ** 2)
    return 2 * r * math.asin(math.sqrt(a))


def seg_km(p, q):
    """[lon, lat] 同士の距離 [km]"""
    return haversine_km(p[1], p[0], q[1], q[0])


def node_key(p):
    """座標を突き合わせ用のキーにする。同じOSMノードなら必ず一致する。"""
    return (round(p[0], COORD_PRECISION), round(p[1], COORD_PRECISION))


def edge_key(a, b):
    """向きに依存しない辺のキー"""
    return (a, b) if a <= b else (b, a)


def simplify(coords, tol):
    """Douglas-Peucker による間引き。coords は [[lon, lat], ...]"""
    if len(coords) < 3:
        return coords
    scale = math.cos(math.radians(coords[0][1])) or 1.0

    def perp(p, a, b):
        px, py = (p[0] - a[0]) * scale, p[1] - a[1]
        bx, by = (b[0] - a[0]) * scale, b[1] - a[1]
        d2 = bx * bx + by * by
        if d2 == 0:
            return math.hypot(px, py)
        t = max(0.0, min(1.0, (px * bx + py * by) / d2))
        return math.hypot(px - t * bx, py - t * by)

    keep = [False] * len(coords)
    keep[0] = keep[-1] = True
    stack = [(0, len(coords) - 1)]
    while stack:
        s, e = stack.pop()
        if e <= s + 1:
            continue
        far_i, far_d = -1, 0.0
        for i in range(s + 1, e):
            d = perp(coords[i], coords[s], coords[e])
            if d > far_d:
                far_i, far_d = i, d
        if far_d > tol:
            keep[far_i] = True
            stack.append((s, far_i))
            stack.append((far_i, e))
    return [c for c, k in zip(coords, keep) if k]


# --------------------------------------------------------------------------
# Overpass
# --------------------------------------------------------------------------

class FetchError(Exception):
    """1つの取得対象が今回は取れなかった。全体は止めない。"""


class OverpassClient:
    """混雑に合わせて自分で速度を落とすOverpassクライアント。

    - 429（レート制限）を受けたら /api/status に空き時刻を聞いて，その分だけ待つ
    - 504（サーバ側タイムアウト）は待ち時間を倍にしながら別のミラーへ回す
    - 失敗が続いたミラーはしばらく使わない
    """

    def __init__(self, verbose=True):
        self.endpoints = [{"url": u, "rest_until": 0.0, "fails": 0} for u in OVERPASS_ENDPOINTS]
        self.interval = REQUEST_INTERVAL
        self.last_call = 0.0
        self.verbose = verbose

    # -- 表示 -------------------------------------------------------------
    def _say(self, text):
        if self.verbose:
            print(text, file=sys.stderr)

    # -- 速度調整 ---------------------------------------------------------
    def _slow_down(self):
        self.interval = min(self.interval * 1.6, MAX_INTERVAL)

    def _speed_up(self):
        # 混雑が解けたら早めに元の速度へ戻す
        self.interval = max(self.interval * 0.6, REQUEST_INTERVAL)

    def _wait_turn(self):
        gap = self.interval - (time.time() - self.last_call)
        if gap > 0:
            time.sleep(gap)

    # -- ミラー選択 -------------------------------------------------------
    def _pick(self):
        now = time.time()
        ready = [e for e in self.endpoints if e["rest_until"] <= now]
        if ready:
            return min(ready, key=lambda e: e["fails"])
        # 全部休養中なら，いちばん早く空くものを待つ
        soonest = min(self.endpoints, key=lambda e: e["rest_until"])
        wait = max(0.0, soonest["rest_until"] - now)
        if wait > 0:
            self._say(f"    どのミラーも混雑中。{wait:.0f}秒待ちます")
            time.sleep(wait)
        return soonest

    def _slot_wait(self, endpoint):
        """/api/status に空きスロットの時刻を聞く。分からなければ None。"""
        url = endpoint["url"].rsplit("/", 1)[0] + "/status"
        try:
            with urllib.request.urlopen(url, timeout=30) as res:
                text = res.read().decode("utf-8", "replace")
        except Exception:
            return None
        if re.search(r"slots? available now", text, re.I):
            return 0.0
        secs = [int(m) for m in re.findall(r"in (\d+) seconds", text)]
        return float(min(secs)) if secs else None

    # -- 本体 -------------------------------------------------------------
    def query(self, build_query, attempts=ATTEMPTS_PER_TARGET):
        """build_query(timeout) -> Overpass QL 文字列。結果のJSONを返す。"""
        backoff = INITIAL_BACKOFF
        timeout = 180
        last = None

        for attempt in range(1, attempts + 1):
            endpoint = self._pick()
            self._wait_turn()
            req = urllib.request.Request(
                endpoint["url"],
                data=build_query(timeout).encode("utf-8"),
                headers={"Content-Type": "text/plain; charset=utf-8",
                         "Accept": "application/json",
                         "User-Agent": "kokudo-map/2.1 (personal hobby map)"},
            )
            try:
                with urllib.request.urlopen(req, timeout=timeout + 120) as res:
                    data = json.loads(res.read().decode("utf-8"))
                self.last_call = time.time()
                endpoint["fails"] = 0
                self._speed_up()
                return data

            except urllib.error.HTTPError as e:
                self.last_call = time.time()
                last = e
                endpoint["fails"] += 1
                self._slow_down()

                if e.code == 429:
                    wait = self._slot_wait(endpoint)
                    if wait is None:
                        header = e.headers.get("Retry-After") if e.headers else None
                        wait = float(header) if (header or "").isdigit() else backoff
                    wait = min(max(wait, MIN_RATE_LIMIT_WAIT), MAX_RATE_LIMIT_WAIT) + random.uniform(0, 3)
                    endpoint["rest_until"] = time.time() + wait
                    self._say(f"    混雑のため待機中（{wait:.0f}秒）")
                    continue

                if e.code in (502, 503, 504):
                    # サーバ側が重い。少し長めの制限時間で別のミラーへ回す
                    endpoint["rest_until"] = time.time() + backoff
                    timeout = min(timeout * 2, 900)
                    self._say(f"    サーバが応答しません（{e.code}）。"
                              f"別のミラーで再試行します")
                    time.sleep(backoff * random.uniform(0.8, 1.2))
                    backoff = min(backoff * 1.8, MAX_BACKOFF)
                    continue

                self._say(f"    エラー {e.code}。再試行します")
                time.sleep(backoff)
                backoff = min(backoff * 1.8, MAX_BACKOFF)

            except (urllib.error.URLError, TimeoutError, json.JSONDecodeError, OSError) as e:
                self.last_call = time.time()
                last = e
                endpoint["fails"] += 1
                endpoint["rest_until"] = time.time() + backoff
                self._slow_down()
                self._say(f"    通信に失敗（{e}）。再試行します")
                time.sleep(backoff * random.uniform(0.8, 1.2))
                backoff = min(backoff * 1.8, MAX_BACKOFF)

        raise FetchError(str(last))


CLIENT = OverpassClient()


# 旧道（現役の国道でなくなった区間）を名前で除くための表現。
# 「国道158号旧道」「国道4号　旧仙台市街区間」「国道18号上新バイパス以前」など。
OLD_ROAD_PATTERN = "(旧|以前)"


def rel_clause(ref):
    """路線を構成するリレーションを .r に集める Overpass QL の断片。

    OSM 日本では本線リレーションに ref が付いていないものが多い
    （例: 国道290号は network=JP:national だが ref なし）。番号一致だけで引くと
    ref を持つバイパスの断片しか取れず，地図が途切れ途切れになる。
    そのため番号一致と名称一致の和を採る。
    """
    base = 'rel["type"="route"]["route"="road"]'
    return (f'(\n'
            f'  {base}["network"="JP:national"]["ref"~"^{ref}$"];\n'
            f'  {base}["name"~"^国道{ref}号"];\n'
            f');\n'
            f'rel._["name"!~"{OLD_ROAD_PATTERN}"]->.r;')


def query_full(ref):
    def build(timeout):
        return f"""[out:json][timeout:{timeout}];
{rel_clause(ref)}
way(r.r);
out geom;"""
    return build


def query_in_pref(ref, pref):
    def build(timeout):
        return f"""[out:json][timeout:{timeout}];
area["admin_level"="4"]["name"="{pref}"]->.a;
{rel_clause(ref)}
way(r.r)(area.a);
out geom;"""
    return build


def query_in_city(ref, pref, city):
    def build(timeout):
        return f"""[out:json][timeout:{timeout}];
area["admin_level"="4"]["name"="{pref}"]->.p;
rel(area.p)["boundary"="administrative"]["admin_level"~"^(7|8)$"]["name"="{city}"];
map_to_area->.c;
{rel_clause(ref)}
way(r.r)(area.c);
out geom;"""
    return build


def query_named_nodes(ref):
    def build(timeout):
        return f"""[out:json][timeout:{timeout}];
{rel_clause(ref)}
way(r.r)->.w;
node(w.w)["name"];
out;"""
    return build


def query_michinoeki(pref):
    """1都道府県ぶんの道の駅。

    OSM 日本では道の駅は highway=services（一部 rest_area）が定着している。
    駅の中の売店・駐車場・バス停にも「道の駅◯◯」という名前が付いていることが
    多いので、この2つのタグに絞らないと同じ駅を何度も拾ってしまう。
    """
    def build(timeout):
        return f"""[out:json][timeout:{timeout}];
area["admin_level"="4"]["name"="{pref}"]->.a;
nwr(area.a)["highway"~"^(services|rest_area)$"]["name"~"道の駅"];
out tags center;"""
    return build


def extract_michinoeki(result, pref):
    """道の駅の名前と位置。同じ駅の重複マッピングはまとめる。"""
    found = []
    for el in result.get("elements", []):
        tags = el.get("tags", {})
        name = tags.get("name")
        if not name:
            continue
        lat, lon = el.get("lat"), el.get("lon")
        if lat is None:
            center = el.get("center") or {}
            lat, lon = center.get("lat"), center.get("lon")
        if lat is None:
            continue
        found.append({"name": eki_name(name), "lat": lat, "lon": lon, "pref": pref})

    # 同名で近いものは同じ駅とみなす（ノードとエリアの二重登録が多い）
    merged = []
    for s in found:
        same = next((m for m in merged if m["name"] == s["name"]
                     and haversine_km(m["lat"], m["lon"], s["lat"], s["lon"]) < 1.0), None)
        if same is None:
            merged.append(s)
    return merged


def eki_name(name):
    """「道の駅　あおき」→「あおき」。全角空白や表記ゆれを落とす。"""
    n = norm_name(name)
    return n[3:] if n.startswith("道の駅") else n


def extract_ways(result):
    ways = {}
    for el in result.get("elements", []):
        if el.get("type") == "way" and el.get("geometry"):
            ways[str(el["id"])] = [[p["lon"], p["lat"]] for p in el["geometry"]]
    return ways


def extract_nodes(result):
    nodes = []
    for el in result.get("elements", []):
        if el.get("type") != "node":
            continue
        tags = el.get("tags", {})
        name = tags.get("name")
        if not name:
            continue
        nodes.append({
            "name": name,
            "lon": el["lon"],
            "lat": el["lat"],
            "signals": tags.get("highway") == "traffic_signals" or tags.get("junction") == "yes",
        })
    return nodes


# --------------------------------------------------------------------------
# キャッシュ
# --------------------------------------------------------------------------

def safe_name(text):
    return re.sub(r'[\\/:*?"<>|]', "_", text)


def route_cache_path(ref):
    return os.path.join(CACHE_DIR, f"r{ref}.json")


def area_cache_path(ref, area):
    return os.path.join(AREA_DIR, f"r{ref}@{safe_name(area)}.json")


def node_cache_path(ref):
    return os.path.join(NODE_DIR, f"r{ref}.json")


def load_json(path):
    if not os.path.exists(path):
        return None
    with open(path, encoding="utf-8") as f:
        return json.load(f)


def save_json(path, data):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False)


def fetch_route(ref, force=False):
    """路線全体の形状"""
    path = route_cache_path(ref)
    if os.path.exists(path) and not force:
        return False
    ways = extract_ways(CLIENT.query(query_full(ref)))
    save_json(path, {"ref": ref, "ways": ways})
    if ways:
        km = sum(sum(seg_km(c[i], c[i + 1]) for i in range(len(c) - 1)) for c in ways.values())
        print(f"    {len(ways)} 区間 / 約 {km:.0f} km")
    else:
        print("    データなし（欠番、またはOSM未整備）")
    return True


def fetch_area(ref, area, force=False):
    """路線のうち，ある都道府県／市町村に入る部分の形状"""
    path = area_cache_path(ref, area)
    if os.path.exists(path) and not force:
        return False
    pref, city = split_area(area)
    query = (query_in_city(ref, pref, city) if city else query_in_pref(ref, pref))
    ways = extract_ways(CLIENT.query(query))
    save_json(path, {"ref": ref, "area": area, "ways": ways})
    if ways:
        print(f"    {len(ways)} 区間")
    else:
        print(f"    データなし。「{area}」の綴りと，その市町村を国道{ref}号が通るか確認してください。")
    return True


def fetch_nodes(ref, force=False):
    """路線上の名前付きノード（交差点名）"""
    path = node_cache_path(ref)
    if os.path.exists(path) and not force:
        return False
    nodes = extract_nodes(CLIENT.query(query_named_nodes(ref)))
    save_json(path, {"ref": ref, "nodes": nodes})
    print(f"    {len(nodes)} 個の名前付き地点")
    return True


def eki_cache_path(pref):
    return os.path.join(EKI_DIR, f"{safe_name(pref)}.json")


def fetch_michinoeki(pref, force=False):
    path = eki_cache_path(pref)
    if os.path.exists(path) and not force:
        return False
    stations = extract_michinoeki(CLIENT.query(query_michinoeki(pref)), pref)
    save_json(path, {"pref": pref, "stations": stations})
    print(f"    {len(stations)} 駅")
    return True


def load_michinoeki():
    """取得済みの道の駅をすべて読む（都道府県順・県内は北から）"""
    out = []
    for pref in PREFECTURES:
        data = load_json(eki_cache_path(pref))
        if not data:
            continue
        out.extend(sorted(data.get("stations") or [], key=lambda s: -s["lat"]))
    return out


def split_area(area):
    """「新潟県長岡市」→ ('新潟県', '長岡市')，「新潟県」→ ('新潟県', None)"""
    for pref in PREFECTURES:
        if area == pref:
            return pref, None
        if area.startswith(pref):
            rest = area[len(pref):].strip()
            return pref, (rest or None)
    return area, None


def normalize_area(area):
    """区間欄の表記ゆれを吸収し，正しければ正規化した文字列を返す"""
    area = area.replace(" ", "").replace("　", "")
    pref, city = split_area(area)
    if pref not in PREFECTURES:
        return None
    return pref + (city or "")


# --------------------------------------------------------------------------
# 走破記録 (routes.csv)
# --------------------------------------------------------------------------

SAMPLE_CSV = """路線番号,区間,走破日,メモ
17,全線,2024-05-03,
8,新潟県,2023-08-11,親不知
8,富山県高岡市,2023-08-12,
116,新潟県長岡市,,
351,宮内〜与板橋,,交差点名で指定した例
"""


def cmd_init(args):
    if os.path.exists(CSV_PATH) and not args.force:
        print(f"{CSV_PATH} はすでにあります。作り直すなら --force を付けてください。")
        return
    with open(CSV_PATH, "w", encoding="utf-8-sig", newline="") as f:
        f.write(SAMPLE_CSV)
    print(f"{CSV_PATH} を作りました。")
    print("区間欄には「全線」「都道府県名」「都道府県名＋市町村名」「交差点A〜交差点B」が書けます。")


def parse_section(text):
    """区間欄の1項目を {"kind": ..., ...} に変換する"""
    text = text.strip()
    if not text or text == FULL:
        return {"kind": "full"}

    parts = [p.strip() for p in SEP_RE.split(text)]
    if len(parts) == 2 and all(parts):
        return {"kind": "nodes", "a": parts[0], "b": parts[1], "label": text}

    area = normalize_area(text)
    if area:
        pref, city = split_area(area)
        return {"kind": "area", "area": area, "label": area,
                "level": "city" if city else "pref"}
    return None


def parse_row(raw_ref, raw_section, date, note, line_no=0, quiet=False):
    """routes.csv の1行を、区間指定の並びに変える。

    `新潟県/富山県` のようなまとめ書きは複数に分かれる。
    `read_records()`（全体の読み込み）と `serve`（1行だけの下見）で共用する。
    """
    ref = (raw_ref or "").strip().lstrip("Rr国道").rstrip("号").strip()
    if not ref.isdigit():
        if not quiet:
            print(f"  {line_no}行目: 路線番号「{raw_ref}」を読めないので飛ばします",
                  file=sys.stderr)
        return []

    text = (raw_section or FULL).strip() or FULL
    # 交差点指定は分解しない
    items = ([text] if SEP_RE.search(text)
             else [p.strip() for p in text.replace("・", "/").split("/") if p.strip()])

    out = []
    for item in items:
        sec = parse_section(item)
        if sec is None:
            if not quiet:
                print(f"  {line_no}行目: 区間「{item}」を解釈できません。"
                      f"都道府県名から書くか，交差点名を「A〜B」の形にしてください。",
                      file=sys.stderr)
            continue
        sec.update({"ref": ref, "date": date, "note": note, "line": line_no})
        out.append(sec)
    return out


def read_records():
    if not os.path.exists(CSV_PATH):
        print(f"{CSV_PATH} がありません。先に `python kokudo_map.py init` を実行してください。",
              file=sys.stderr)
        sys.exit(1)

    records = []
    with open(CSV_PATH, encoding="utf-8-sig", newline="") as f:
        for line_no, row in enumerate(csv.DictReader(f), start=2):
            if not (row.get("路線番号") or "").strip():
                continue
            records.extend(parse_row(row.get("路線番号"),
                                     row.get("区間"),
                                     (row.get("走破日") or "").strip(),
                                     (row.get("メモ") or "").strip(),
                                     line_no))
    return records


EKI_HEADER = ["都道府県", "道の駅", "訪問日", "メモ"]


def read_eki_records():
    """michinoeki.csv を読む。{(都道府県, 正規化した駅名): {...}}"""
    if not os.path.exists(EKI_CSV_PATH):
        return {}
    out = {}
    with open(EKI_CSV_PATH, encoding="utf-8-sig", newline="") as f:
        for row in csv.DictReader(f):
            name = (row.get("道の駅") or "").strip()
            if not name:
                continue
            out[((row.get("都道府県") or "").strip(), eki_name(name))] = {
                "date": (row.get("訪問日") or "").strip(),
                "note": (row.get("メモ") or "").strip(),
            }
    return out


def sync_eki_csv(stations):
    """未記載の道の駅を michinoeki.csv に足す。既存の行には触れない。"""
    known = read_eki_records()
    missing = [s for s in stations if (s["pref"], s["name"]) not in known]
    if not missing and os.path.exists(EKI_CSV_PATH):
        return 0

    rows = []
    for s in stations:
        rec = known.get((s["pref"], s["name"]), {})
        rows.append({"都道府県": s["pref"], "道の駅": s["name"],
                     "訪問日": rec.get("date", ""), "メモ": rec.get("note", "")})
    # CSV にしか無い行（自分で足した駅など）も残す
    listed = {(s["pref"], s["name"]) for s in stations}
    for (pref, name), rec in known.items():
        if (pref, name) not in listed:
            rows.append({"都道府県": pref, "道の駅": name,
                         "訪問日": rec["date"], "メモ": rec["note"]})

    with open(EKI_CSV_PATH, "w", encoding="utf-8-sig", newline="") as f:
        w = csv.DictWriter(f, fieldnames=EKI_HEADER)
        w.writeheader()
        w.writerows(rows)
    return len(missing)


def build_eki():
    """地図に載せる道の駅。[緯度, 経度, 名前, 都道府県, 訪問済みか, メモ]"""
    stations = load_michinoeki()
    if not stations:
        return [], 0
    added = sync_eki_csv(stations)
    visited = read_eki_records()
    out = []
    for s in stations:
        rec = visited.get((s["pref"], s["name"]), {})
        been = bool(rec.get("date"))
        out.append([round(s["lat"], 5), round(s["lon"], 5), s["name"], s["pref"],
                    1 if been else 0, rec.get("date", ""), rec.get("note", "")])
    return out, added


# --------------------------------------------------------------------------
# 区間指定に使える地点を増やす
# --------------------------------------------------------------------------
#
# OSM に名前の付いた交差点は偏っていて、37路線は4個以下しかない。
# 名前に頼らず区間を切れるよう、手持ちの形状から次の2種類を算出して足す。
#   - 国道どうしの交点（全国 4,340 箇所）
#   - 路線の端（1路線に2つ）
# さらに区間欄には `@緯度,経度` と直接書ける（`nearest()` で吸着させる）。


def _pack(key):
    """node_key を1つの整数にする。交点の集計で辞書を軽くするため。"""
    return int(round(key[0] * 1e7)) * (1 << 32) + int(round(key[1] * 1e7))


def cache_signature(refs):
    """路線キャッシュが変わったかを見る印"""
    sig = []
    for ref in refs:
        path = route_cache_path(ref)
        if os.path.exists(path):
            sig.append(f"{ref}:{os.path.getsize(path)}")
    return "|".join(sig)


def build_junction_index(refs, quiet=False):
    """国道どうしの交点を求める。{packされた座標: (路線番号, ...)}

    2本以上が通るノードのうち、隣のノードと路線の組み合わせが変わる境目だけを
    採る。こうしないと重複区間の途中が丸ごと交点になってしまう。
    """
    cached = load_json(JUNCTION_PATH)
    sig = cache_signature(refs)
    if cached and cached.get("signature") == sig:
        return {int(k): tuple(v) for k, v in cached["junctions"].items()}

    if not quiet:
        print("  国道どうしの交点を算出しています…（初回のみ）", file=sys.stderr)

    seen = defaultdict(int)
    for ref in refs:
        ways = (load_json(route_cache_path(ref)) or {}).get("ways") or {}
        nodes = {_pack(node_key(c)) for coords in ways.values() for c in coords}
        for n in nodes:
            seen[n] += 1
    shared = {n for n, c in seen.items() if c >= 2}
    del seen

    node_refs = defaultdict(list)
    adj = defaultdict(set)
    for ref in refs:
        ways = (load_json(route_cache_path(ref)) or {}).get("ways") or {}
        for coords in ways.values():
            prev = None
            for c in coords:
                n = _pack(node_key(c))
                if n in shared:
                    node_refs[n].append(ref)
                if prev is not None and (prev in shared or n in shared):
                    adj[prev].add(n)
                    adj[n].add(prev)
                prev = n

    combos = {n: tuple(sorted(set(rs), key=int)) for n, rs in node_refs.items()}
    junctions = {n: rs for n, rs in combos.items()
                 if len(rs) >= 2 and any(combos.get(q, ()) != rs for q in adj.get(n, ()))}

    save_json(JUNCTION_PATH, {"signature": sig,
                              "junctions": {str(k): list(v) for k, v in junctions.items()}})
    if not quiet:
        print(f"  国道どうしの交点 {len(junctions):,} 箇所", file=sys.stderr)
    return junctions


def derived_nodes(ref, graph, node_dist, junctions):
    """その路線で使える、こちらで算出した地点"""
    out = []

    # 交差点の分岐は数m刻みで何点も立つことがあるので、同名で近いものはまとめる
    found = []
    for key in sorted(graph.adj):
        rs = junctions.get(_pack(key))
        if not rs or ref not in rs:
            continue
        name = "×".join(f"R{r}" for r in rs)
        if any(n == name and haversine_km(key[1], key[0], la, lo) < CROSS_MERGE_KM
               for n, la, lo in found):
            continue
        found.append((name, key[1], key[0]))
        out.append({"name": name, "lat": key[1], "lon": key[0], "kind": KIND_CROSS})

    ends = route_ends(graph, node_dist)
    for key, label in ends:
        out.append({"name": f"R{ref}端({label})", "lat": key[1], "lon": key[0],
                    "kind": KIND_END})
    return out


def route_ends(graph, node_dist):
    """路線の両端。向き（北/南/東/西）を付けて区別できるようにする。"""
    if not node_dist:
        return []
    start = min(node_dist, key=lambda k: node_dist[k])
    far = max(node_dist, key=lambda k: node_dist[k])
    if start == far:
        return []
    dlat, dlon = far[1] - start[1], far[0] - start[0]
    if abs(dlat) >= abs(dlon):
        a, b = ("南", "北") if dlat > 0 else ("北", "南")
    else:
        a, b = ("西", "東") if dlon > 0 else ("東", "西")
    return [(start, a), (far, b)]


# --------------------------------------------------------------------------
# 経路グラフ
# --------------------------------------------------------------------------

class RouteGraph:
    """1路線の道路網。座標が一致するノードで繋がっているとみなす。"""

    def __init__(self, ways):
        self.adj = defaultdict(list)
        self.edges = {}
        for coords in ways.values():
            for i in range(len(coords) - 1):
                a, b = node_key(coords[i]), node_key(coords[i + 1])
                if a == b:
                    continue
                key = edge_key(a, b)
                if key not in self.edges:
                    self.edges[key] = seg_km(coords[i], coords[i + 1])
                    d = self.edges[key]
                    self.adj[a].append((b, d, key))
                    self.adj[b].append((a, d, key))
        self.bridged = self._bridge_gaps()

    def _bridge_gaps(self):
        """way が繋がっていないだけの隙間を埋める。2段階でやる。

        1. 行き止まり（次数1）から `GAP_BRIDGE_M` 以内の任意のノードへ。
           T字路の取りこぼしを拾うが、立体交差を掴まないよう距離は短く抑える。
        2. 行き止まり「同士」なら `GAP_BRIDGE_END_M` まで。向かい合った端点は
           まず未接続の隙間なので、広めに見てよい。

        繋いだ本数を返す。
        """
        if not self.adj:
            return 0

        parent = {k: k for k in self.adj}

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        for a, b in self.edges:
            ra, rb = find(a), find(b)
            if ra != rb:
                parent[ra] = rb

        def link(a, b, d):
            key = edge_key(a, b)
            self.edges[key] = d
            self.adj[a].append((b, d, key))
            self.adj[b].append((a, d, key))
            parent[find(a)] = find(b)

        made = 0

        # -- 1段目: 行き止まり → 任意のノード -----------------------------
        limit = GAP_BRIDGE_M / 1000.0
        cell = limit / 111.0 * 2
        grid = defaultdict(list)
        for k in self.adj:
            grid[(int(k[1] / cell), int(k[0] / cell))].append(k)

        for e in sorted(k for k, v in self.adj.items() if len(v) == 1):
            gy, gx = int(e[1] / cell), int(e[0] / cell)
            best, best_d = None, limit
            for dy in (-1, 0, 1):
                for dx in (-1, 0, 1):
                    for k in grid.get((gy + dy, gx + dx), ()):
                        if find(k) == find(e):
                            continue
                        d = haversine_km(e[1], e[0], k[1], k[0])
                        if d < best_d:
                            best, best_d = k, d
            if best is not None:
                link(e, best, best_d)
                made += 1

        # -- 2段目: 行き止まり同士 ----------------------------------------
        ends = sorted(k for k, v in self.adj.items() if len(v) == 1)
        if 1 < len(ends) <= 3000:
            limit2 = GAP_BRIDGE_END_M / 1000.0
            pairs = []
            for i, a in enumerate(ends):
                for b in ends[i + 1:]:
                    if find(a) == find(b):
                        continue
                    d = haversine_km(a[1], a[0], b[1], b[0])
                    if d <= limit2:
                        pairs.append((d, a, b))
            for d, a, b in sorted(pairs):
                if find(a) != find(b):
                    link(a, b, d)
                    made += 1

        return made

    def total_km(self):
        return sum(self.edges.values())

    def nearest(self, lon, lat):
        """指定座標に対応するグラフ上のノード。交差点ノードは道路の構成点なので通常は完全一致する。"""
        key = node_key([lon, lat])
        if key in self.adj:
            return key
        best, best_d = None, float("inf")
        for k in self.adj:
            d = (k[0] - lon) ** 2 + ((k[1] - lat) * 1.2) ** 2
            if d < best_d:
                best, best_d = k, d
        return best

    def dijkstra(self, start, goals):
        """start から各ノードへの最短距離と直前ノードを返す"""
        dist = {start: 0.0}
        prev = {}
        goals = set(goals)
        found = set()
        pq = [(0.0, start)]
        while pq:
            d, u = heapq.heappop(pq)
            if d > dist.get(u, float("inf")):
                continue
            if u in goals:
                found.add(u)
                if found >= goals:
                    break
            for v, w, key in self.adj[u]:
                nd = d + w
                if nd < dist.get(v, float("inf")):
                    dist[v] = nd
                    prev[v] = (u, key)
                    heapq.heappush(pq, (nd, v))
        return dist, prev

    def path_edges(self, start, goal):
        """start→goal の最短経路が通る辺の集合と距離"""
        dist, prev = self.dijkstra(start, [goal])
        if goal not in dist:
            return None, None
        edges = set()
        cur = goal
        while cur != start:
            cur, key = prev[cur]
            edges.add(key)
        return edges, dist[goal]

    def terminals(self):
        """端点（接続が1本だけのノード）"""
        return [k for k, v in self.adj.items() if len(v) == 1]

    def components(self):
        """連結成分をノードの集合として並べる"""
        seen = set()
        for start in self.adj:
            if start in seen:
                continue
            stack, comp = [start], set()
            seen.add(start)
            while stack:
                u = stack.pop()
                comp.add(u)
                for v, _, _ in self.adj[u]:
                    if v not in seen:
                        seen.add(v)
                        stack.append(v)
            yield comp

    def component_gap_km(self, a, b):
        """a と b が属するかたまりの、いちばん近い所どうしの距離 [km]"""
        comps = list(self.components())
        ca = next((c for c in comps if a in c), None)
        cb = next((c for c in comps if b in c), None)
        if ca is None or cb is None or ca is cb:
            return None
        small, large = (ca, cb) if len(ca) <= len(cb) else (cb, ca)
        return min(haversine_km(p[1], p[0], q[1], q[0]) for p in small for q in large)

    def far_end(self):
        """路線の端らしいノードを1つ選ぶ（一覧を起点側から並べるのに使う）

        バイパスの断片など小さな塊を起点にすると路線の大半に距離が付かないので、
        いちばん大きな連結成分の中から選ぶ。
        """
        if not self.adj:
            return None
        main = max(self.components(), key=len)
        ends = [k for k in main if len(self.adj[k]) == 1] or list(main)
        seed = min(ends)
        dist, _ = self.dijkstra(seed, [])
        reachable = [(dist[e], e) for e in ends if e in dist]
        return max(reachable)[1] if reachable else seed


def norm_name(text):
    """交差点名の表記ゆれを吸収する。

    「長沢（西）」と「長沢(西)」、「渚１丁目」と「渚1丁目」を同じものとして扱う。
    手で書く区間欄と OSM の表記が全角／半角で食い違うことが多い。
    """
    return unicodedata.normalize("NFKC", text).replace(" ", "").replace("　", "")


# 「@37.4056,138.8087」のように、名前ではなく座標で区間端を指定する書き方
COORD_ONLY_RE = re.compile(
    r"^@?\s*(\d+(?:\.\d+)?)\s*[,/]\s*(\d+(?:\.\d+)?)\s*$")


def endpoint_candidates(nodes, text, graph, dist):
    """区間端の候補。座標で書かれていれば最寄りのノードに吸着させる。"""
    m = COORD_ONLY_RE.match(text.strip())
    if m:
        lat, lon = float(m.group(1)), float(m.group(2))
        return [{"name": text.strip(), "lat": lat, "lon": lon, "kind": KIND_PLAIN}]
    return match_named_nodes(nodes, text, graph, dist)


def match_named_nodes(nodes, query, graph=None, dist=None):
    """交差点名の候補を返す。

    「本町@104.6」のように @ のあとに起点からのキロ程を書くと，そこに近いものだけに絞る。
    「本町@37.4056,138.8087」のように緯度経度でも指定できる。
    """
    q = query.strip()
    hint = None
    if "@" in q:
        q, _, hint = (x.strip() for x in q.partition("@"))

    variants = [norm_name(q), norm_name(q.replace("交差点", ""))]
    names = [(n, norm_name(n["name"])) for n in nodes]
    hits = []
    for v in variants:
        hits = [n for n, nm in names if nm == v]
        if hits:
            break
    if not hits:
        for v in variants:
            hits = [n for n, nm in names if v and v in nm]
            if hits:
                break
    if not hits or not hint:
        return hits

    if "," in hint or "/" in hint:  # 緯度,経度（CSVを壊さないよう / でもよい）
        try:
            lat, lon = (float(x) for x in re.split(r"[,/]", hint, maxsplit=1))
        except ValueError:
            return hits
        return [min(hits, key=lambda n: (n["lat"] - lat) ** 2 + (n["lon"] - lon) ** 2)]

    try:  # 起点からのキロ程
        target = float(hint.rstrip("kmKM"))
    except ValueError:
        return hits
    if graph is None or dist is None:
        return hits
    scored = [(abs(dist.get(graph.nearest(n["lon"], n["lat"]), 1e9) - target), n) for n in hits]
    return [min(scored, key=lambda t: t[0])[1]]


def resolve_node_section(graph, nodes, sec, ref, dist=None):
    """「A〜B」を辺の集合に変換する"""
    cand_a = endpoint_candidates(nodes, sec["a"], graph, dist)
    cand_b = endpoint_candidates(nodes, sec["b"], graph, dist)

    for label, name, cands in (("A", sec["a"], cand_a), ("B", sec["b"], cand_b)):
        if not cands:
            print(f"  国道{ref}号: 地点「{name}」が見つかりません。"
                  f"地図で名前を確かめるか、`@緯度,経度` の形で場所を直接書いてください。",
                  file=sys.stderr)
            return None, None

    # 候補が複数あるときは，経路がいちばん短くなる組み合わせを採る
    best = None
    for na in cand_a:
        ka = graph.nearest(na["lon"], na["lat"])
        for nb in cand_b:
            kb = graph.nearest(nb["lon"], nb["lat"])
            if ka == kb:
                continue
            edges, dist = graph.path_edges(ka, kb)
            if edges is not None and (best is None or dist < best[1]):
                best = (edges, dist)

    if best is None:
        gap = graph.component_gap_km(graph.nearest(cand_a[0]["lon"], cand_a[0]["lat"]),
                                     graph.nearest(cand_b[0]["lon"], cand_b[0]["lat"]))
        detail = (f"2点は別々のかたまりに属しています（隙間は約 {gap * 1000:.0f} m）。"
                  if gap is not None and gap < 0.2 else
                  f"2点は別々のかたまりに属しています（隙間は約 {gap:.1f} km）。"
                  if gap is not None else "")
        print(f"  国道{ref}号: 「{sec['label']}」を繋ぐ経路が見つかりません。{detail}"
              f"海上区間や未開通区間で路線が分断されている可能性があります。", file=sys.stderr)
        return None, None

    if len(cand_a) > 1 or len(cand_b) > 1:
        print(f"  国道{ref}号: 「{sec['label']}」は同名の地点が複数あるため，"
              f"最短になる組み合わせ（{best[1]:.1f} km）を採用しました。", file=sys.stderr)
        print(f"    意図と違う場合は「本町@104.6」のようにキロ程を，"
              f"または「本町@37.4056,138.8087」のように緯度経度を添えてください。", file=sys.stderr)
    return best


# --------------------------------------------------------------------------
# fetch
# --------------------------------------------------------------------------

def collect_targets(args):
    """取得すべきものを (種別, 路線番号, 付加情報, 表示名) の並びにする

    交差点名は地図の注記にも使うので，形状と同じ範囲ぶん取る。
    """
    if args.all:
        refs = [str(n) for n in range(1, MAX_ROUTE + 1) if n not in MISSING_NUMBERS]
        return ([("route", r, None, f"国道{r}号") for r in refs]
                + [("nodes", r, None, f"国道{r}号 の交差点名") for r in refs]
                + eki_targets())

    records = read_records()
    refs = sorted({r["ref"] for r in records}, key=int)
    targets = [("route", ref, None, f"国道{ref}号") for ref in refs]
    for ref, area in sorted({(r["ref"], r["area"]) for r in records if r["kind"] == "area"}):
        targets.append(("area", ref, area, f"国道{ref}号（{area}）"))
    targets += [("nodes", ref, None, f"国道{ref}号 の交差点名") for ref in refs]
    targets += eki_targets()
    return targets


def eki_targets():
    return [("michinoeki", None, pref, f"道の駅（{pref}）") for pref in PREFECTURES]


def is_cached(kind, ref, extra):
    path = {"route": lambda: route_cache_path(ref),
            "area": lambda: area_cache_path(ref, extra),
            "nodes": lambda: node_cache_path(ref),
            "michinoeki": lambda: eki_cache_path(extra)}[kind]()
    return os.path.exists(path)


def run_target(kind, ref, extra, force):
    if kind == "route":
        return fetch_route(ref, force)
    if kind == "area":
        return fetch_area(ref, extra, force)
    if kind == "michinoeki":
        return fetch_michinoeki(extra, force)
    return fetch_nodes(ref, force)


def cmd_fetch(args):
    targets = collect_targets(args)
    todo = [t for t in targets if args.force or not is_cached(t[0], t[1], t[2])]
    done_already = len(targets) - len(todo)

    if not todo:
        print(f"{len(targets)} 件すべて取得済みです。")
        return

    print(f"取得対象 {len(todo)} 件"
          + (f"（{done_already} 件は取得済みなので飛ばします）" if done_already else ""))
    print("混雑したら自動で待つので，そのまま放っておいて構いません。"
          " 中断しても取得済みぶんは残ります。\n")

    started = time.time()
    failures = {}

    for pass_no in range(1, MAX_PASSES + 1):
        if pass_no > 1:
            print(f"\n未取得が {len(todo)} 件残っています。"
                  f"{PASS_COOLDOWN:.0f}秒休んでから {pass_no} 巡目に入ります。")
            try:
                time.sleep(PASS_COOLDOWN)
            except KeyboardInterrupt:
                print("\n中断しました。取得済みぶんは残っています。")
                return

        retry = []
        got = 0
        total = len(todo)
        for i, (kind, ref, extra, label) in enumerate(todo, start=1):
            head = f"[{i}/{total}]" + (f"（{pass_no}巡目）" if pass_no > 1 else "")
            print(f"{head} {label} を取得中…")
            try:
                run_target(kind, ref, extra, args.force)
                failures.pop(label, None)
                got += 1
            except FetchError as e:
                failures[label] = str(e)
                retry.append((kind, ref, extra, label))
                print(f"    今回は取得できませんでした。あとでまとめて再試行します")
                # 立て続けに全滅するならOverpass側の障害。粘らずに切り上げる
                if got == 0 and len(retry) >= 5:
                    print("\n連続して取得できません。Overpass が停止しているか，"
                          "回線側の問題の可能性があります。")
                    print("しばらく時間をおいてから同じコマンドを実行してください。"
                          "取得済みぶんは残っています。")
                    return
            except KeyboardInterrupt:
                print("\n中断しました。取得済みぶんは残っています。"
                      "同じコマンドで続きから再開できます。")
                return

        todo = retry
        if not todo:
            break

    elapsed = (time.time() - started) / 60
    print(f"\n終了しました（{elapsed:.0f}分）。")
    if todo:
        print(f"{len(todo)} 件は取得できませんでした:")
        for _, _, _, label in todo[:20]:
            print(f"  - {label}")
        if len(todo) > 20:
            print(f"  … 他 {len(todo) - 20} 件")
        print("時間をおいて同じコマンドを実行すると，この分だけ取りにいきます。")
    else:
        print("すべて取得できました。`python kokudo_map.py build` で地図を作れます。")


# --------------------------------------------------------------------------
# nodes（交差点名の一覧）
# --------------------------------------------------------------------------

def cmd_nodes(args):
    ref = str(args.ref)
    try:
        fetch_route(ref)
        fetch_nodes(ref)
    except FetchError as e:
        print(f"Overpass から取得できませんでした（{e}）。"
              f"時間をおいて再実行してください。", file=sys.stderr)
        return
    except KeyboardInterrupt:
        print("\n中断しました。", file=sys.stderr)
        return

    ways = (load_json(route_cache_path(ref)) or {}).get("ways") or {}
    nodes = (load_json(node_cache_path(ref)) or {}).get("nodes") or []
    if not ways:
        print(f"国道{ref}号の形状がありません。", file=sys.stderr)
        return


    graph = RouteGraph(ways)
    start = graph.far_end()
    dist, _ = graph.dijkstra(start, [])

    cached_refs = sorted((n[1:-5] for n in os.listdir(CACHE_DIR)
                          if n.startswith("r") and n.endswith(".json")), key=int)
    nodes = nodes + derived_nodes(ref, graph, dist, build_junction_index(cached_refs))

    labels = {KIND_SIGNAL: "信号", KIND_CROSS: "国道交点", KIND_END: "路線の端"}
    rows = []
    for n in nodes:
        k = graph.nearest(n["lon"], n["lat"])
        kind = n.get("kind", KIND_SIGNAL if n.get("signals") else KIND_PLAIN)
        rows.append({
            "名称": n["name"],
            "起点からの距離km": round(dist.get(k, float("nan")), 1) if k in dist else "",
            "信号交差点": labels.get(kind, ""),
            "緯度": round(n["lat"], 6),
            "経度": round(n["lon"], 6),
        })
    rows.sort(key=lambda r: (r["起点からの距離km"] == "", r["起点からの距離km"]))

    os.makedirs(LIST_DIR, exist_ok=True)
    out = os.path.join(LIST_DIR, f"国道{ref}号.csv")
    with open(out, "w", encoding="utf-8-sig", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0]))
        w.writeheader()
        w.writerows(rows)

    print(f"\n国道{ref}号の名前付き地点 {len(rows)} 件（端から順）\n")
    for r in rows[:40]:
        mark = "●" if r["信号交差点"] else "・"
        km = f'{r["起点からの距離km"]:>7}' if r["起点からの距離km"] != "" else "      -"
        print(f"  {mark} {km} km  {r['名称']}")
    if len(rows) > 40:
        print(f"  … 残り {len(rows) - 40} 件")
    print(f"\n全件を {out} に書き出しました。")
    print("routes.csv の区間欄には，ここに出ている名称をそのまま「A〜B」の形で書いてください。")


# --------------------------------------------------------------------------
# build
# --------------------------------------------------------------------------

def add_named_nodes(acc, ref, node_dist, nodes):
    """1路線ぶんの交差点名を acc に足しこむ。

    重複区間では同じ交差点が複数の路線に現れるので、座標と名前でまとめ、
    「どの国道の何km地点か」を路線ぶんだけ並べて持つ。
    node_dist は far_end() を起点としたキロ程（`@` 指定の解決と同じ値）。
    グラフ上に見つからない交差点は距離を None にする。
    """
    for n in nodes:
        k = node_key([n["lon"], n["lat"]])
        key = (k, n["name"])
        entry = acc.get(key)
        if entry is None:
            kind = n.get("kind")
            if kind is None:
                kind = KIND_SIGNAL if n.get("signals") else KIND_PLAIN
            entry = acc[key] = [round(n["lat"], 5), round(n["lon"], 5),
                                n["name"], kind, []]
        km = (node_dist or {}).get(k)
        entry[4].append([ref, round(km, 1) if km is not None else None])


def finalize_named_nodes(acc):
    """[緯度, 経度, 名前, 種類, [[路線番号, 起点からのkm], ...]] の並びにする。

    同じ座標に複数の呼び名が付くことがある（国道の終端が別の国道の途中と
    交わっている場合、そこは「R363×R419」であり「R419端(北)」でもある）。
    別々の点のままだと重なり判定で片方が消え、消えなかった方が持っていない
    路線の区間を指定できなくなる。1点にまとめて両方の名前と路線を持たせる。
    """
    merged = {}
    for (key, name), entry in acc.items():
        base = merged.get(key)
        if base is None:
            merged[key] = entry
            continue
        if name not in base[2].split(NAME_SEP):
            base[2] += NAME_SEP + name
        base[3] = max(base[3], entry[3])
        for pair in entry[4]:
            if pair not in base[4]:
                base[4].append(pair)

    out = []
    for entry in merged.values():
        entry[4].sort(key=lambda pair: int(pair[0]))
        out.append(entry)
    return out


def route_covered(ref, graph, recs, node_dist, nodes):
    """1路線ぶんの走破した辺と、表示用の区間ラベル・走破日・メモを求める。

    build と serve の両方から呼ぶ（serve は編集された1路線だけ呼び直す）。
    """
    covered = set()
    sections, dates, notes = [], [], []

    for rec in recs:
        if rec["date"]:
            dates.append(rec["date"])
        if rec["note"]:
            notes.append(rec["note"])

        if rec["kind"] == "full":
            covered |= set(graph.edges)
            sections.append(FULL)

        elif rec["kind"] == "area":
            adata = load_json(area_cache_path(ref, rec["area"]))
            if adata is None:
                print(f"  国道{ref}号（{rec['area']}）が未取得です。"
                      f"`python kokudo_map.py fetch` を実行してください。", file=sys.stderr)
                continue
            sub_graph = RouteGraph(adata.get("ways") or {})
            hit = set(sub_graph.edges) & set(graph.edges)
            if not hit:
                print(f"  国道{ref}号（{rec['area']}）に該当する区間がありません。", file=sys.stderr)
                continue
            covered |= hit
            sections.append(rec["label"])

        elif rec["kind"] == "nodes":
            edges, dist = resolve_node_section(graph, nodes, rec, ref, node_dist)
            if edges:
                covered |= edges
                sections.append(f"{rec['label']}（{dist:.0f} km）")

    return covered, sections, dates, notes


def route_points(ref, graph, node_dist, junctions):
    """その路線で区間指定に使える地点。OSM の名前＋こちらで算出したもの。"""
    osm = (load_json(node_cache_path(ref)) or {}).get("nodes") or []
    return osm + derived_nodes(ref, graph, node_dist, junctions)


def route_features(ref, ways, covered):
    """各wayを走破／未走破の連続部分に切り分けて GeoJSON Feature にする"""
    done_lines, todo_lines = [], []
    for coords in ways.values():
        run, run_state = [], None
        for i in range(len(coords) - 1):
            a, b = node_key(coords[i]), node_key(coords[i + 1])
            state = edge_key(a, b) in covered
            if state != run_state:
                if len(run) >= 2:
                    (done_lines if run_state else todo_lines).append(run)
                run, run_state = [coords[i]], state
            run.append(coords[i + 1])
        if len(run) >= 2:
            (done_lines if run_state else todo_lines).append(run)

    out = []
    for lines, kind in ((todo_lines, "todo"), (done_lines, "done")):
        simplified = [s for s in (simplify(l, SIMPLIFY_TOLERANCE) for l in lines) if len(s) >= 2]
        if simplified:
            out.append({
                "type": "Feature",
                "properties": {"ref": ref, "kind": kind},
                "geometry": {"type": "MultiLineString", "coordinates": simplified},
            })
    return out


def route_status(route_km, route_done_km, covered):
    if not covered:
        return "todo"
    return "done" if route_done_km >= route_km * 0.98 else "partial"


def build_data():
    records = read_records()

    by_ref = defaultdict(list)
    for rec in records:
        by_ref[rec["ref"]].append(rec)

    cached_refs = set()
    if os.path.isdir(CACHE_DIR):
        for name in os.listdir(CACHE_DIR):
            if name.startswith("r") and name.endswith(".json"):
                cached_refs.add(name[1:-5])

    all_refs = sorted(cached_refs | set(by_ref), key=int)

    features, summary = [], []
    total_km = 0.0
    counted_edges = set()
    node_acc = {}
    covered_by_ref, edge_km = {}, {}
    junctions = build_junction_index(all_refs)

    for ref in all_refs:
        data = load_json(route_cache_path(ref))
        ways = (data or {}).get("ways") or {}
        if not ways:
            continue

        recs = by_ref.get(ref, [])
        # 起点からのキロ程。地図の注記にも `@` 指定の解決にも同じ値を使う
        graph = RouteGraph(ways)
        start = graph.far_end()
        node_dist = graph.dijkstra(start, [])[0] if start else None
        nodes_here = route_points(ref, graph, node_dist, junctions)
        add_named_nodes(node_acc, ref, node_dist, nodes_here)

        covered, sections, dates, notes = route_covered(ref, graph, recs, node_dist, nodes_here)

        # 延長の集計
        route_km = route_done_km = 0.0
        for key, km in graph.edges.items():
            route_km += km
            hit = key in covered
            if hit:
                route_done_km += km
                edge_km[key] = km
            if key not in counted_edges:
                counted_edges.add(key)
                total_km += km

        status = route_status(route_km, route_done_km, covered)
        covered_by_ref[ref] = covered
        features.extend(route_features(ref, ways, covered))

        lats = [p[1] for c in ways.values() for p in c]
        lons = [p[0] for c in ways.values() for p in c]

        summary.append({
            "ref": ref,
            "status": status,
            "km": round(route_km, 1),
            "doneKm": round(route_done_km, 1),
            "sections": sections,
            "dates": sorted(set(dates)),
            "notes": notes,
            "bounds": [[min(lats), min(lons)], [max(lats), max(lons)]],
        })

    nodes = finalize_named_nodes(node_acc)
    eki, eki_added = build_eki()

    # 重複区間を二重に数えないよう、走破した辺の集合の和で距離を出す
    done_edges = set()
    for edges in covered_by_ref.values():
        done_edges |= edges
    done_km = sum(edge_km.get(e, 0.0) for e in done_edges)

    stats = {
        "totalRoutes": len(summary),
        "doneRoutes": sum(1 for s in summary if s["status"] == "done"),
        "partialRoutes": sum(1 for s in summary if s["status"] == "partial"),
        "totalKm": round(total_km),
        "doneKm": round(done_km),
        "nodeCount": len(nodes),
        "ekiTotal": len(eki),
        "ekiDone": sum(1 for e in eki if e[4]),
        "ekiAdded": eki_added,
    }
    return {
        "geojson": {"type": "FeatureCollection", "features": features},
        "summary": summary,
        "stats": stats,
        "nodes": nodes,
        "eki": eki,
        # serve が1路線だけ計算し直すのに使う
        "coveredByRef": covered_by_ref,
        "edgeKm": edge_km,
        "junctions": junctions,
    }


def render_html(data, editable=False):
    """地図の HTML を組み立てる。editable=True なら serve 用の編集UIが出る。"""
    config = {"basemap": DEFAULT_BASEMAP, "opacity": BASEMAP_OPACITY,
              "showTodo": bool(SHOW_TODO), "showNodes": bool(SHOW_NODES),
              "nodeZoom": NODE_MIN_ZOOM, "labelZoom": LABEL_MIN_ZOOM,
              "showEki": bool(SHOW_EKI), "editable": bool(editable),
              "colors": {"done": DONE_COLOR, "todo": TODO_COLOR, "select": SELECT_COLOR}}
    return (HTML_TEMPLATE
            .replace("__GEOJSON__", json.dumps(data["geojson"], separators=(",", ":")))
            .replace("__SUMMARY__", json.dumps(data["summary"], ensure_ascii=False,
                                               separators=(",", ":")))
            .replace("__STATS__", json.dumps(data["stats"], ensure_ascii=False))
            .replace("__NODES__", json.dumps(data["nodes"], ensure_ascii=False,
                                             separators=(",", ":")))
            .replace("__EKI__", json.dumps(data["eki"], ensure_ascii=False,
                                           separators=(",", ":")))
            .replace("__CONFIG__", json.dumps(config))
            .replace("__DONE_COLOR__", DONE_COLOR)
            .replace("__TODO_COLOR__", TODO_COLOR)
            .replace("__SELECT_COLOR__", SELECT_COLOR)
            .replace("__NAME_SEP__", NAME_SEP)
            .replace("__PING_MS__", str(int(PING_INTERVAL * 1000))))


def cmd_build(args):
    print("地図を組み立てています…")
    data = build_data()
    geojson, summary = data["geojson"], data["summary"]
    stats, nodes, eki = data["stats"], data["nodes"], data["eki"]
    if not summary:
        print("描ける路線がありません。先に `python kokudo_map.py fetch` を実行してください。",
              file=sys.stderr)
        sys.exit(1)

    html = render_html(data, editable=False)
    with open(OUT_PATH, "w", encoding="utf-8") as f:
        f.write(html)

    pct = stats["doneKm"] / stats["totalKm"] * 100 if stats["totalKm"] else 0
    print(f"\n{OUT_PATH} を書き出しました（{os.path.getsize(OUT_PATH)/1024/1024:.1f} MB）")
    print(f"  収録路線 : {stats['totalRoutes']} 本")
    print(f"  全線走破 : {stats['doneRoutes']} 本（一部走破 {stats['partialRoutes']} 本）")
    print(f"  距離走破率: {stats['doneKm']:,} / {stats['totalKm']:,} km = {pct:.1f}%")
    print(f"  交差点名 : {stats['nodeCount']:,} 地点")
    if stats["ekiTotal"]:
        pct_eki = stats["ekiDone"] / stats["ekiTotal"] * 100
        print(f"  道の駅   : {stats['ekiDone']:,} / {stats['ekiTotal']:,} 駅 = {pct_eki:.1f}%")
        if stats["ekiAdded"]:
            print(f"    {stats['ekiAdded']} 駅を {EKI_CSV_PATH} に追加しました。"
                  f"訪問日を書き込むと地図が赤くなります。")
    if stats["totalRoutes"] < 300:
        print("\n※ 走破率は取得済みの路線だけで計算しています。")
        print("  全国基準にするには `python kokudo_map.py fetch --all` を一度実行してください。")


# --------------------------------------------------------------------------
# serve（地図から履歴を編集する）
# --------------------------------------------------------------------------
#
# file:// で開いた HTML からはファイルを書けないので、127.0.0.1 だけで待ち受ける
# 小さなサーバを立てて、ブラウザからの保存要求を Python 側で CSV に書く。
# 全路線の再計算は40秒ほどかかるので、編集された1路線だけ計算し直して差分を返す。

SERVE_PORT = 8765
# 地図の画面から何秒ごとに生存を知らせてもらうか
PING_INTERVAL = 5.0
# タブが閉じられた合図を受けてから、実際に終了するまでの猶予 [秒]。
# 読み込み直しでも同じ合図が飛ぶので、すぐ落とすと再読込で終了してしまう。
BYE_GRACE = 8.0
# 画面から何も言ってこなくなってから終了するまで [秒]。
# ブラウザは裏のタブのタイマーを1分程度まで間引くので、短くしすぎないこと。
IDLE_TIMEOUT = 900.0


ROUTE_HEADER = ["路線番号", "区間", "走破日", "メモ"]


def read_route_rows():
    """routes.csv を1行ずつそのまま読む（一覧表示と編集用）。

    `read_records()` と違い、解釈せずに書いてあるまま返す。
    行の位置がそのまま識別子になる。
    """
    rows = []
    if not os.path.exists(CSV_PATH):
        return rows
    with open(CSV_PATH, encoding="utf-8-sig", newline="") as f:
        for i, row in enumerate(csv.DictReader(f)):
            if not any((row.get(c) or "").strip() for c in ROUTE_HEADER):
                continue
            rows.append({"index": i,
                         "ref": (row.get("路線番号") or "").strip(),
                         "section": (row.get("区間") or "").strip(),
                         "date": (row.get("走破日") or "").strip(),
                         "note": (row.get("メモ") or "").strip()})
    return rows


def write_route_rows(rows):
    """routes.csv を書き直す。書き損じないよう別名で書いてから置き換える。"""
    tmp = CSV_PATH + ".tmp"
    with open(tmp, "w", encoding="utf-8-sig", newline="") as f:
        w = csv.writer(f, lineterminator="\n")
        w.writerow(ROUTE_HEADER)
        for r in rows:
            w.writerow([r["ref"], r["section"], r["date"], r["note"]])
    os.replace(tmp, CSV_PATH)


def append_route_row(ref, section, date, note):
    """routes.csv の末尾に1行足す。既存の行には触れない。"""
    text = ""
    if os.path.exists(CSV_PATH):
        with open(CSV_PATH, encoding="utf-8-sig") as f:
            text = f.read()
    if not text.strip():
        text = ",".join(["路線番号", "区間", "走破日", "メモ"]) + "\n"
    if not text.endswith("\n"):
        text += "\n"
    buf = io.StringIO()
    csv.writer(buf, lineterminator="\n").writerow([ref, section, date, note])
    with open(CSV_PATH, "w", encoding="utf-8-sig", newline="") as f:
        f.write(text + buf.getvalue())


def set_eki_visit(pref, name, date, note):
    """michinoeki.csv の1駅ぶんを書き換える。無ければ足す。"""
    rows, found = [], False
    if os.path.exists(EKI_CSV_PATH):
        with open(EKI_CSV_PATH, encoding="utf-8-sig", newline="") as f:
            for row in csv.DictReader(f):
                if ((row.get("都道府県") or "").strip() == pref
                        and eki_name(row.get("道の駅") or "") == name):
                    row["訪問日"] = date
                    if note is not None:
                        row["メモ"] = note
                    found = True
                rows.append({k: (row.get(k) or "") for k in EKI_HEADER})
    if not found:
        rows.append({"都道府県": pref, "道の駅": name, "訪問日": date, "メモ": note or ""})
    with open(EKI_CSV_PATH, "w", encoding="utf-8-sig", newline="") as f:
        w = csv.DictWriter(f, fieldnames=EKI_HEADER)
        w.writeheader()
        w.writerows(rows)


def recompute_ref(data, ref):
    """1路線だけ計算し直し、全国の集計も更新する。返り値はブラウザに返す差分。"""
    ways = (load_json(route_cache_path(ref)) or {}).get("ways") or {}
    if not ways:
        return None

    graph = RouteGraph(ways)
    start = graph.far_end()
    node_dist = graph.dijkstra(start, [])[0] if start else None
    recs = [r for r in read_records() if r["ref"] == ref]
    nodes_here = route_points(ref, graph, node_dist, data.get("junctions") or {})
    covered, sections, dates, notes = route_covered(ref, graph, recs, node_dist, nodes_here)

    route_km = route_done_km = 0.0
    for key, km in graph.edges.items():
        route_km += km
        if key in covered:
            route_done_km += km
            data["edgeKm"][key] = km

    data["coveredByRef"][ref] = covered

    row = next((s for s in data["summary"] if s["ref"] == ref), None)
    if row is None:
        return None
    row.update({
        "status": route_status(route_km, route_done_km, covered),
        "km": round(route_km, 1),
        "doneKm": round(route_done_km, 1),
        "sections": sections,
        "dates": sorted(set(dates)),
        "notes": notes,
    })

    features = route_features(ref, ways, covered)
    data["geojson"]["features"] = ([f for f in data["geojson"]["features"]
                                    if f["properties"]["ref"] != ref] + features)
    refresh_stats(data)
    return {"summary": row, "features": features, "stats": data["stats"]}


def refresh_stats(data):
    """全国の走破距離を数え直す。重複区間を二重に数えないよう辺の和で持つ。"""
    union = set()
    for edges in data["coveredByRef"].values():
        union |= edges
    done_km = sum(data["edgeKm"].get(k, 0.0) for k in union)
    summary = data["summary"]
    data["stats"].update({
        "doneKm": round(done_km),
        "doneRoutes": sum(1 for s in summary if s["status"] == "done"),
        "partialRoutes": sum(1 for s in summary if s["status"] == "partial"),
        "ekiDone": sum(1 for e in data["eki"] if e[4]),
    })


class EditHandler(http.server.BaseHTTPRequestHandler):
    """地図を配って、編集要求を CSV に書くだけのサーバ"""

    data = None
    lock = None
    server_ref = None       # 自分を止めるためのサーバ本体
    last_seen = 0.0         # 地図の画面から最後に合図が来た時刻
    goodbye_at = 0.0        # タブが閉じられた合図が来た時刻
    stopping = False

    def log_message(self, fmt, *args):
        pass          # アクセスログは出さない

    @classmethod
    def stop(cls, why):
        """待ち受けをやめる。別のスレッドから止めないと自分を待って固まる。"""
        if cls.stopping or cls.server_ref is None:
            return
        cls.stopping = True
        print(why, file=sys.stderr)
        threading.Thread(target=cls.server_ref.shutdown, daemon=True).start()

    def _send(self, code, body, ctype="application/json; charset=utf-8"):
        raw = body if isinstance(body, bytes) else body.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(raw)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(raw)

    def do_GET(self):
        if self.path in ("/", "/index.html"):
            with self.lock:
                html = render_html(self.data, editable=True)
            self._send(200, html, "text/html; charset=utf-8")
        elif self.path == "/api/records":
            with self.lock:
                rows = read_route_rows()
            self._send(200, json.dumps({"rows": rows}, ensure_ascii=False))
        else:
            self._send(404, json.dumps({"error": "not found"}))

    def do_POST(self):
        try:
            length = int(self.headers.get("Content-Length") or 0)
            payload = json.loads(self.rfile.read(length).decode("utf-8")) if length else {}
        except (ValueError, UnicodeDecodeError):
            self._send(400, json.dumps({"error": "壊れた要求です"}))
            return

        try:
            with self.lock:
                if self.path == "/api/eki":
                    result = self._save_eki(payload)
                elif self.path == "/api/section":
                    result = self._save_section(payload)
                elif self.path == "/api/record":
                    result = self._edit_record(payload)
                elif self.path == "/api/preview":
                    result = self._preview_record(payload)
                elif self.path == "/api/ping":
                    # 地図の画面が生きている合図。読み込み直しならここで戻る
                    EditHandler.last_seen = time.time()
                    EditHandler.goodbye_at = 0.0
                    result = {"ok": True}
                elif self.path == "/api/bye":
                    # タブが閉じられた（か、読み込み直された）
                    EditHandler.goodbye_at = time.time()
                    result = {"ok": True}
                elif self.path == "/api/quit":
                    result = {"ok": True}
                    EditHandler.stop("\n地図の「終了」が押されました。終了します。")
                else:
                    self._send(404, json.dumps({"error": "not found"}))
                    return
        except Exception as e:                      # 保存に失敗しても地図は生かす
            self._send(500, json.dumps({"error": str(e)}, ensure_ascii=False))
            return

        self._send(200, json.dumps(result, ensure_ascii=False))

    # -- 道の駅 ----------------------------------------------------------
    def _save_eki(self, payload):
        pref = (payload.get("pref") or "").strip()
        name = eki_name(payload.get("name") or "")
        date = (payload.get("date") or "").strip()
        note = payload.get("note")
        set_eki_visit(pref, name, date, note)

        for e in self.data["eki"]:
            if e[3] == pref and e[2] == name:
                e[4] = 1 if date else 0
                e[5] = date
                if note is not None:
                    e[6] = note
                break
        refresh_stats(self.data)
        print(f"  道の駅 {pref} {name}: "
              + (f"訪問 {date}" if date else "未訪問に戻しました"), file=sys.stderr)
        return {"ok": True, "stats": self.data["stats"]}

    # -- 国道の区間 ------------------------------------------------------
    def _save_section(self, payload):
        ref = str(payload.get("ref") or "").strip()
        section = (payload.get("section") or "").strip()
        if not ref.isdigit() or not section:
            return {"ok": False, "error": "路線番号か区間が空です"}

        append_route_row(ref, section, (payload.get("date") or "").strip(),
                         (payload.get("note") or "").strip())
        diff = recompute_ref(self.data, ref)
        if diff is None:
            return {"ok": False, "error": f"国道{ref}号を計算し直せませんでした"}
        print(f"  国道{ref}号に「{section}」を追加しました "
              f"({diff['summary']['doneKm']:.0f} / {diff['summary']['km']:.0f} km)",
              file=sys.stderr)
        return {"ok": True, **diff}

    # -- 記録1件がどこを指しているか --------------------------------------
    def _preview_record(self, payload):
        """その行の区間だけを辺に直し、地図に重ねる形と範囲を返す"""
        rows = read_route_rows()
        target = next((r for r in rows if r["index"] == payload.get("index")), None)
        if target is None or target["section"] != (payload.get("section") or ""):
            return {"ok": False, "error": "記録が変わっています。一覧を開き直してください"}

        secs = parse_row(target["ref"], target["section"],
                         target["date"], target["note"], quiet=True)
        if not secs:
            return {"ok": False, "error": "この区間は解釈できません"}

        ref = secs[0]["ref"]
        ways = (load_json(route_cache_path(ref)) or {}).get("ways") or {}
        if not ways:
            return {"ok": False, "error": f"国道{ref}号の形状がありません"}

        graph = RouteGraph(ways)
        start = graph.far_end()
        node_dist = graph.dijkstra(start, [])[0] if start else None
        nodes = route_points(ref, graph, node_dist, self.data.get("junctions") or {})
        covered, _sections, _dates, _notes = route_covered(ref, graph, secs, node_dist, nodes)
        if not covered:
            return {"ok": False, "error": "この区間は地図上で特定できませんでした"}

        feats = [f for f in route_features(ref, ways, covered)
                 if f["properties"]["kind"] == "done"]
        pts = [p for f in feats for line in f["geometry"]["coordinates"] for p in line]
        if not pts:
            return {"ok": False, "error": "この区間は地図上で特定できませんでした"}
        return {"ok": True, "ref": ref, "features": feats,
                "km": round(sum(graph.edges[e] for e in covered), 1),
                "bounds": [[min(p[1] for p in pts), min(p[0] for p in pts)],
                           [max(p[1] for p in pts), max(p[0] for p in pts)]]}

    # -- 記録の書き換えと削除 --------------------------------------------
    def _edit_record(self, payload):
        action = payload.get("action")
        index = payload.get("index")
        rows = read_route_rows()
        target = next((r for r in rows if r["index"] == index), None)

        # 一覧を開いたあとにファイルが変わっていたら、取り違えないよう断る
        if target is None or target["section"] != (payload.get("section") or ""):
            return {"ok": False, "error": "記録が変わっています。一覧を開き直してください",
                    "rows": rows}

        ref = target["ref"]
        if action == "delete":
            rows = [r for r in rows if r["index"] != index]
            print(f"  国道{ref}号の「{target['section']}」を削除しました", file=sys.stderr)
        elif action == "update":
            target["date"] = (payload.get("date") or "").strip()
            target["note"] = (payload.get("note") or "").strip()
            print(f"  国道{ref}号の「{target['section']}」を更新しました"
                  f"（走破日 {target['date'] or '空'}）", file=sys.stderr)
        else:
            return {"ok": False, "error": "不明な操作です"}

        write_route_rows(rows)
        out = {"ok": True, "rows": read_route_rows()}
        if ref.isdigit():
            diff = recompute_ref(self.data, ref)
            if diff:
                out.update(diff)
        return out


def watch_browser():
    """地図の画面が閉じられたら、こちらも終了する。

    合図が来ないまま終了すると、ブラウザを開く前に落ちてしまう。
    いちども合図が来ていないうちは何もしない。
    """
    while not EditHandler.stopping:
        time.sleep(1.0)
        now = time.time()
        bye, seen = EditHandler.goodbye_at, EditHandler.last_seen
        if bye and now - bye > BYE_GRACE and seen < bye:
            EditHandler.stop("\n地図のタブが閉じられました。終了します。")
            return
        if seen and now - seen > IDLE_TIMEOUT:
            EditHandler.stop("\nしばらく画面から応答がないので終了します。")
            return


def cmd_serve(args):
    print("地図を組み立てています…（初回は1分ほどかかります）")
    data = build_data()
    if not data["summary"]:
        print("描ける路線がありません。先に `python kokudo_map.py fetch` を実行してください。",
              file=sys.stderr)
        sys.exit(1)

    EditHandler.data = data
    EditHandler.lock = threading.Lock()
    url = f"http://127.0.0.1:{args.port}/"

    try:
        server = http.server.ThreadingHTTPServer(("127.0.0.1", args.port), EditHandler)
    except OSError as e:
        print(f"ポート {args.port} を使えません（{e}）。"
              f"`--port 8766` のように変えてください。", file=sys.stderr)
        sys.exit(1)
    EditHandler.server_ref = server

    print(f"\n{url} で待ち受けています。ブラウザを開きます。")
    print("  道の駅の丸を押すと訪問済みを切り替えられます。")
    print("  交差点名を押して「ここから」→「ここまで」で区間を追加できます。")
    print("  編集はその場で routes.csv / michinoeki.csv に書き込まれます。")
    print("\n  終わるときは、地図の右上の「終了」を押すか、ブラウザのタブを閉じてください。")
    print("  この画面は自動で閉じます。\n")
    webbrowser.open(url)
    threading.Thread(target=watch_browser, daemon=True).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        EditHandler.stop("\n終了します。")
    server.server_close()
    print("終了しました。")


# --------------------------------------------------------------------------
# HTML テンプレート
# --------------------------------------------------------------------------

HTML_TEMPLATE = r"""<!DOCTYPE html>
<html lang="ja">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>国道走破マップ</title>
<link rel="stylesheet" href="https://unpkg.com/leaflet@1.9.4/dist/leaflet.css">
<style>
  :root {
    --sign-blue: #0b3f8f;
    --done: __DONE_COLOR__;
    --todo: __TODO_COLOR__;
    --select: __SELECT_COLOR__;
    --ink: #16202c;
    --muted: #6c7a89;
    --rule: #dfe4ea;
    --panel: #fbfcfd;
  }
  * { box-sizing: border-box; }
  html, body { height: 100%; margin: 0; }
  body {
    font-family: "BIZ UDPGothic", "Noto Sans JP", "Hiragino Kaku Gothic ProN",
                 "Yu Gothic UI", system-ui, sans-serif;
    color: var(--ink); -webkit-font-smoothing: antialiased;
  }
  #app { display: flex; height: 100%; }
  #map { flex: 1; background: #eef1f4; }

  #side {
    width: 330px; flex: none; display: flex; flex-direction: column;
    background: var(--panel); border-left: 1px solid var(--rule);
  }
  header { padding: 18px 20px 14px; border-bottom: 1px solid var(--rule); }
  .titlebar { display: flex; align-items: flex-start; gap: 10px; }
  .titlebar > div { flex: 1; min-width: 0; }
  #quit {
    flex: none; font: inherit; font-size: 11px; padding: 4px 12px; cursor: pointer;
    border: 1px solid var(--rule); border-radius: 5px; background: #fff; color: var(--muted);
  }
  #quit:hover { background: var(--done); border-color: var(--done); color: #fff; }
  #quit:focus-visible { outline: 2px solid var(--sign-blue); outline-offset: 2px; }
  #quit[hidden] { display: none; }

  /* 終了したあとにかぶせる案内 */
  #bye {
    position: fixed; inset: 0; z-index: 10000; display: grid; place-items: center;
    background: rgba(251,252,253,.96); text-align: center; padding: 24px;
  }
  #bye b { display: block; font-size: 17px; margin-bottom: 10px; }
  #bye span { font-size: 12.5px; color: var(--muted); line-height: 1.9; }
  h1 { margin: 0; font-size: 15px; font-weight: 700; letter-spacing: .08em; }
  .tagline { margin: 4px 0 0; font-size: 11px; color: var(--muted); letter-spacing: .04em; }

  .stats { padding: 16px 20px; border-bottom: 1px solid var(--rule); }
  .bar { height: 8px; border-radius: 4px; background: var(--todo); overflow: hidden; margin-bottom: 10px; }
  .bar > span { display: block; height: 100%; background: var(--done); }
  .figure { display: flex; align-items: baseline; gap: 6px; }
  .figure b { font-size: 30px; font-weight: 700; line-height: 1; font-variant-numeric: tabular-nums; }
  .figure small { font-size: 12px; color: var(--muted); }
  .detail { margin-top: 10px; font-size: 11.5px; color: var(--muted); line-height: 1.7; font-variant-numeric: tabular-nums; }

  .view {
    padding: 12px 20px 14px; border-bottom: 1px solid var(--rule);
    display: grid; gap: 9px; font-size: 11.5px; color: var(--muted);
  }
  .view label { display: flex; align-items: center; gap: 9px; }
  .view label > span:first-child { flex: none; width: 44px; }
  .view select {
    flex: 1; font: inherit; font-size: 11.5px; padding: 4px 6px;
    border: 1px solid var(--rule); border-radius: 5px; background: #fff; color: var(--ink);
  }
  .view input[type="range"] { flex: 1; accent-color: var(--sign-blue); }
  .view .check { gap: 7px; cursor: pointer; }
  .view .check input { accent-color: var(--done); }
  .view :focus-visible { outline: 2px solid var(--sign-blue); outline-offset: 2px; }

  .filters { display: flex; padding: 10px 16px; gap: 6px; border-bottom: 1px solid var(--rule); }  .filters button {
    flex: 1; padding: 6px 0; font: inherit; font-size: 11.5px; cursor: pointer;
    border: 1px solid var(--rule); background: #fff; border-radius: 5px; color: var(--muted);
  }
  .filters button[aria-pressed="true"] { background: var(--sign-blue); border-color: var(--sign-blue); color: #fff; font-weight: 700; }
  .filters button:focus-visible { outline: 2px solid var(--sign-blue); outline-offset: 2px; }

  .tabs { display: flex; border-bottom: 1px solid var(--rule); }
  .tabs button {
    flex: 1; padding: 9px 0; font: inherit; font-size: 11.5px; cursor: pointer;
    border: 0; border-bottom: 2px solid transparent; background: none; color: var(--muted);
  }
  .tabs button[aria-pressed="true"] {
    color: var(--sign-blue); border-bottom-color: var(--sign-blue); font-weight: 700;
  }
  .tabs button:focus-visible { outline: 2px solid var(--sign-blue); outline-offset: -2px; }
  #paneRoutes, #paneRecords { flex: 1; min-height: 0; display: flex; flex-direction: column; }
  #paneRoutes[hidden], #paneRecords[hidden], .tabs[hidden] { display: none; }
  #paneRecords { overflow-y: auto; padding: 4px 0 24px; }

  .rec { padding: 8px 16px; border-bottom: 1px solid #eef1f4; font-size: 11.5px; }
  .rec.on { background: #fff6e2; }
  .rec .head {
    display: flex; align-items: center; gap: 8px; width: 100%;
    padding: 0; border: 0; background: none; font: inherit; text-align: left; cursor: pointer;
  }
  .rec .head:hover .sec { text-decoration: underline; }
  .rec .head:focus-visible { outline: 2px solid var(--sign-blue); outline-offset: 2px; }
  .rec .num {
    flex: none; min-width: 34px; padding: 1px 5px; border-radius: 4px; text-align: center;
    background: var(--sign-blue); color: #fff; font-weight: 700; font-size: 10.5px;
  }
  .rec.on .num { background: #a86400; }
  .rec .sec { flex: 1; min-width: 0; word-break: break-all; }
  .rec .foot { display: flex; align-items: center; gap: 6px; margin-top: 5px; color: var(--muted); }
  .rec .foot .when { flex: 1; font-variant-numeric: tabular-nums; }
  .rec input {
    font: inherit; font-size: 11px; padding: 3px 5px; width: 100%;
    border: 1px solid var(--rule); border-radius: 4px; background: #fff; color: var(--ink);
  }
  .rec .grid { display: grid; grid-template-columns: 1fr 1fr; gap: 5px; margin-top: 5px; }
  .btn.warn { border-color: var(--done); color: var(--done); }

  #list { flex: 1; overflow-y: auto; padding: 6px 0 24px; }
  .row {
    display: flex; align-items: center; gap: 11px; width: 100%;
    padding: 7px 20px; background: none; border: 0; font: inherit; text-align: left; cursor: pointer;
  }
  .row:hover { background: #eef2f7; }

  /* serve のときだけ出る編集用の帯とボタン */
  #edit { display: none; padding: 10px 16px; border-bottom: 1px solid var(--rule);
          background: #fff8e6; font-size: 11.5px; line-height: 1.7; }
  #edit.on { display: block; }
  #edit b { color: #a86400; }
  .btn { font: inherit; font-size: 11px; padding: 3px 9px; margin: 2px 3px 0 0;
         border: 1px solid var(--rule); border-radius: 5px; background: #fff;
         color: var(--ink); cursor: pointer; }
  .btn:hover { background: #eef2f7; }
  .btn.go { background: var(--sign-blue); border-color: var(--sign-blue);
            color: #fff; font-weight: 700; }
  .btn.off { background: #fff; border-color: var(--done); color: var(--done); }
  .leaflet-popup-content .btn { margin-top: 6px; }
  .row[aria-pressed="true"] { background: #e7edfa; box-shadow: inset 3px 0 0 var(--sign-blue); }
  .row[aria-pressed="true"] .name { color: var(--sign-blue); }
  .row:focus-visible { outline: 2px solid var(--sign-blue); outline-offset: -2px; }
  .row .meta { flex: 1; min-width: 0; }
  .row .name { font-size: 12.5px; font-weight: 600; }
  .row .sub {
    font-size: 10.5px; color: var(--muted); white-space: nowrap;
    overflow: hidden; text-overflow: ellipsis; font-variant-numeric: tabular-nums;
  }

  /* 国道標識（おにぎり） */
  .shield {
    flex: none; width: 30px; height: 26px; display: grid; place-items: center;
    clip-path: polygon(50% 100%, 0 8%, 100% 8%); background: var(--todo);
  }
  .shield.done { background: var(--done); }
  .shield.partial { background: linear-gradient(90deg, var(--done) 50%, var(--todo) 50%); }
  .shield span {
    font-size: 10px; font-weight: 700; color: #fff; line-height: 1;
    margin-top: -3px; letter-spacing: -.03em; font-variant-numeric: tabular-nums;
  }

  .legend { padding: 12px 20px 16px; border-top: 1px solid var(--rule); font-size: 11px; color: var(--muted); line-height: 1.9; }
  .legend i { display: inline-block; width: 18px; height: 3px; margin-right: 7px; vertical-align: 2px; }

  @media (max-width: 760px) {
    #app { flex-direction: column-reverse; }
    #side { width: 100%; height: 46%; border-left: 0; border-top: 1px solid var(--rule); }
  }
  @media (prefers-reduced-motion: reduce) { * { transition: none !important; } }
</style>
</head>
<body>
<div id="app">
  <div id="map"></div>
  <aside id="side">
    <header>
      <div class="titlebar">
        <div>
          <h1>国道走破マップ</h1>
          <p class="tagline">走った道を赤で塗る</p>
        </div>
        <button id="quit" type="button" hidden>終了</button>
      </div>
    </header>
    <div class="stats">
      <div class="bar"><span id="bar"></span></div>
      <div class="figure"><b id="pct">–</b><small>% 走破（距離）</small></div>
      <div class="detail" id="detail"></div>
    </div>
    <div class="view">
      <label>
        <span>背景</span>
        <select id="basemap">
          <option value="blank">白地図（海岸線と行政界のみ）</option>
          <option value="pale">淡色地図（地名・道路あり）</option>
          <option value="std">標準地図</option>
          <option value="photo">空中写真</option>
          <option value="none">背景なし</option>
        </select>
      </label>
      <label>
        <span>濃さ</span>
        <input type="range" id="opacity" min="0" max="100" step="5">
      </label>
      <label class="check">
        <input type="checkbox" id="showTodo"><span>未走破の国道も描く</span>
      </label>
      <label class="check">
        <input type="checkbox" id="showNodes"><span>交差点名を出す（拡大すると出ます）</span>
      </label>
      <label class="check">
        <input type="checkbox" id="showEki"><span>道の駅を出す</span>
      </label>
    </div>
    <div id="edit"></div>
    <div class="tabs" id="tabs" hidden>
      <button data-tab="routes" aria-pressed="true">路線</button>
      <button data-tab="records" aria-pressed="false">走破記録</button>
    </div>
    <div id="paneRoutes">
      <div class="filters">
        <button data-filter="all" aria-pressed="true">すべて</button>
        <button data-filter="done" aria-pressed="false">走破済み</button>
        <button data-filter="partial" aria-pressed="false">一部</button>
        <button data-filter="todo" aria-pressed="false">未走破</button>
      </div>
      <div id="list"></div>
    </div>
    <div id="paneRecords" hidden></div>
    <div class="legend">
      <div><i style="background:var(--done)"></i>走破済み</div>
      <div><i style="background:var(--todo)"></i>未走破</div>
      <div><b style="color:var(--done)">●</b> 訪問済みの道の駅　<b style="color:var(--todo)">●</b> 未訪問</div>
      <div style="margin-top:6px"><b style="color:#0b3f8f">●</b> 信号交差点　<b style="color:#0f7b4f">◆</b> 国道どうしの交点　<b style="color:#111827">◆</b> 路線の端</div>
      <div style="margin-top:6px">一覧の番号を押すとその国道だけが色濃く出ます（もう一度押すと解除）</div>
      <div>交差点名をクリックすると区間欄用の書き方が出ます</div>
    </div>
  </aside>
</div>

<script src="https://unpkg.com/leaflet@1.9.4/dist/leaflet.js"></script>
<script>
// スクリプトが途中で止まると地図が半分だけ描かれた状態になり、原因が分からない。
// 気づけるように画面へ出す。
window.addEventListener("error", (ev) => {
  const box = document.createElement("div");
  box.style.cssText = "position:fixed;left:0;right:0;bottom:0;z-index:9999;"
    + "background:#d81f26;color:#fff;padding:10px 14px;"
    + "font:12px/1.6 ui-monospace,monospace;white-space:pre-wrap";
  box.textContent = "地図の読み込みでエラーが起きました。\n"
    + (ev.message || ev.error || "") + "\n"
    + (ev.filename || "") + " " + (ev.lineno || "") + "行目";
  document.body.appendChild(box);
});

const GEOJSON = __GEOJSON__;
const SUMMARY = __SUMMARY__;
const STATS = __STATS__;
const EKI = __EKI__;       // [緯度, 経度, 名前, 都道府県, 訪問済みか, 訪問日, メモ]
const NODES = __NODES__;   // [緯度, 経度, 名前, 信号か, [[路線番号, 起点からのkm], ...]]
const CONFIG = __CONFIG__;

const GSI = "https://cyberjapandata.gsi.go.jp/xyz/";
const GSI_CREDIT = "<a href='https://maps.gsi.go.jp/development/ichiran.html'>国土地理院</a>";
const OSM_CREDIT = "道路データ: <a href='https://www.openstreetmap.org/copyright'>OpenStreetMap</a> contributors";

// 白地図は z5〜z14 でしか配信されていないので、範囲外は近いズームのタイルを引き伸ばす
const BASEMAPS = {
  blank: { url: GSI + "blank/{z}/{x}/{y}.png", credit: GSI_CREDIT, minNativeZoom: 5, maxNativeZoom: 14 },
  pale:  { url: GSI + "pale/{z}/{x}/{y}.png",  credit: GSI_CREDIT, maxNativeZoom: 18 },
  std:   { url: GSI + "std/{z}/{x}/{y}.png",   credit: GSI_CREDIT, maxNativeZoom: 18 },
  photo: { url: GSI + "seamlessphoto/{z}/{x}/{y}.jpg", credit: GSI_CREDIT, maxNativeZoom: 18 },
  none:  { url: null, credit: null }
};

const map = L.map("map", { preferCanvas: true }).setView([37.0, 137.5], 6);
map.attributionControl.addAttribution(OSM_CREDIT);

let baseLayer = null;

function setBasemap(key) {
  if (baseLayer) { map.removeLayer(baseLayer); baseLayer = null; }
  const spec = BASEMAPS[key] || BASEMAPS.blank;
  document.getElementById("map").style.background = key === "photo" ? "#2b2f33" : "#f5f7f9";
  if (!spec.url) return;
  baseLayer = L.tileLayer(spec.url, {
    attribution: "地図データ: " + spec.credit,
    maxZoom: 18,
    minNativeZoom: spec.minNativeZoom,
    maxNativeZoom: spec.maxNativeZoom,
    opacity: Number(document.getElementById("opacity").value) / 100
  });
  baseLayer.addTo(map);
  baseLayer.bringToBack();
}

// 線も道の駅も1枚のキャンバスに描く。
// pane を分けるとキャンバスも分かれ、上の pane が下の線へのクリックを飲み込む。
// 1枚なら Leaflet が描画順（あとに足したものが上）で当たり判定をしてくれる。
map.createPane("featPane").style.zIndex = 420;
const featRenderer = L.canvas({ pane: "featPane", padding: 0.3, tolerance: 10 });

// 選択した路線の縁取り。線そのものより下に敷いて，赤／グレーを潰さない
map.createPane("selPane").style.zIndex = 405;

const COLORS = CONFIG.colors;
let selectedRef = null;
let recHighlight = null;   // 記録タブで選んだ区間の形（縁取りに使う）

// 編集用の状態。道の駅レイヤがこれらを使うので、必ずレイヤ生成より前に置くこと。
const EDITABLE = !!CONFIG.editable;
const editEl = document.getElementById("edit");
const ekiMarkers = [];          // EKI と同じ並びのマーカー
let pending = null;             // 区間の始点として選んだ交差点
let popupNode = null;           // いま開いている交差点のポップアップの地点
let lineLatLng = null;          // 線をクリックした場所（任意の点の指定に使う）

// 地点の種類。0=名前付き 1=信号 2=国道の交点 3=路線の端
const PT_COLOR = ["#8a96a3", "#0b3f8f", "#0f7b4f", "#111827"];
const NAME_SEP = "__NAME_SEP__";   // 1地点に複数の呼び名が付くときの区切り
const PT_SIZE = [2.2, 3, 3.8, 4.2];

function esc(text) {
  return String(text).replace(/[&<>"]/g, c =>
    ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c]));
}

function todoStyle(f) {
  if (f.properties.ref === selectedRef) return { color: COLORS.todo, weight: 2.8, opacity: 1 };
  return { color: COLORS.todo, weight: 1.4, opacity: selectedRef ? 0.18 : 0.85 };
}
function doneStyle(f) {
  if (f.properties.ref === selectedRef) return { color: COLORS.done, weight: 4.5, opacity: 1 };
  return { color: COLORS.done, weight: 2.8, opacity: selectedRef ? 0.16 : 0.95 };
}

const layerSel = L.geoJSON(null, {
  pane: "selPane", renderer: L.canvas({ pane: "selPane" }),
  style: { color: COLORS.select, weight: 10, opacity: 0.55 },
  interactive: false
}).addTo(map);
const layerTodo = L.geoJSON(null, {
  pane: "featPane", renderer: featRenderer, style: todoStyle
});
const layerDone = L.geoJSON(null, {
  pane: "featPane", renderer: featRenderer, style: doneStyle
});

// 選択を地図と一覧の両方に反映する
function refreshSelection() {
  layerSel.clearLayers();
  if (recHighlight) {
    // 記録1件ぶんの区間だけを縁取る
    for (const f of recHighlight) layerSel.addData(f);
  } else if (selectedRef) {
    for (const f of GEOJSON.features) {
      if (f.properties.ref !== selectedRef) continue;
      // 未走破を隠しているときは、その部分の縁取りも出さない
      if (f.properties.kind === "todo" && !showTodoEl.checked) continue;
      layerSel.addData(f);
    }
  }
  layerDone.setStyle(doneStyle);
  layerTodo.setStyle(todoStyle);
  for (const b of listEl.querySelectorAll(".row")) {
    b.setAttribute("aria-pressed", String(b.dataset.ref === selectedRef));
  }
}

// 同じ番号をもう一度押すと解除
function selectRoute(ref) {
  recActive = null;          // 路線を選び直したら区間のハイライトは外す
  recHighlight = null;
  selectedRef = (selectedRef === ref) ? null : ref;
  refreshSelection();
  return selectedRef !== null;
}

const byRef = {};
for (const s of SUMMARY) byRef[s.ref] = s;
for (const f of GEOJSON.features) {
  (f.properties.kind === "done" ? layerDone : layerTodo).addData(f);
}

const STATUS_LABEL = { done: "全線走破", partial: "一部走破", todo: "未走破" };

function popupHtml(s) {
  const bits = [
    `<strong style="font-size:14px">国道${s.ref}号</strong>`,
    `${STATUS_LABEL[s.status]}　${s.doneKm.toLocaleString()} / ${s.km.toLocaleString()} km`
  ];
  if (s.sections.length) bits.push(`区間: ${s.sections.join(" ／ ")}`);
  if (s.dates.length) bits.push(`走破日: ${s.dates.join(", ")}`);
  if (s.notes.length) bits.push(s.notes.join(" / "));
  return bits.join("<br>");
}

// 点と線分の距離の2乗（画面座標）
function segDist2(p, a, b) {
  const bx = b.x - a.x, by = b.y - a.y;
  const d2 = bx * bx + by * by;
  const t = d2 > 0 ? Math.max(0, Math.min(1, ((p.x - a.x) * bx + (p.y - a.y) * by) / d2)) : 0;
  const dx = p.x - (a.x + t * bx), dy = p.y - (a.y + t * by);
  return dx * dx + dy * dy;
}

// その地点を通っている国道をすべて拾う。
// Leaflet のクリックは最前面の1本しか返さないので、重複区間では
// どの国道として記録するのか選べない。当たり判定を自分で全レイヤに掛ける。
//
// 重複区間でも路線ごとに独立して線を間引いているため、同じ道でも描かれた線が
// 数十mずれることがある（実測で 17% が 15m 以上）。画素固定の判定だと
// 拡大するほど取りこぼすので、40m 相当を目安にズームで換算する。
function routesAtPoint(latlng) {
  const p = map.latLngToLayerPoint(latlng);
  const mPerPx = 156543.03 * Math.cos(latlng.lat * Math.PI / 180) / Math.pow(2, map.getZoom());
  const tol = Math.min(25, Math.max(6, 40 / mPerPx));
  const tol2 = tol * tol;

  const refs = new Set();
  for (const layer of [layerDone, layerTodo]) {
    if (!map.hasLayer(layer)) continue;
    layer.eachLayer(l => {
      const ref = l.feature && l.feature.properties.ref;
      if (!ref || refs.has(ref) || !l._parts) return;
      for (const part of l._parts) {
        for (let i = 1; i < part.length; i++) {
          if (segDist2(p, part[i - 1], part[i]) <= tol2) {
            refs.add(ref);
            return;
          }
        }
      }
    });
  }
  return [...refs].sort((a, b) => Number(a) - Number(b));
}

// 線の上の好きな場所を区間端にできる。重複区間では国道ごとにボタンを出す。
function linePopupHtml(refs) {
  const rows = refs.map(ref => {
    const s = byRef[ref];
    if (!s) return "";
    const act = !EDITABLE ? ""
      : (pending && pending.ref === ref
        ? `<button class="btn go" data-pt-finish="${ref}">ここまで</button>`
        : `<button class="btn" data-pt-start="${ref}">ここから</button>`);
    return `<tr><td style="padding-right:9px"><b>国道${ref}号</b></td>`
      + `<td style="padding-right:9px">${STATUS_LABEL[s.status]}　`
      + `${s.doneKm.toLocaleString()} / ${s.km.toLocaleString()} km</td>`
      + `<td>${act}</td></tr>`;
  }).join("");

  const bits = [`<strong style="font-size:13px">この地点を通る国道</strong>`
    + `<table style="font-size:11.5px;margin:6px 0 2px;border-collapse:collapse">`
    + `${rows}</table>`];
  if (refs.length === 1) {
    const s = byRef[refs[0]];
    if (s && s.sections.length) bits.push(`<span style="font-size:11px">区間: ${s.sections.join(" ／ ")}</span>`);
    if (s && s.dates.length) bits.push(`<span style="font-size:11px">走破日: ${s.dates.join(", ")}</span>`);
    if (s && s.notes.length) bits.push(`<span style="font-size:11px">${esc(s.notes.join(" / "))}</span>`);
  }
  return bits.join("<br>");
}

for (const layer of [layerDone, layerTodo]) {
  layer.on("click", (e) => {
    lineLatLng = e.latlng;
    let refs = routesAtPoint(e.latlng);
    if (!refs.length && e.layer.feature) refs = [e.layer.feature.properties.ref];
    if (refs.length) {
      L.popup().setLatLng(e.latlng).setContent(linePopupHtml(refs)).openOn(map);
    }
  });
}

// ---- 道の駅 ----
// 千駅ほどなので、交差点名と違って普通のマーカーで足りる。
const layerEki = L.layerGroup([], { pane: "featPane" });

EKI.forEach((e, i) => {
  const been = e[4];
  const marker = L.circleMarker([e[0], e[1]], {
    pane: "featPane", renderer: featRenderer, radius: been ? 6 : 5,
    color: "#fff", weight: 1.6, opacity: 0.95,
    fillColor: been ? COLORS.done : COLORS.todo, fillOpacity: been ? 1 : 0.8
  }).addTo(layerEki);
  marker.bindPopup(() => ekiPopup(i));
  ekiMarkers[i] = marker;
});

// ---- 交差点名の注記 ----
// 数万地点あるのでマーカーは使わず、表示範囲に入るぶんだけキャンバスに描く。
// 名前は重なるものを捨てながら置くので、縮小するほど自然に間引かれる。
const NODE_GRID = 0.05;             // 索引の升目（度）。約5km四方
const NODE_DRAW_LIMIT = 2000;       // 1画面に描く点の上限

const nodeIndex = new Map();
for (const n of NODES) {
  const key = Math.floor(n[0] / NODE_GRID) + "," + Math.floor(n[1] / NODE_GRID);
  let cell = nodeIndex.get(key);
  if (!cell) nodeIndex.set(key, cell = []);
  cell.push(n);
}

map.createPane("labelPane");
const labelPane = map.getPane("labelPane");
labelPane.style.zIndex = 450;
labelPane.style.pointerEvents = "none";
const labelCanvas = L.DomUtil.create("canvas", "", labelPane);
labelCanvas.style.position = "absolute";
const lctx = labelCanvas.getContext("2d");

const NAME_FONT = '600 11px "BIZ UDPGothic","Noto Sans JP","Yu Gothic UI",sans-serif';
const TAG_FONT = '500 9px "BIZ UDPGothic","Noto Sans JP","Yu Gothic UI",sans-serif';
const TAG_LINE = 10;   // 積むときの行送り [px]

let nodesOn = true;
let zooming = false;
let placed = [];   // 実際に描いた地点。クリック判定に使う

// 「R路線番号/端からのkm」を、乗っている国道のぶんだけ作る
function nodeTags(n) {
  return (n[4] || []).map(p => "R" + p[0] + "/" + (p[1] === null ? "?" : p[1]));
}

function sizeLabelCanvas() {
  const size = map.getSize();
  const dpr = window.devicePixelRatio || 1;
  labelCanvas.width = size.x * dpr;
  labelCanvas.height = size.y * dpr;
  labelCanvas.style.width = size.x + "px";
  labelCanvas.style.height = size.y + "px";
  lctx.setTransform(dpr, 0, 0, dpr, 0, 0);
}

function clearLabels() {
  const size = map.getSize();
  lctx.clearRect(0, 0, size.x, size.y);
  placed = [];
}

function visibleNodes() {
  const b = map.getBounds();
  const out = [];
  const y0 = Math.floor(b.getSouth() / NODE_GRID), y1 = Math.floor(b.getNorth() / NODE_GRID);
  const x0 = Math.floor(b.getWest() / NODE_GRID), x1 = Math.floor(b.getEast() / NODE_GRID);
  for (let y = y0; y <= y1; y++) {
    for (let x = x0; x <= x1; x++) {
      const cell = nodeIndex.get(y + "," + x);
      if (!cell) continue;
      for (const n of cell) if (b.contains([n[0], n[1]])) out.push(n);
    }
  }
  return out;
}

function drawLabels() {
  L.DomUtil.setPosition(labelCanvas, map.containerPointToLayerPoint([0, 0]));
  clearLabels();
  const z = map.getZoom();
  if (!nodesOn || z < CONFIG.nodeZoom) return;

  const withText = z >= CONFIG.labelZoom;
  const found = visibleNodes();
  found.sort((a, b) => b[3] - a[3]);          // 信号交差点を優先して置く
  if (found.length > NODE_DRAW_LIMIT) found.length = NODE_DRAW_LIMIT;

  lctx.textBaseline = "middle";
  lctx.lineJoin = "round";

  const HALO = "rgba(255,255,255,.92)";
  const boxes = [];
  for (const n of found) {
    const p = map.latLngToContainerPoint([n[0], n[1]]);
    const r = PT_SIZE[n[3]] || 2.2;
    lctx.beginPath();
    if (n[3] >= 2) {          // 算出した地点はひし形にして一目で分かるようにする
      lctx.moveTo(p.x, p.y - r);
      lctx.lineTo(p.x + r, p.y);
      lctx.lineTo(p.x, p.y + r);
      lctx.lineTo(p.x - r, p.y);
      lctx.closePath();
    } else {
      lctx.arc(p.x, p.y, r, 0, Math.PI * 2);
    }
    lctx.strokeStyle = "rgba(255,255,255,.9)";
    lctx.lineWidth = 1.4;
    lctx.stroke();
    lctx.fillStyle = PT_COLOR[n[3]] || "#8a96a3";
    lctx.fill();
    if (!withText) continue;

    // 2本までは名前のうしろに横並び。3本以上は下に積む
    // （横に伸ばすと重なり判定で捨てられて、かえって見えなくなる）
    const tags = nodeTags(n);
    const inline = tags.length <= 2 ? tags.join(" ") : "";
    const stack = tags.length > 2 ? tags : [];

    lctx.font = NAME_FONT;
    const w1 = lctx.measureText(n[2]).width;
    lctx.font = TAG_FONT;
    const wInline = inline ? lctx.measureText(inline).width + 4 : 0;
    let wStack = 0;
    for (const t of stack) wStack = Math.max(wStack, lctx.measureText(t).width);

    const tx = p.x + 6, ty = p.y;
    const w = Math.max(w1 + wInline, wStack);
    const box = [tx - 2, ty - 8, tx + w + 2, ty + 8 + stack.length * TAG_LINE];
    if (boxes.some(o => box[0] < o[2] && box[2] > o[0] && box[1] < o[3] && box[3] > o[1])) continue;
    boxes.push(box);

    lctx.font = NAME_FONT;
    lctx.lineWidth = 3.2;
    lctx.strokeStyle = HALO;
    lctx.strokeText(n[2], tx, ty);
    lctx.fillStyle = "#16202c";
    lctx.fillText(n[2], tx, ty);

    lctx.font = TAG_FONT;
    lctx.lineWidth = 3;
    if (inline) {
      lctx.strokeStyle = HALO;
      lctx.strokeText(inline, tx + w1 + 4, ty);
      lctx.fillStyle = "#0b3f8f";
      lctx.fillText(inline, tx + w1 + 4, ty);
    }
    for (let i = 0; i < stack.length; i++) {
      const y = ty + TAG_LINE * (i + 1);
      lctx.strokeStyle = HALO;
      lctx.strokeText(stack[i], tx, y);
      lctx.fillStyle = "#0b3f8f";
      lctx.fillText(stack[i], tx, y);
    }
    placed.push({ n: n, x: p.x, y: p.y });
  }
}

// 名前をクリックしたら routes.csv に貼れる形を出す
map.on("click", (e) => {
  if (!placed.length) return;
  const p = map.latLngToContainerPoint(e.latlng);
  let best = null, bestD = 196;   // 14px 以内
  for (const it of placed) {
    const d = (it.x - p.x) ** 2 + (it.y - p.y) ** 2;
    if (d < bestD) { bestD = d; best = it; }
  }
  if (!best) return;
  const n = best.n;
  popupNode = n;
  const name = esc(n[2]);
  const canon = esc(n[2].split(NAME_SEP)[0]);
  const here = `${canon}@${n[0]}/${n[1]}`;
  const rows = (n[4] || []).map(pair => {
    const km = pair[1];
    // 分断された区間の地点は端からの距離が測れない。そこは座標で位置を示す。
    const paste = km === null
      ? `<span style="color:#6c7a89">距離不明</span>　<code>${here}</code>`
      : `${km} km　<code>${canon}@${km}</code>`;
    let act = "";
    if (EDITABLE) {
      act = (pending && pending.ref === pair[0])
        ? `<button class="btn go" data-finish="${pair[0]}">ここまで</button>`
        : `<button class="btn" data-start="${pair[0]}">ここから</button>`;
    }
    return `<tr><td style="padding-right:10px">国道${pair[0]}号</td>`
      + `<td style="padding-right:8px">${paste}</td><td>${act}</td></tr>`;
  }).join("");
  L.popup().setLatLng([n[0], n[1]]).setContent(
    `<strong style="font-size:13px">${name}</strong>` +
    (n[3] ? "　信号交差点" : "") +
    `<table style="font-size:11px;margin:6px 0 4px;border-collapse:collapse">${rows}</table>` +
    `<span style="font-size:11px;color:#6c7a89">どの路線でも: </span>` +
    `<code style="font-size:11px">${canon}@${n[0]}/${n[1]}</code>`
  ).openOn(map);
});

sizeLabelCanvas();
map.on("move", () => { if (!zooming) drawLabels(); });
map.on("zoomstart", () => { zooming = true; clearLabels(); });
map.on("zoomend", () => { zooming = false; drawLabels(); });
map.on("resize", () => { sizeLabelCanvas(); drawLabels(); });

const pct = STATS.totalKm ? (STATS.doneKm / STATS.totalKm * 100) : 0;
document.getElementById("pct").textContent = pct.toFixed(1);
document.getElementById("bar").style.width = Math.max(pct, 0.4) + "%";
document.getElementById("detail").innerHTML =
  `${STATS.doneKm.toLocaleString()} / ${STATS.totalKm.toLocaleString()} km<br>` +
  `全線走破 ${STATS.doneRoutes} 本・一部走破 ${STATS.partialRoutes} 本 / 収録 ${STATS.totalRoutes} 本` +
  (STATS.ekiTotal
    ? `<br>道の駅 ${STATS.ekiDone.toLocaleString()} / ${STATS.ekiTotal.toLocaleString()} 駅`
      + `（${(STATS.ekiDone / STATS.ekiTotal * 100).toFixed(1)}%）`
    : "");

const listEl = document.getElementById("list");
let filter = "all";

function render() {
  const rows = SUMMARY.filter(s => filter === "all" || s.status === filter);
  listEl.innerHTML = "";
  if (!rows.length) {
    listEl.innerHTML = '<p style="padding:20px;font-size:12px;color:#6c7a89">該当する路線はありません</p>';
    return;
  }
  const frag = document.createDocumentFragment();
  for (const s of rows) {
    const btn = document.createElement("button");
    btn.className = "row";
    btn.type = "button";
    btn.dataset.ref = s.ref;
    btn.setAttribute("aria-pressed", String(s.ref === selectedRef));
    const sub = s.status === "partial"
      ? `${s.doneKm.toLocaleString()} / ${s.km.toLocaleString()} km　${s.sections.join("・")}`
      : `${s.km.toLocaleString()} km`;
    btn.innerHTML =
      `<span class="shield ${s.status}"><span>${s.ref}</span></span>` +
      `<span class="meta"><span class="name">国道${s.ref}号</span><br><span class="sub">${sub}</span></span>`;
    btn.addEventListener("click", () => {
      if (!selectRoute(s.ref)) {   // 解除したときは地図を動かさない
        map.closePopup();
        return;
      }
      map.fitBounds(s.bounds, { padding: [40, 40] });
      L.popup()
        .setLatLng([(s.bounds[0][0] + s.bounds[1][0]) / 2, (s.bounds[0][1] + s.bounds[1][1]) / 2])
        .setContent(popupHtml(s)).openOn(map);
    });
    frag.appendChild(btn);
  }
  listEl.appendChild(frag);
}

for (const btn of document.querySelectorAll(".filters button")) {
  btn.addEventListener("click", () => {
    filter = btn.dataset.filter;
    for (const b of document.querySelectorAll(".filters button")) {
      b.setAttribute("aria-pressed", String(b === btn));
    }
    listEl.scrollTop = 0;
    render();
  });
}

// ---- 編集（serve のときだけ動く） ----
// 変数の宣言は道の駅レイヤより前で済ませてある（下の「編集用の状態」参照）。
// ここに const で置くと、レイヤ生成時にまだ初期化されておらず地図全体が止まる。

function today() {
  const d = new Date();
  return `${d.getFullYear()}/${d.getMonth() + 1}/${d.getDate()}`;
}

async function post(path, body) {
  const res = await fetch(path, {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify(body)
  });
  const out = await res.json().catch(() => ({ error: "応答を読めませんでした" }));
  if (!res.ok || out.error) throw new Error(out.error || `保存に失敗しました (${res.status})`);
  return out;
}

function showEdit(html) {
  editEl.innerHTML = html;
  editEl.classList.toggle("on", !!html);
}

function refreshStats(stats) {
  Object.assign(STATS, stats);
  const pc = STATS.totalKm ? (STATS.doneKm / STATS.totalKm * 100) : 0;
  document.getElementById("pct").textContent = pc.toFixed(1);
  document.getElementById("bar").style.width = Math.max(pc, 0.4) + "%";
  document.getElementById("detail").innerHTML =
    `${STATS.doneKm.toLocaleString()} / ${STATS.totalKm.toLocaleString()} km<br>` +
    `全線走破 ${STATS.doneRoutes} 本・一部走破 ${STATS.partialRoutes} 本 / 収録 ${STATS.totalRoutes} 本` +
    (STATS.ekiTotal
      ? `<br>道の駅 ${STATS.ekiDone.toLocaleString()} / ${STATS.ekiTotal.toLocaleString()} 駅`
        + `（${(STATS.ekiDone / STATS.ekiTotal * 100).toFixed(1)}%）`
      : "");
}

// -- 道の駅 --------------------------------------------------------------
function ekiPopup(i) {
  const e = EKI[i];
  const been = e[4];
  return `<strong style="font-size:13px">道の駅 ${esc(e[2])}</strong>` +
    `<br><span style="font-size:11px;color:#6c7a89">${esc(e[3])}</span>` +
    (been ? `<br>訪問: ${esc(e[5])}` : `<br><span style="color:#6c7a89">未訪問</span>`) +
    (e[6] ? `<br>${esc(e[6])}` : "") +
    (EDITABLE
      ? `<br><button class="btn ${been ? "off" : "go"}" data-eki="${i}">`
        + (been ? "訪問を取り消す" : "行った") + `</button>`
      : "");
}

async function toggleEki(i) {
  const e = EKI[i], marker = ekiMarkers[i];
  if (!e || !marker) return;
  const been = e[4];
  const date = been ? "" : today();
  const out = await post("/api/eki", { pref: e[3], name: e[2], date: date });
  e[4] = been ? 0 : 1;
  e[5] = date;
  marker.setStyle({
    fillColor: e[4] ? COLORS.done : COLORS.todo,
    fillOpacity: e[4] ? 1 : 0.8, radius: e[4] ? 6 : 5
  });
  marker.setPopupContent(ekiPopup(i));
  refreshStats(out.stats);
}

// -- 国道の区間 ----------------------------------------------------------
// label は画面に出す名前、text は routes.csv に書く形（名前@km または @緯度,経度）
function startSection(ref, label, text) {
  pending = { ref: ref, label: label, text: text };
  showEdit(`国道${ref}号 <b>${esc(label)}</b> から<br>` +
    `もう一方の地点を押して「ここまで」を選んでください` +
    `<br><button class="btn" data-cancel="1">やめる</button>`);
  map.closePopup();
}

async function finishSection(ref, label, text) {
  if (!pending || pending.ref !== ref) return;
  const a = pending, b = { label: label, text: text };
  pending = null;
  showEdit(`国道${ref}号 <b>${esc(a.label)}〜${esc(b.label)}</b> を保存しています…`);
  const section = `${a.text}〜${b.text}`;
  try {
    const out = await post("/api/section", { ref: ref, section: section, date: today() });
    applyRouteUpdate(ref, out);
    if (!recordsEl.hidden) loadRecords();
    showEdit(`国道${ref}号 <b>${esc(a.label)}〜${esc(b.label)}</b> を追加しました`
      + `（${out.summary.doneKm.toLocaleString()} / ${out.summary.km.toLocaleString()} km）`
      + `<br><button class="btn" data-cancel="1">閉じる</button>`);
    map.closePopup();
  } catch (err) {
    showEdit(`<b>保存できませんでした</b><br>${esc(err.message)}`
      + `<br><button class="btn" data-cancel="1">閉じる</button>`);
  }
}

function applyRouteUpdate(ref, out) {
  for (const layer of [layerDone, layerTodo]) {
    const kill = [];
    layer.eachLayer(l => {
      if (l.feature && l.feature.properties.ref === ref) kill.push(l);
    });
    for (const l of kill) layer.removeLayer(l);
  }
  GEOJSON.features = GEOJSON.features.filter(f => f.properties.ref !== ref);
  for (const f of out.features) {
    GEOJSON.features.push(f);
    (f.properties.kind === "done" ? layerDone : layerTodo).addData(f);
  }
  const i = SUMMARY.findIndex(s => s.ref === ref);
  if (i >= 0) SUMMARY[i] = out.summary;
  byRef[ref] = out.summary;
  refreshStats(out.stats);
  if (selectedRef === ref) refreshSelection();
  render();
}

// 地図・ポップアップ・帯のボタンをまとめて受ける
document.addEventListener("click", (ev) => {
  const btn = ev.target.closest("button[data-eki], button[data-start], " +
                               "button[data-finish], button[data-cancel], " +
                               "button[data-pt-start], button[data-pt-finish], " +
                               "button[data-tab], button[data-rec-go], " +
                               "button[data-rec-edit], button[data-rec-del], " +
                               "button[data-rec-save], button[data-rec-cancel]");
  if (!btn) return;
  ev.preventDefault();
  const fail = (err) =>
    showEdit(`<b>保存できませんでした</b><br>${esc(err.message)}`
      + `<br><button class="btn" data-cancel="1">閉じる</button>`);

  if (btn.hasAttribute("data-cancel")) {
    pending = null;
    showEdit("");
    if (recActive !== null) {
      recActive = null;
      recHighlight = null;
      selectedRef = null;
      refreshSelection();
      renderRecords();
    }
  } else if (btn.hasAttribute("data-eki")) {
    toggleEki(Number(btn.dataset.eki)).catch(fail);
  } else if (btn.hasAttribute("data-start") || btn.hasAttribute("data-finish")) {
    const ref = btn.dataset.start || btn.dataset.finish;
    const pair = popupNode && (popupNode[4] || []).find(x => x[0] === ref);
    if (!pair) return;
    // 1つの地点に複数の呼び名が付いていることがある（「R363×R419／R419端(北)」）。
    // 区間欄には結合前の名前を書かないと突き合わせに失敗する。
    const canon = popupNode[2].split(NAME_SEP)[0];
    // 距離が測れない地点（分断された区間）は座標で位置を確定させる
    const text = pair[1] === null
      ? `${canon}@${popupNode[0]}/${popupNode[1]}`
      : `${canon}@${pair[1]}`;
    if (btn.hasAttribute("data-start")) startSection(ref, popupNode[2], text);
    else finishSection(ref, popupNode[2], text).catch(fail);
  } else if (btn.hasAttribute("data-tab")) {
    showTab(btn.dataset.tab);
  } else if (btn.hasAttribute("data-rec-go")) {
    showRecord(Number(btn.dataset.recGo)).catch(fail);
  } else if (btn.hasAttribute("data-rec-edit")) {
    editingIndex = Number(btn.dataset.recEdit);
    renderRecords();
  } else if (btn.hasAttribute("data-rec-cancel")) {
    editingIndex = null;
    renderRecords();
  } else if (btn.hasAttribute("data-rec-save")) {
    saveRecord(Number(btn.dataset.recSave)).catch(fail);
  } else if (btn.hasAttribute("data-rec-del")) {
    deleteRecord(Number(btn.dataset.recDel)).catch(fail);
  } else if (btn.hasAttribute("data-pt-start") || btn.hasAttribute("data-pt-finish")) {
    if (!lineLatLng) return;
    const ref = btn.dataset.ptStart || btn.dataset.ptFinish;
    const lat = lineLatLng.lat.toFixed(5), lon = lineLatLng.lng.toFixed(5);
    const text = `@${lat}/${lon}`;
    const label = `地点(${lat},${lon})`;
    if (btn.hasAttribute("data-pt-start")) startSection(ref, label, text);
    else finishSection(ref, label, text).catch(fail);
  }
});

// ---- 走破記録の一覧（serve のときだけ） ----
// CSV を開かずに日付の書き換えと削除ができるようにする。
const recordsEl = document.getElementById("paneRecords");
const routesEl = document.getElementById("paneRoutes");
const tabsEl = document.getElementById("tabs");
let RECORDS = [];
let editingIndex = null;
let recActive = null;      // ハイライト中の記録の番号

function showTab(name) {
  routesEl.hidden = name !== "routes";
  recordsEl.hidden = name !== "records";
  for (const b of tabsEl.querySelectorAll("button")) {
    b.setAttribute("aria-pressed", String(b.dataset.tab === name));
  }
  if (name === "records") loadRecords();
}

async function loadRecords() {
  recordsEl.innerHTML = '<p style="padding:16px;font-size:12px;color:#6c7a89">読み込み中…</p>';
  try {
    const res = await fetch("/api/records");
    RECORDS = (await res.json()).rows || [];
  } catch (err) {
    recordsEl.innerHTML = '<p style="padding:16px;font-size:12px;color:#d81f26">'
      + "記録を読めませんでした</p>";
    return;
  }
  renderRecords();
}

function renderRecords() {
  if (!RECORDS.length) {
    recordsEl.innerHTML = '<p style="padding:16px;font-size:12px;color:#6c7a89">'
      + "まだ記録がありません。地図から区間を追加してください。</p>";
    return;
  }
  const frag = document.createDocumentFragment();
  for (const r of RECORDS) {
    const div = document.createElement("div");
    div.className = "rec" + (recActive === r.index ? " on" : "");
    const editing = editingIndex === r.index;
    let html =
      `<button class="head" type="button" data-rec-go="${r.index}"`
      + ` aria-pressed="${String(recActive === r.index)}">`
      + `<span class="num">${esc(r.ref)}</span>`
      + `<span class="sec">${esc(r.section)}</span></button>`;
    if (editing) {
      html += `<div class="grid">`
        + `<input data-rec-date="${r.index}" value="${esc(r.date)}" placeholder="走破日">`
        + `<input data-rec-note="${r.index}" value="${esc(r.note)}" placeholder="メモ">`
        + `</div><div class="foot">`
        + `<span class="when"></span>`
        + `<button class="btn go" data-rec-save="${r.index}">保存</button>`
        + `<button class="btn" data-rec-cancel="1">やめる</button></div>`;
    } else {
      html += `<div class="foot"><span class="when">`
        + (r.date ? esc(r.date) : "日付なし")
        + (r.note ? "　" + esc(r.note) : "")
        + `</span>`
        + `<button class="btn" data-rec-edit="${r.index}">編集</button>`
        + `<button class="btn warn" data-rec-del="${r.index}">削除</button></div>`;
    }
    div.innerHTML = html;
    frag.appendChild(div);
  }
  recordsEl.innerHTML = "";
  recordsEl.appendChild(frag);
}

function applyRecordResult(out) {
  RECORDS = out.rows || RECORDS;
  editingIndex = null;
  // 行が動くと番号がずれるので、ハイライトは落とす
  recActive = null;
  recHighlight = null;
  if (out.summary && out.features) applyRouteUpdate(out.summary.ref, out);
  else if (out.stats) refreshStats(out.stats);
  renderRecords();
}

// 記録1件が指している区間だけを地図に浮かび上がらせる
async function showRecord(index) {
  const row = RECORDS.find(r => r.index === index);
  if (!row) return;
  if (recActive === index) {          // もう一度押したら解除
    recActive = null;
    recHighlight = null;
    selectedRef = null;
    refreshSelection();
    renderRecords();
    return;
  }
  const out = await post("/api/preview", { index: index, section: row.section });
  recActive = index;
  recHighlight = out.features;
  selectedRef = out.ref;              // その路線以外を沈める
  refreshSelection();
  renderRecords();
  map.fitBounds(out.bounds, { padding: [50, 50] });
  showEdit(`国道${out.ref}号 <b>${esc(row.section)}</b>（${out.km.toLocaleString()} km）`
    + `<br><button class="btn" data-cancel="1">閉じる</button>`);
}

async function saveRecord(index) {
  const row = RECORDS.find(r => r.index === index);
  if (!row) return;
  const date = recordsEl.querySelector(`[data-rec-date="${index}"]`).value;
  const note = recordsEl.querySelector(`[data-rec-note="${index}"]`).value;
  applyRecordResult(await post("/api/record", {
    action: "update", index: index, section: row.section, date: date, note: note
  }));
}

async function deleteRecord(index) {
  const row = RECORDS.find(r => r.index === index);
  if (!row) return;
  if (!confirm(`国道${row.ref}号「${row.section}」を削除します。よろしいですか。`)) return;
  applyRecordResult(await post("/api/record", {
    action: "delete", index: index, section: row.section
  }));
}

// ---- 表示設定 ----
const basemapEl = document.getElementById("basemap");
const opacityEl = document.getElementById("opacity");
const showTodoEl = document.getElementById("showTodo");
const showNodesEl = document.getElementById("showNodes");
const showEkiEl = document.getElementById("showEki");

basemapEl.value = CONFIG.basemap in BASEMAPS ? CONFIG.basemap : "blank";
opacityEl.value = Math.round(CONFIG.opacity * 100);
showTodoEl.checked = CONFIG.showTodo;
showNodesEl.checked = CONFIG.showNodes;
showEkiEl.checked = CONFIG.showEki;
nodesOn = CONFIG.showNodes;

basemapEl.addEventListener("change", () => setBasemap(basemapEl.value));
opacityEl.addEventListener("input", () => {
  if (baseLayer) baseLayer.setOpacity(Number(opacityEl.value) / 100);
});
// 1枚のキャンバスでは「あとに足したもの」が上に来る。
// 未走破 → 走破済み → 道の駅 の順を保つため、切り替えのたびに積み直す。
function stackLayers() {
  for (const l of [layerTodo, layerDone, layerEki]) map.removeLayer(l);
  if (showTodoEl.checked) layerTodo.addTo(map);
  layerDone.addTo(map);
  if (showEkiEl.checked) layerEki.addTo(map);
}

showTodoEl.addEventListener("change", () => {
  stackLayers();
  refreshSelection();
});

// Esc で選択解除
document.addEventListener("keydown", (e) => {
  if (e.key === "Escape" && selectedRef) {
    selectRoute(selectedRef);
    map.closePopup();
  }
});
showNodesEl.addEventListener("change", () => {
  nodesOn = showNodesEl.checked;
  drawLabels();
});
showEkiEl.addEventListener("change", stackLayers);

// ---- 起動と終了（serve のときだけ） ----
// プログラム本体はこの画面が生きている間だけ動く。
// タブを閉じたら本体も終わるようにしておかないと、
// 使う人が「黒い画面」を自分で閉じる羽目になる。
const quitEl = document.getElementById("quit");
quitEl.hidden = !EDITABLE;

function farewell(text) {
  const box = document.createElement("div");
  box.id = "bye";
  box.innerHTML = `<div><b>終了しました</b><span>${esc(text)}</span></div>`;
  document.body.appendChild(box);
}

if (EDITABLE) {
  // 生きている合図。これが途絶えると本体は自分で終わる
  const beat = () => fetch("/api/ping", { method: "POST" }).catch(() => {});
  beat();
  setInterval(beat, __PING_MS__);
  // 別のページから戻ってきたとき（bfcache）にも、すぐ知らせる
  window.addEventListener("pageshow", beat);

  // タブを閉じたとき。読み込み直しでも飛ぶので、本体は少し待ってから判断する
  window.addEventListener("pagehide", () => {
    if (navigator.sendBeacon) navigator.sendBeacon("/api/bye", "{}");
  });

  quitEl.addEventListener("click", async () => {
    quitEl.disabled = true;
    try {
      await fetch("/api/quit", { method: "POST" });
    } catch (err) {
      /* 本体が先に落ちていても構わない */
    }
    farewell("このタブを閉じてください。"
      + "もう一度使うときは、プログラムをもう一度起動してください。");
  });
}

tabsEl.hidden = !EDITABLE;
setBasemap(basemapEl.value);
stackLayers();
drawLabels();

render();
</script>
</body>
</html>
"""


# --------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description="国道走破マップ生成ツール")
    sub = parser.add_subparsers(dest="command", required=True)

    p = sub.add_parser("init", help="routes.csv のひな形を作る")
    p.add_argument("--force", action="store_true", help="既存のCSVを上書きする")
    p.set_defaults(func=cmd_init)

    p = sub.add_parser("fetch", help="OpenStreetMap からデータを取得する")
    p.add_argument("--all", action="store_true", help="全国道（1〜507号）の形状を取得する")
    p.add_argument("--force", action="store_true", help="キャッシュを無視して取り直す")
    p.set_defaults(func=cmd_fetch)

    p = sub.add_parser("nodes", help="路線上で使える交差点名の一覧を出す")
    p.add_argument("ref", help="路線番号（例: 17）")
    p.set_defaults(func=cmd_nodes)

    p = sub.add_parser("build", help="地図 HTML を生成する")
    p.set_defaults(func=cmd_build)

    p = sub.add_parser("serve", help="地図から履歴を編集できる状態で開く")
    p.add_argument("--port", type=int, default=SERVE_PORT, help=f"既定 {SERVE_PORT}")
    p.set_defaults(func=cmd_serve)

    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
