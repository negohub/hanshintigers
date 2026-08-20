#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
猛虎必勝 — NPBデータ自動収集スクリプト

    python scripts/update_data.py              # 通常実行（data/latest.json を更新）
    python scripts/update_data.py --dry-run    # 保存せず標準出力に出す
    python scripts/update_data.py --date 2026-08-21

設計方針
--------
* 取得先ごとに try/except で囲み、**一部が失敗しても他は更新する**。
  失敗したセクションは data/latest.json の前回値をそのまま引き継ぐ（サイトが空にならない）。
* HTML構造の変更に強いよう、まず pandas.read_html で表をまるごと読み、
  列名の「ゆらぎ」を正規化してから使う。
* 天気は Open-Meteo（APIキー不要・JSON）を使用。浜風は風向を球場軸に射影して算出する。

出典
----
* 順位表 / チーム成績 / 個人成績 : NPB公式（npb.jp）
* 予告先発                      : スポーツナビ（baseball.yahoo.co.jp）
* 天気・風速                    : Open-Meteo (open-meteo.com)
"""

from __future__ import annotations

import argparse
import io
import json
import math
import os
import re
import sys
import time
import unicodedata
from datetime import datetime, date, timedelta, timezone
from typing import Any, Dict, List, Optional

import requests

try:
    import pandas as pd
except ImportError:  # pragma: no cover
    pd = None

try:
    from bs4 import BeautifulSoup
except ImportError:  # pragma: no cover
    BeautifulSoup = None


# =====================================================================
# 設定
# =====================================================================

JST = timezone(timedelta(hours=9))
_season_env = (os.environ.get("NPB_SEASON") or "").strip()
SEASON = int(_season_env) if _season_env.isdigit() else datetime.now(JST).year

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT_PATH = os.path.join(ROOT, "data", "latest.json")

UA = ("Mozilla/5.0 (compatible; moko-hissho-bot/1.0; "
      "+https://github.com/negohub/hanshin-yosou)")
TIMEOUT = 20
RETRY = 3
SLEEP = 1.2          # 連続アクセスの間隔（相手サーバに負荷をかけない）

NPB = "https://npb.jp/bis/{season}/stats/{page}"

# NPB公式のチーム記号（個人成績ページの末尾）
# このサイトは阪神の予想サイトなので、セ・リーグ6球団だけを扱う
TEAM_CODE = {
    "巨人": "g", "阪神": "t", "ＤｅＮＡ": "db", "広島": "c", "ヤクルト": "s", "中日": "d",
}

# サイト側（index.html の TEAM キー）に合わせた正式表記へ寄せる
# セ・リーグ以外の球団名も正規化はしておく（日程ページの解析で拾うため）
TEAM_ALIASES = {
    "阪神": "阪神", "阪神タイガース": "阪神", "T": "阪神", "タイガース": "阪神",
    "巨人": "巨人", "読売": "巨人", "読売ジャイアンツ": "巨人", "G": "巨人", "ジャイアンツ": "巨人",
    "DeNA": "ＤｅＮＡ", "ＤｅＮＡ": "ＤｅＮＡ", "横浜DeNA": "ＤｅＮＡ",
    "横浜DeNAベイスターズ": "ＤｅＮＡ", "ベイスターズ": "ＤｅＮＡ", "DB": "ＤｅＮＡ",
    "広島": "広島", "広島東洋カープ": "広島", "カープ": "広島", "C": "広島",
    "ヤクルト": "ヤクルト", "東京ヤクルトスワローズ": "ヤクルト", "スワローズ": "ヤクルト", "S": "ヤクルト",
    "中日": "中日", "中日ドラゴンズ": "中日", "ドラゴンズ": "中日", "D": "中日",
    "ソフトバンク": "ソフトバンク", "福岡ソフトバンクホークス": "ソフトバンク", "ホークス": "ソフトバンク", "H": "ソフトバンク",
    "日本ハム": "日本ハム", "北海道日本ハムファイターズ": "日本ハム", "ファイターズ": "日本ハム",
    "日本ハムファイターズ": "日本ハム", "F": "日本ハム",
    "オリックス": "オリックス", "オリックス・バファローズ": "オリックス", "バファローズ": "オリックス", "B": "オリックス",
    "ロッテ": "ロッテ", "千葉ロッテマリーンズ": "ロッテ", "マリーンズ": "ロッテ", "M": "ロッテ",
    "楽天": "楽天", "東北楽天ゴールデンイーグルス": "楽天", "イーグルス": "楽天", "E": "楽天",
    "西武": "西武", "埼玉西武ライオンズ": "西武", "ライオンズ": "西武", "L": "西武",
}

HOME_TEAM = "阪神"
CENTRAL = ["阪神", "巨人", "ＤｅＮＡ", "広島", "ヤクルト", "中日"]

# 球場の位置と「浜風の吹いてくる方位」
#   hamakaze_from … その方位から吹くとき最も浜風らしい（度／北=0, 東=90）
#   甲子園はライト（南西）方向から本塁へ吹き込む風を浜風と呼ぶ。実測に合わせて調整可。
PARKS = {
    "甲子園":     {"lat": 34.7211, "lon": 135.3617, "dome": False, "hamakaze_from": 225},
    "京セラD大阪": {"lat": 34.6693, "lon": 135.4761, "dome": True},
    "東京ドーム":  {"lat": 35.7056, "lon": 139.7519, "dome": True},
    "神宮":       {"lat": 35.6744, "lon": 139.7170, "dome": False, "hamakaze_from": 180},
    "横浜":       {"lat": 35.4433, "lon": 139.6400, "dome": False, "hamakaze_from": 180},
    "マツダ":     {"lat": 34.3919, "lon": 132.4842, "dome": False, "hamakaze_from": 180},
    "バンテリン":  {"lat": 35.1856, "lon": 136.9472, "dome": True},
    "PayPayドーム": {"lat": 33.5953, "lon": 130.3625, "dome": True},
    "エスコン":    {"lat": 42.9906, "lon": 141.5116, "dome": True},
    "ZOZOマリン":  {"lat": 35.6453, "lon": 140.0311, "dome": False, "hamakaze_from": 270},
    "楽天モバイル": {"lat": 38.2562, "lon": 140.9022, "dome": False, "hamakaze_from": 180},
    "ベルーナD":   {"lat": 35.7694, "lon": 139.4200, "dome": True},
}

# 球場名のゆらぎ吸収
PARK_ALIASES = {
    "阪神甲子園球場": "甲子園", "甲子園球場": "甲子園", "甲子園": "甲子園",
    "京セラドーム大阪": "京セラD大阪", "京セラD": "京セラD大阪",
    "東京ドーム": "東京ドーム",
    "明治神宮野球場": "神宮", "神宮球場": "神宮", "神宮": "神宮",
    "横浜スタジアム": "横浜", "ハマスタ": "横浜", "横浜": "横浜",
    "MAZDA Zoom-Zoom スタジアム広島": "マツダ", "マツダスタジアム": "マツダ", "マツダ": "マツダ",
    "バンテリンドーム ナゴヤ": "バンテリン", "バンテリンドーム": "バンテリン", "バンテリン": "バンテリン",
    "みずほPayPayドーム福岡": "PayPayドーム", "PayPayドーム": "PayPayドーム",
    "エスコンフィールド": "エスコン", "ES CON FIELD HOKKAIDO": "エスコン",
    "ZOZOマリンスタジアム": "ZOZOマリン", "ZOZOマリン": "ZOZOマリン",
    "楽天モバイルパーク宮城": "楽天モバイル",
    "ベルーナドーム": "ベルーナD",
}

# FIP定数（要件の簡易式）
FIP_CONST = 3.20

# wOBA係数（NPB向けの一般的な近似値。年ごとに再校正する前提）
WOBA_W = {"bb": 0.692, "hbp": 0.730, "1b": 0.865, "2b": 1.334, "3b": 1.725, "hr": 2.065}

LOG_PREFIX = "[update_data]"


def log(*a: Any) -> None:
    print(LOG_PREFIX, *a, flush=True)


# =====================================================================
# 小道具
# =====================================================================

def norm_text(s: Any) -> str:
    """全角/半角・空白・注記を落として比較しやすくする"""
    if s is None:
        return ""
    s = unicodedata.normalize("NFKC", str(s))
    s = s.replace("\u3000", " ")
    s = re.sub(r"[\s\u200b]+", "", s)
    s = re.sub(r"[※*＊†]", "", s)
    return s.strip()


def norm_team(name: Any) -> Optional[str]:
    key = norm_text(name)
    if not key:
        return None
    if key in TEAM_ALIASES:
        return TEAM_ALIASES[key]
    for alias, canon in TEAM_ALIASES.items():
        if norm_text(alias) and norm_text(alias) in key:
            return canon
    return None


def norm_park(name: Any) -> Optional[str]:
    key = norm_text(name)
    if not key:
        return None
    if key in PARK_ALIASES:
        return PARK_ALIASES[key]
    for alias, canon in PARK_ALIASES.items():
        if norm_text(alias) in key:
            return canon
    return None


def to_float(v: Any) -> Optional[float]:
    if v is None:
        return None
    s = norm_text(v).replace(",", "")
    if s in ("", "-", "--", "―", "‐", "----"):
        return None
    s = s.lstrip("+")
    m = re.match(r"^-?\d*\.?\d+$", s)
    if not m:
        # 「1.2」「.285」「3回1/3」など
        m2 = re.match(r"^(-?\d+)回(\d)/3$", s)
        if m2:
            return int(m2.group(1)) + int(m2.group(2)) / 3
        m3 = re.search(r"-?\d*\.?\d+", s)
        if not m3:
            return None
        s = m3.group(0)
    try:
        return float(s)
    except ValueError:
        return None


def to_int(v: Any) -> Optional[int]:
    f = to_float(v)
    return int(round(f)) if f is not None else None


def get(url: str, *, binary: bool = False) -> Optional[Any]:
    """リトライ付きGET。失敗したら None"""
    for i in range(RETRY):
        try:
            r = requests.get(url, headers={"User-Agent": UA,
                                           "Accept-Language": "ja,en;q=0.8"},
                             timeout=TIMEOUT)
            r.raise_for_status()
            if binary:
                return r.content
            r.encoding = r.apparent_encoding or r.encoding
            return r.text
        except Exception as e:  # noqa: BLE001
            log(f"  GET失敗({i + 1}/{RETRY}) {url} : {e}")
            time.sleep(SLEEP * (i + 1))
    return None


def read_tables(html: str) -> List["pd.DataFrame"]:
    if pd is None or not html:
        return []
    try:
        return pd.read_html(io.StringIO(html))
    except Exception as e:  # noqa: BLE001
        log(f"  表の読み取りに失敗: {e}")
        return []


def flatten_columns(df: "pd.DataFrame") -> "pd.DataFrame":
    """MultiIndexの列を1段にし、列名を正規化する"""
    cols = []
    for c in df.columns:
        if isinstance(c, tuple):
            parts = [norm_text(x) for x in c if "Unnamed" not in str(x)]
            cols.append(parts[-1] if parts else "")
        else:
            cols.append(norm_text(c) if "Unnamed" not in str(c) else "")
    df = df.copy()
    df.columns = cols
    return df


def pick(row: Dict[str, Any], *names: str) -> Any:
    """列名のゆらぎを吸収して値を取り出す"""
    for n in names:
        if n in row and row[n] is not None:
            return row[n]
    nrow = {norm_text(k): v for k, v in row.items()}
    for n in names:
        k = norm_text(n)
        if k in nrow and nrow[k] is not None:
            return nrow[k]
        for key, val in nrow.items():
            if key.startswith(k) and val is not None:
                return val
    return None


def load_previous() -> Dict[str, Any]:
    if not os.path.exists(OUT_PATH):
        return {}
    try:
        with open(OUT_PATH, encoding="utf-8") as f:
            return json.load(f)
    except Exception as e:  # noqa: BLE001
        log(f"  前回データの読み込みに失敗: {e}")
        return {}


# =====================================================================
# ① 順位表
# =====================================================================

def parse_standings(html: str, league: str) -> List[Dict[str, Any]]:
    out: List[Dict[str, Any]] = []
    for df in read_tables(html):
        df = flatten_columns(df)
        if df.empty or df.shape[1] < 5:
            continue
        recs = df.to_dict("records")
        first = recs[0]
        if norm_team(pick(first, "チーム", "球団", "順位")) is None and \
           not any(norm_team(v) for v in first.values()):
            continue
        for rec in recs:
            team = None
            for v in rec.values():
                team = norm_team(v)
                if team:
                    break
            if not team:
                continue
            w = to_int(pick(rec, "勝", "勝利", "試合勝"))
            l = to_int(pick(rec, "敗", "敗戦", "負"))
            d = to_int(pick(rec, "分", "引分", "引き分け"))
            if w is None or l is None:
                continue
            d = d or 0
            rf = to_int(pick(rec, "得点", "総得点"))
            ra = to_int(pick(rec, "失点", "総失点"))
            pct = to_float(pick(rec, "勝率"))
            if pct is None:
                pct = round(w / (w + l), 3) if (w + l) else 0.0
            item = {
                "team": team,
                "league": league,
                "g": to_int(pick(rec, "試合", "試")) or (w + l + d),
                "w": w, "l": l, "d": d,
                "pct": round(pct, 3),
                "gb": pick(rec, "差", "ゲーム差", "gb"),
                "rf": rf, "ra": ra,
                "run_diff": (rf - ra) if (rf is not None and ra is not None) else None,
                "home_rec": norm_text(pick(rec, "ホーム")) or None,
                "road_rec": norm_text(pick(rec, "ロード")) or None,
                "hr": to_int(pick(rec, "本塁打", "本")),
                "avg": to_float(pick(rec, "打率")),
                "era": to_float(pick(rec, "防御率")),
            }
            item["gb"] = norm_text(item["gb"]) if item["gb"] is not None else None
            if not any(x["team"] == team for x in out):
                out.append(item)
        if len(out) >= 6:
            break

    out.sort(key=lambda x: (-x["pct"], -x["w"]))
    for i, t in enumerate(out, 1):
        t["rank"] = i
        t["balance"] = t["w"] - t["l"]          # 貯金／借金
    return out[:6]


def fetch_standings() -> Dict[str, List[Dict[str, Any]]]:
    res: Dict[str, List[Dict[str, Any]]] = {}
    for league, page in (("セ", "std_c.html"),):
        url = NPB.format(season=SEASON, page=page)
        log(f"順位表({league}) {url}")
        html = get(url)
        time.sleep(SLEEP)
        rows = parse_standings(html or "", league)
        if rows:
            res[league] = rows
            log(f"  → {len(rows)}球団")
        else:
            log(f"  → 取得できず（前回値を使う）")
    return res


# =====================================================================
# ② NPB公式の月別日程ページを1枚読んで、結果・予告先発をまとめて取る
#    https://npb.jp/games/<season>/schedule_<MM>_detail.html
#    1ページに全球団の「対戦カード／スコア／球場／開始時間／予告先発」が
#    載っているので、ここを起点にすると取りこぼしが少ない。
# =====================================================================

SCHEDULE = "https://npb.jp/games/{season}/schedule_{mm}_detail.html"

_DATE_RE = re.compile(r"(\d{1,2})[/／](\d{1,2})")
_SCORE_RE = re.compile(r"^(.+?)(\d{1,2})\s*[-−–]\s*(\d{1,2})(.+)$")
_TIME_RE = re.compile(r"(\d{1,2}):(\d{2})")


def _split_card(text: str):
    """「巨人 7 - 8 DeNA」→ (巨人, 7, 8, DeNA) / 「阪神 - ヤクルト」→ (阪神, None, None, ヤクルト)"""
    t = norm_text(text)
    if not t:
        return None
    m = _SCORE_RE.match(t)
    if m:
        home, hs, as_, away = norm_team(m.group(1)), to_int(m.group(2)), to_int(m.group(3)), norm_team(m.group(4))
        if home and away:
            return home, hs, as_, away
    if "中止" in t:
        parts = [norm_team(x) for x in re.split(r"中止", t)]
        parts = [p for p in parts if p]
        if len(parts) == 2:
            return parts[0], None, None, parts[1]
    # スコア無し（これからの試合）。チーム名が2つ並んでいるはず
    found = []
    for m2 in re.finditer(r"[ぁ-んァ-ヶ一-龠ａ-ｚＡ-Ｚa-zA-Z]{2,10}", t):
        nm = norm_team(m2.group(0))
        if nm and nm not in found:
            found.append(nm)
    if len(found) == 2:
        return found[0], None, None, found[1]
    return None


def _split_starters(text: str):
    """「先発：下村 先発：高橋」→ (下村, 高橋)。責任投手（勝：/敗：）は無視"""
    t = norm_text(text)
    if not t or "先発" not in t:
        return None, None
    names = re.findall(r"先発[:：]([^\s先勝敗]{1,10})", t)
    if len(names) >= 2:
        return names[0], names[1]
    if len(names) == 1:
        return names[0], None
    return None, None


def fetch_month_games(month: int, season: int = None) -> List[Dict[str, Any]]:
    """月別日程ページから、その月の全試合を取り出す"""
    season = season or SEASON
    url = SCHEDULE.format(season=season, mm=f"{month:02d}")
    log(f"日程ページ {url}")
    html = get(url)
    time.sleep(SLEEP)
    if not html:
        return []
    games: List[Dict[str, Any]] = []
    cur_date = None
    for df in read_tables(html):
        df = flatten_columns(df)
        if df.shape[1] < 3:
            continue
        for rec in df.to_dict("records"):
            vals = [v for v in rec.values()]
            texts = [norm_text(v) for v in vals]
            # 日付
            for tx in texts[:1]:
                m = _DATE_RE.search(tx)
                if m:
                    cur_date = f"{int(m.group(1))}/{int(m.group(2))}"
            if not cur_date:
                continue
            # 対戦カード（チーム名が2つ入っているセル）
            card = None
            for tx in texts:
                got = _split_card(tx)
                if got and got[0] != got[3]:
                    card = got
                    break
            if not card:
                continue
            home, hs, as_, away = card
            # 球場と開始時間
            venue, start = None, None
            for tx in texts:
                pk = norm_park(tx)
                if pk and not venue:
                    venue = pk
                    tm = _TIME_RE.search(tx)
                    if tm:
                        start = f"{int(tm.group(1))}:{tm.group(2)}"
            sp_h, sp_a = None, None
            for tx in texts:
                a, b = _split_starters(tx)
                if a:
                    sp_h, sp_a = a, b
                    break
            games.append({"date": cur_date, "month": month, "home": home, "away": away,
                          "home_score": hs, "away_score": as_, "venue": venue,
                          "start_time": start, "home_starter": sp_h, "away_starter": sp_a})
    log(f"  → {len(games)}試合")
    return games


def load_season_games() -> List[Dict[str, Any]]:
    """今季の全試合（3月〜今月）を月別日程ページからまとめて読む。1回だけ実行してキャッシュ"""
    cached = globals().get("_SCHEDULE_CACHE")
    if cached:
        return cached
    today = datetime.now(JST).date()
    allg: List[Dict[str, Any]] = []
    for m in range(3, today.month + 1):
        allg.extend(fetch_month_games(m))
    globals()["_SCHEDULE_CACHE"] = allg
    return allg


def fetch_recent_form(days: int = 45) -> Dict[str, Dict[str, Any]]:
    """日程の結果から、球団ごとの直近10試合と連勝／連敗を作る"""
    allg = load_season_games()
    if not allg:
        return {}

    order = {m: i for i, m in enumerate(sorted({g["month"] for g in allg}))}

    def key(g):
        return (order.get(g["month"], 0), int(g["date"].split("/")[1]))

    results: Dict[str, List[bool]] = {}
    for g in sorted(allg, key=key):
        if g["home_score"] is None or g["away_score"] is None:
            continue
        if g["home_score"] == g["away_score"]:
            continue                        # 引き分けは連続記録に影響しない
        hw = g["home_score"] > g["away_score"]
        results.setdefault(g["home"], []).append(hw)
        results.setdefault(g["away"], []).append(not hw)

    form: Dict[str, Dict[str, Any]] = {}
    for team, seq in results.items():
        last10 = seq[-10:]
        w = sum(1 for x in last10 if x)
        n, t = 0, None
        for x in reversed(seq):
            if t is None:
                t, n = x, 1
            elif t == x:
                n += 1
            else:
                break
        form[team] = {
            "last10": {"w": w, "l": len(last10) - w, "d": 0},
            "streak": {"type": ("win" if t else "lose") if t is not None else None, "n": n,
                       "label": (f"{n}連勝" if t else f"{n}連敗") if t is not None else "—"},
        }
    log(f"直近10試合 → {len(form)}球団ぶん算出")
    return form


def fetch_park_stats() -> Dict[str, Dict[str, Any]]:
    """阪神の球場別成績（勝敗分・得点・失点）を今季の全試合から集計する"""
    allg = load_season_games()
    if not allg:
        return {}
    out: Dict[str, Dict[str, Any]] = {}
    for g in allg:
        if HOME_TEAM not in (g["home"], g["away"]):
            continue
        if g["home_score"] is None or g["away_score"] is None:
            continue
        park = g.get("venue")
        if not park:
            continue
        is_home = g["home"] == HOME_TEAM
        rf = g["home_score"] if is_home else g["away_score"]
        ra = g["away_score"] if is_home else g["home_score"]
        o = out.setdefault(park, {"g": 0, "w": 0, "l": 0, "d": 0, "rf": 0, "ra": 0, "home": is_home})
        o["g"] += 1
        o["rf"] += rf
        o["ra"] += ra
        if rf > ra:
            o["w"] += 1
        elif rf < ra:
            o["l"] += 1
        else:
            o["d"] += 1
    for park, o in out.items():
        n = o["w"] + o["l"]
        o["pct"] = round(o["w"] / n, 3) if n else None
        o["rf_avg"] = round(o["rf"] / o["g"], 2) if o["g"] else None
        o["ra_avg"] = round(o["ra"] / o["g"], 2) if o["g"] else None
    log(f"球場別成績 → {len(out)}球場ぶん集計")
    return out


# =====================================================================
# ③ チーム指標（打率・OPS・防御率）
# =====================================================================

def parse_team_table(html: str, kind: str) -> Dict[str, Dict[str, Any]]:
    out: Dict[str, Dict[str, Any]] = {}
    for df in read_tables(html):
        df = flatten_columns(df)
        for rec in df.to_dict("records"):
            team = None
            for v in rec.values():
                team = norm_team(v)
                if team:
                    break
            if not team:
                continue
            cur = out.setdefault(team, {})
            if kind == "bat":
                obp = to_float(pick(rec, "出塁率"))
                slg = to_float(pick(rec, "長打率"))
                avg = to_float(pick(rec, "打率"))
                if avg is not None:
                    cur["avg"] = round(avg, 3)
                if obp is not None and slg is not None:
                    cur["obp"] = round(obp, 3)
                    cur["slg"] = round(slg, 3)
                    cur["ops"] = round(obp + slg, 3)
                hr = to_int(pick(rec, "本塁打"))
                if hr is not None:
                    cur["hr"] = hr
                runs = to_int(pick(rec, "得点"))
                if runs is not None:
                    cur["runs"] = runs
            else:
                era = to_float(pick(rec, "防御率"))
                if era is not None:
                    cur["era"] = round(era, 2)
                so = to_int(pick(rec, "奪三振", "三振"))
                if so is not None:
                    cur["so"] = so
                whip_h = to_float(pick(rec, "被安打", "安打"))
                whip_bb = to_float(pick(rec, "与四球", "四球"))
                ip = to_float(pick(rec, "投球回"))
                if None not in (whip_h, whip_bb, ip) and ip:
                    cur["whip"] = round((whip_h + whip_bb) / ip, 2)
    return out


def fetch_team_stats() -> Dict[str, Dict[str, Any]]:
    stats: Dict[str, Dict[str, Any]] = {}
    pages = [("tmb_c.html", "bat"), ("tmp_c.html", "pit")]
    for page, kind in pages:
        url = NPB.format(season=SEASON, page=page)
        log(f"チーム{'打撃' if kind == 'bat' else '投手'}成績 {url}")
        html = get(url)
        time.sleep(SLEEP)
        for team, vals in parse_team_table(html or "", kind).items():
            stats.setdefault(team, {}).update(vals)
    log(f"  → {len(stats)}球団")
    return stats


# =====================================================================
# ④ 個人成績（野手・投手）
# =====================================================================

def calc_fip(hr: Optional[float], bb: Optional[float], hbp: Optional[float],
             so: Optional[float], ip: Optional[float]) -> Optional[float]:
    """FIP = (13*被HR + 3*(四球+死球) - 2*奪三振) / 投球回 + 3.20"""
    if ip is None or ip <= 0:
        return None
    hr, bb, hbp, so = (hr or 0), (bb or 0), (hbp or 0), (so or 0)
    return round((13 * hr + 3 * (bb + hbp) - 2 * so) / ip + FIP_CONST, 2)


def calc_woba(rec: Dict[str, Any]) -> Optional[float]:
    ab = to_float(pick(rec, "打数"))
    h = to_float(pick(rec, "安打"))
    d2 = to_float(pick(rec, "二塁打"))
    d3 = to_float(pick(rec, "三塁打"))
    hr = to_float(pick(rec, "本塁打"))
    bb = to_float(pick(rec, "四球"))
    hbp = to_float(pick(rec, "死球"))
    sf = to_float(pick(rec, "犠飛"))
    if None in (ab, h) or ab is None:
        return None
    d2, d3, hr = (d2 or 0), (d3 or 0), (hr or 0)
    bb, hbp, sf = (bb or 0), (hbp or 0), (sf or 0)
    b1 = max(h - d2 - d3 - hr, 0)
    denom = ab + bb + hbp + sf
    if denom <= 0:
        return None
    num = (WOBA_W["bb"] * bb + WOBA_W["hbp"] * hbp + WOBA_W["1b"] * b1 +
           WOBA_W["2b"] * d2 + WOBA_W["3b"] * d3 + WOBA_W["hr"] * hr)
    return round(num / denom, 3)


def parse_batters(html: str) -> List[Dict[str, Any]]:
    out = []
    for df in read_tables(html):
        df = flatten_columns(df)
        for rec in df.to_dict("records"):
            name = pick(rec, "選手", "選手名", "氏名")
            name = norm_text(name)
            if not name or name in ("選手", "選手名", "計", "合計") or len(name) > 12:
                continue
            avg = to_float(pick(rec, "打率"))
            pa = to_int(pick(rec, "打席"))
            ab = to_int(pick(rec, "打数"))
            if avg is None and ab is None:
                continue
            obp = to_float(pick(rec, "出塁率"))
            slg = to_float(pick(rec, "長打率"))
            out.append({
                "name": name,
                "g": to_int(pick(rec, "試合")),
                "pa": pa, "ab": ab,
                "h": to_int(pick(rec, "安打")),
                "hr": to_int(pick(rec, "本塁打")),
                "rbi": to_int(pick(rec, "打点")),
                "sb": to_int(pick(rec, "盗塁")),
                "bb": to_int(pick(rec, "四球")),
                "so": to_int(pick(rec, "三振")),
                "avg": avg, "obp": obp, "slg": slg,
                "ops": round(obp + slg, 3) if (obp is not None and slg is not None) else None,
                "woba": calc_woba(rec),
            })
        if out:
            break
    # 打席数の多い順（規定打席の代わり）
    out.sort(key=lambda x: (-(x.get("pa") or x.get("ab") or 0)))
    return out[:20]


def parse_pitchers(html: str) -> List[Dict[str, Any]]:
    out = []
    for df in read_tables(html):
        df = flatten_columns(df)
        for rec in df.to_dict("records"):
            name = norm_text(pick(rec, "選手", "選手名", "氏名"))
            if not name or name in ("選手", "選手名", "計", "合計") or len(name) > 12:
                continue
            ip = to_float(pick(rec, "投球回"))
            era = to_float(pick(rec, "防御率"))
            if ip is None and era is None:
                continue
            h = to_float(pick(rec, "被安打", "安打"))
            bb = to_float(pick(rec, "与四球", "四球"))
            hbp = to_float(pick(rec, "与死球", "死球"))
            so = to_float(pick(rec, "奪三振", "三振"))
            hr = to_float(pick(rec, "被本塁打", "本塁打"))
            whip = round((h + bb) / ip, 2) if (h is not None and bb is not None and ip) else None
            out.append({
                "name": name,
                "g": to_int(pick(rec, "試合", "登板")),
                "gs": to_int(pick(rec, "先発")),
                "w": to_int(pick(rec, "勝利", "勝")),
                "l": to_int(pick(rec, "敗戦", "敗")),
                "sv": to_int(pick(rec, "セーブ", "S")),
                "hld": to_int(pick(rec, "ホールド", "H")),
                "ip": round(ip, 1) if ip is not None else None,
                "era": era, "whip": whip,
                "so": to_int(so), "bb": to_int(bb), "hr": to_int(hr),
                "fip": calc_fip(hr, bb, hbp, so, ip),
            })
        if out:
            break
    out.sort(key=lambda x: -(x.get("ip") or 0))
    return out[:20]


def fetch_players(teams: List[str]) -> Dict[str, Dict[str, List[Dict[str, Any]]]]:
    """球団別の個人成績（NPB公式のチーム別ページ）"""
    res: Dict[str, Dict[str, List[Dict[str, Any]]]] = {}
    for team in teams:
        code = TEAM_CODE.get(team)
        if not code:
            continue
        bat_url = NPB.format(season=SEASON, page=f"idb1_{code}.html")
        pit_url = NPB.format(season=SEASON, page=f"idp1_{code}.html")
        log(f"個人成績 {team}")
        bat = parse_batters(get(bat_url) or "")
        time.sleep(SLEEP)
        pit = parse_pitchers(get(pit_url) or "")
        time.sleep(SLEEP)
        if bat or pit:
            res[team] = {"batters": bat, "pitchers": pit}
            log(f"  → 野手{len(bat)}人 / 投手{len(pit)}人")
        else:
            log("  → 取得できず")
    return res


# =====================================================================
# ⑤ 予告先発と試合条件
# =====================================================================

def _resolve_pitcher(short: Optional[str], roster: List[Dict[str, Any]]) -> Optional[str]:
    """「下村」→「下村 海翔」。同じ球団の登録投手から姓で引き当てる"""
    if not short:
        return None
    key = norm_text(short)
    if not key:
        return None
    for p in roster or []:
        nm = norm_text(p.get("name"))
        if nm == key or nm.startswith(key) or key.startswith(nm):
            return p.get("name")
    return short


def fetch_probables(target: date) -> List[Dict[str, Any]]:
    """月別日程ページから、その日の阪神戦（カード・球場・予告先発）を取る"""
    key = f"{target.month}/{target.day}"
    games = load_season_games() or fetch_month_games(target.month)
    rows = [g for g in games
            if g["date"] == key and HOME_TEAM in (g["home"], g["away"])]
    if not rows:
        log(f"予告先発: {key} の{HOME_TEAM}戦は日程に見つからず")
        return []
    g = rows[0]
    is_home = g["home"] == HOME_TEAM
    opp = g["away"] if is_home else g["home"]
    item = {
        "date": target.isoformat(),
        "opponent": opp,
        "card": f"対{opp}",
        "venue": g.get("venue"),
        "home": is_home,
        "start_time": g.get("start_time") or "18:00",
        "hanshin_pitcher": g["home_starter"] if is_home else g["away_starter"],
        "opponent_pitcher": g["away_starter"] if is_home else g["home_starter"],
        "score": ([g["home_score"], g["away_score"]] if is_home else [g["away_score"], g["home_score"]])
                 if g["home_score"] is not None else None,
    }
    log(f"予告先発: {item['card']} @{item['venue']} "
        f"{item['hanshin_pitcher']} vs {item['opponent_pitcher']}")
    return [item]


# =====================================================================
# ⑥ 天気・浜風
# =====================================================================

def hamakaze_component(speed: Optional[float], direction: Optional[float],
                       park: str) -> float:
    """風向を球場の浜風軸に射影して、浜風ぶんの風速(m/s)を返す"""
    cfg = PARKS.get(park) or {}
    if cfg.get("dome") or speed is None or direction is None:
        return 0.0
    base = cfg.get("hamakaze_from")
    if base is None:
        return 0.0
    diff = math.radians((direction - base + 180) % 360 - 180)
    return round(max(0.0, speed * math.cos(diff)), 1)


def fetch_weather(park: Optional[str], target: date,
                  hour: int = 18) -> Optional[Dict[str, Any]]:
    if not park or park not in PARKS:
        return None
    cfg = PARKS[park]
    if cfg.get("dome"):
        return {"park": park, "dome": True, "text": "ドーム", "wind_speed": 0, "hamakaze": 0}
    url = ("https://api.open-meteo.com/v1/forecast"
           f"?latitude={cfg['lat']}&longitude={cfg['lon']}"
           "&hourly=temperature_2m,precipitation_probability,wind_speed_10m,wind_direction_10m"
           "&wind_speed_unit=ms&timezone=Asia%2FTokyo&forecast_days=7")
    log(f"天気 {park}")
    raw = get(url)
    if not raw:
        return None
    try:
        js = json.loads(raw)
        stamp = f"{target.isoformat()}T{hour:02d}:00"
        idx = js["hourly"]["time"].index(stamp)
    except Exception as e:  # noqa: BLE001
        log(f"  天気の解析に失敗: {e}")
        return None
    h = js["hourly"]
    speed = h["wind_speed_10m"][idx]
    direction = h["wind_direction_10m"][idx]
    return {
        "park": park,
        "dome": False,
        "temp": h["temperature_2m"][idx],
        "pop": h["precipitation_probability"][idx],
        "wind_speed": round(speed, 1),
        "wind_deg": direction,
        "hamakaze": hamakaze_component(speed, direction, park),
        "at": stamp,
    }


# =====================================================================
# 組み立て
# =====================================================================

def build(target: date) -> Dict[str, Any]:
    prev = load_previous()
    now = datetime.now(JST)

    data: Dict[str, Any] = {
        "updated_at": now.isoformat(timespec="seconds"),
        "season": SEASON,
        "target_date": target.isoformat(),
        "sources": {
            "standings": "npb.jp",
            "team_stats": "npb.jp",
            "players": "npb.jp",
            "probables": "baseball.yahoo.co.jp",
            "weather": "open-meteo.com",
        },
        "errors": [],
    }

    def section(key: str, fn, default):
        try:
            val = fn()
        except Exception as e:  # noqa: BLE001
            log(f"!! {key} で例外: {e}")
            data["errors"].append(f"{key}: {e}")
            val = None
        if not val:
            data["errors"].append(f"{key}: 取得できず前回値を使用")
            return prev.get(key, default)
        return val

    # 順位表
    standings = section("standings", fetch_standings, {})
    for lg in ("セ",):
        if lg not in standings and prev.get("standings", {}).get(lg):
            standings[lg] = prev["standings"][lg]

    # 直近10試合・連勝連敗をマージ
    form = section("form", fetch_recent_form, {})
    for lg, rows in standings.items():
        for row in rows:
            f = (form or {}).get(row["team"])
            if f:
                row.update(f)
            # 取れなかった場合は入れない（サイト側の登録値がそのまま生きる）
    data["standings"] = standings

    # チーム指標
    data["team_stats"] = section("team_stats", fetch_team_stats, {})

    # 個人成績（阪神＋今日の対戦相手）
    probables = section("probables", lambda: fetch_probables(target), [])
    data["probables"] = probables
    focus = ["阪神"]
    if probables and probables[0].get("opponent"):
        focus.append(probables[0]["opponent"])
    data["players"] = section("players", lambda: fetch_players(focus), {})

    # 予告先発のFIPを個人成績から引く
    fip_index: Dict[str, float] = {}
    for team, sets in (data.get("players") or {}).items():
        for p in sets.get("pitchers", []):
            if p.get("fip") is not None:
                fip_index[p["name"]] = p["fip"]
    for g in data["probables"]:
        for side, team_key in (("hanshin", HOME_TEAM), ("opponent", g.get("opponent"))):
            roster = ((data.get("players") or {}).get(team_key) or {}).get("pitchers", [])
            full = _resolve_pitcher(g.get(f"{side}_pitcher"), roster)
            if full:
                g[f"{side}_pitcher"] = full
            g[f"{side}_fip"] = fip_index.get(full) if full else None
        # 天気
        hour = int((g.get("start_time") or "18:00").split(":")[0])
        w = fetch_weather(g.get("venue"), target, hour)
        if w:
            g["weather"] = w
            g["wind"] = w.get("hamakaze", 0)

    data["fip_index"] = fip_index

    # 対戦成績（阪神から見た球団別）
    data["h2h"] = section("h2h", lambda: fetch_h2h(), prev.get("h2h", {}))

    # 球場別成績（阪神）
    data["park_stats"] = section("park_stats", fetch_park_stats, prev.get("park_stats", {}))

    return data


# 勝敗表の「対神／対巨／対デ…」列を球団名に戻す
H2H_COLS = {"対神": "阪神", "対巨": "巨人", "対デ": "ＤｅＮＡ",
            "対ヤ": "ヤクルト", "対広": "広島", "対中": "中日"}


def fetch_h2h() -> Dict[str, Dict[str, int]]:
    """セ・リーグ勝敗表の対戦成績欄から、阪神の球団別成績を取り出す"""
    url = NPB.format(season=SEASON, page="std_c.html")
    log(f"対戦成績 {url}")
    html = get(url)
    time.sleep(SLEEP)
    if not html:
        return {}
    out: Dict[str, Dict[str, int]] = {}
    for df in read_tables(html):
        df = flatten_columns(df)
        cols = list(df.columns)
        if not any(c in H2H_COLS for c in cols):
            continue
        for rec in df.to_dict("records"):
            row_team = None
            for v in rec.values():
                row_team = norm_team(v)
                if row_team:
                    break
            if row_team != HOME_TEAM:
                continue
            for col, val in rec.items():
                opp = H2H_COLS.get(norm_text(col))
                if not opp or opp == HOME_TEAM:
                    continue
                t = norm_text(val)
                m = re.match(r"^(\d+)[-−–](\d+)(?:\((\d+)\))?$", t)
                if m:
                    out[opp] = {"w": int(m.group(1)), "l": int(m.group(2)),
                                "d": int(m.group(3) or 0)}
        if out:
            break
    log(f"  → {len(out)}球団ぶん")
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--date", help="対象日 YYYY-MM-DD（既定は今日）")
    ap.add_argument("--dry-run", action="store_true", help="保存せず標準出力に出す")
    ap.add_argument("--out", default=OUT_PATH)
    args = ap.parse_args()

    target = (datetime.strptime(args.date, "%Y-%m-%d").date()
              if args.date else datetime.now(JST).date())
    log(f"=== {target} のデータを収集します（{SEASON}年） ===")

    data = build(target)

    if data["errors"]:
        log("警告:")
        for e in data["errors"]:
            log("  - " + e)

    text = json.dumps(data, ensure_ascii=False, indent=2, sort_keys=False)
    if args.dry_run:
        print(text)
        return 0

    os.makedirs(os.path.dirname(args.out), exist_ok=True)
    # 中身が同じなら書かない（無駄なコミットを作らない）
    if os.path.exists(args.out):
        try:
            with open(args.out, encoding="utf-8") as f:
                old = json.load(f)
            old.pop("updated_at", None)
            new = json.loads(text)
            new.pop("updated_at", None)
            if old == new:
                log("前回と同じ内容のため書き込みをスキップしました")
                return 0
        except Exception:  # noqa: BLE001
            pass

    with open(args.out, "w", encoding="utf-8") as f:
        f.write(text + "\n")
    log(f"保存しました → {args.out}")

    # 主要な中身を最後に表示（Actionsのログで確認できるように）
    cen = data.get("standings", {}).get("セ", [])
    if cen:
        log("セ・リーグ順位:")
        for t in cen:
            log(f"  {t['rank']}位 {t['team']} {t['w']}勝{t['l']}敗{t['d']}分 "
                f"勝率{t['pct']:.3f} 直近10 {t.get('last10', {}).get('w', '-')}勝")
    ps = data.get("park_stats") or {}
    if ps:
        log("球場別成績（阪神）:")
        for park, o in sorted(ps.items(), key=lambda x: -x[1]["g"]):
            log(f"  {park} {o['g']}試合 {o['w']}勝{o['l']}敗{o['d']}分 "
                f"得点{o['rf_avg']} 失点{o['ra_avg']}")
    for g in data.get("probables", []):
        log(f"予告先発: {g['card']} @{g.get('venue')} "
            f"{g.get('hanshin_pitcher')}({g.get('hanshin_fip')}) vs "
            f"{g.get('opponent_pitcher')}({g.get('opponent_fip')}) "
            f"浜風 {g.get('wind')}m/s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
