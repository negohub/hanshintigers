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
SEASON = int(os.environ.get("NPB_SEASON", datetime.now(JST).year))

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
# ② 直近10試合・連勝／連敗（日程結果から算出）
# =====================================================================

def fetch_recent_form(days: int = 45) -> Dict[str, Dict[str, Any]]:
    """スポーツナビの日別スコアから、球団ごとの直近10試合と連勝/連敗を作る"""
    if BeautifulSoup is None:
        log("直近10試合: BeautifulSoup が無いのでスキップ")
        return {}
    results: Dict[str, List[Dict[str, Any]]] = {}
    today = datetime.now(JST).date()
    got = 0
    for i in range(1, days + 1):
        d = today - timedelta(days=i)
        url = f"https://baseball.yahoo.co.jp/npb/schedule/?date={d.isoformat()}"
        html = get(url)
        time.sleep(0.4)
        if not html:
            continue
        got += 1
        soup = BeautifulSoup(html, "html.parser")
        text = soup.get_text("\n")
        # 「巨人 3 - 2 阪神」のような並びを拾う
        for m in re.finditer(r"([^\n\d]{2,10}?)\s*(\d{1,2})\s*[-−]\s*(\d{1,2})\s*([^\n\d]{2,10})", text):
            a, sa, sb, b = norm_team(m.group(1)), to_int(m.group(2)), to_int(m.group(3)), norm_team(m.group(4))
            if not a or not b or a == b or sa is None or sb is None:
                continue
            for team, mine, opp in ((a, sa, sb), (b, sb, sa)):
                results.setdefault(team, []).append(
                    {"date": d.isoformat(), "mine": mine, "opp": opp})
    if not got:
        return {}

    form: Dict[str, Dict[str, Any]] = {}
    for team, games in results.items():
        # 日付昇順にして重複を除く
        seen, uniq = set(), []
        for g in sorted(games, key=lambda x: x["date"]):
            key = (g["date"], g["mine"], g["opp"])
            if key in seen:
                continue
            seen.add(key)
            uniq.append(g)
        last10 = uniq[-10:]
        w = sum(1 for g in last10 if g["mine"] > g["opp"])
        l = sum(1 for g in last10 if g["mine"] < g["opp"])
        dr = len(last10) - w - l
        streak_n, streak_type = 0, None
        for g in reversed(uniq):
            if g["mine"] == g["opp"]:
                continue
            t = "win" if g["mine"] > g["opp"] else "lose"
            if streak_type is None:
                streak_type, streak_n = t, 1
            elif streak_type == t:
                streak_n += 1
            else:
                break
        form[team] = {
            "last10": {"w": w, "l": l, "d": dr},
            "streak": {"type": streak_type, "n": streak_n,
                       "label": (f"{streak_n}連勝" if streak_type == "win"
                                 else f"{streak_n}連敗" if streak_type == "lose" else "—")},
        }
    log(f"直近10試合 → {len(form)}球団ぶん算出")
    return form


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

def fetch_probables(target: date) -> List[Dict[str, Any]]:
    """スポーツナビの日程ページから阪神戦の予告先発を拾う"""
    if BeautifulSoup is None:
        log("予告先発: BeautifulSoup が無いのでスキップ")
        return []
    url = f"https://baseball.yahoo.co.jp/npb/schedule/?date={target.isoformat()}"
    log(f"予告先発 {url}")
    html = get(url)
    if not html:
        return []
    soup = BeautifulSoup(html, "html.parser")
    games: List[Dict[str, Any]] = []

    for card in soup.select("li, tr, div"):
        text = card.get_text(" ", strip=True)
        if "阪神" not in text or len(text) > 400:
            continue
        teams = []
        for m in re.finditer(r"[ぁ-んァ-ヶ一-龠ａ-ｚA-Za-z]{2,12}", text):
            t = norm_team(m.group(0))
            if t and t not in teams:
                teams.append(t)
        if len(teams) < 2 or "阪神" not in teams:
            continue
        park = norm_park(text)
        tm = re.search(r"(\d{1,2}):(\d{2})", text)
        # 「先発 才木 － 戸郷」のような並び
        pitchers = re.findall(r"(?:先発|予告)?[\s:：]*([一-龠ぁ-んァ-ヶA-Za-zー・]{2,10})\s*[－\-–]\s*([一-龠ぁ-んァ-ヶA-Za-zー・]{2,10})", text)
        opp = [t for t in teams if t != "阪神"][0]
        home_first = teams[0] != "阪神"     # スポナビは「ビジター vs ホーム」表記
        item = {
            "date": target.isoformat(),
            "opponent": opp,
            "card": f"対{opp}",
            "venue": park,
            "home": (park == "甲子園"),
            "start_time": f"{tm.group(1)}:{tm.group(2)}" if tm else "18:00",
            "hanshin_pitcher": None,
            "opponent_pitcher": None,
            "_raw": text[:200],
        }
        if pitchers:
            a, b = pitchers[0]
            if home_first:
                item["opponent_pitcher"], item["hanshin_pitcher"] = a, b
            else:
                item["hanshin_pitcher"], item["opponent_pitcher"] = a, b
        games.append(item)
        break

    if not games:
        log("  → 阪神戦の予告先発は見つからず")
    return games


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
        return {"park": park, "dome": True, "text": "ドーム", "wind_speed": 0,
                "hamakaze": 0, "pop": 0}
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
            elif not row.get("last10"):
                row["last10"] = {"w": 5, "l": 5, "d": 0}
                row["streak"] = {"type": None, "n": 0, "label": "—"}
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
        for side, team_key in (("hanshin", "阪神"), ("opponent", g.get("opponent"))):
            name = g.get(f"{side}_pitcher")
            if not name:
                continue
            hit = fip_index.get(name)
            if hit is None:
                for k, v in fip_index.items():
                    if name in k or k in name:
                        hit = v
                        break
            g[f"{side}_fip"] = hit
        # 天気
        hour = int((g.get("start_time") or "18:00").split(":")[0])
        w = fetch_weather(g.get("venue"), target, hour)
        if w:
            g["weather"] = w
            g["wind"] = w.get("hamakaze", 0)

    data["fip_index"] = fip_index

    # 対戦成績（阪神から見た球団別）
    data["h2h"] = section("h2h", lambda: fetch_h2h(), prev.get("h2h", {}))

    return data


def fetch_h2h() -> Dict[str, Dict[str, int]]:
    """NPB公式のチーム別対戦成績表から、阪神の対戦成績を取り出す"""
    url = NPB.format(season=SEASON, page="std_ci.html")   # セ・リーグ 対戦成績
    log(f"対戦成績 {url}")
    html = get(url)
    time.sleep(SLEEP)
    if not html:
        return {}
    out: Dict[str, Dict[str, int]] = {}
    for df in read_tables(html):
        df = flatten_columns(df)
        for rec in df.to_dict("records"):
            row_team = None
            for v in rec.values():
                row_team = norm_team(v)
                if row_team:
                    break
            if row_team != "阪神":
                continue
            for col, val in rec.items():
                opp = norm_team(col)
                if not opp or opp == "阪神":
                    continue
                m = re.match(r"^(\d+)\D+(\d+)\D+(\d+)$", norm_text(val))
                if m:
                    out[opp] = {"w": int(m.group(1)), "l": int(m.group(2)),
                                "d": int(m.group(3))}
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
    for g in data.get("probables", []):
        log(f"予告先発: {g['card']} @{g.get('venue')} "
            f"{g.get('hanshin_pitcher')}({g.get('hanshin_fip')}) vs "
            f"{g.get('opponent_pitcher')}({g.get('opponent_fip')}) "
            f"浜風 {g.get('wind')}m/s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
