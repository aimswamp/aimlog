#!/usr/bin/env python3
"""
ショート動画（YouTube Shorts / TikTok）自動合成スクリプト (Phase 2)
- `data/articles.json` の記事から `short_script` を取得
- ローカルで起動中の VOICEVOX Engine (http://127.0.0.1:50021) でセリフ音声を合成
  - ずんだもん (ノーマル: speaker=3)
  - 春日部つむぎ (ノーマル: speaker=8)
- `assets/bg/` 内の手元のAIM練習プレイ動画 (MP4) をランダムな開始位置からシーク＆背景ループ＆縦型 (1080x1920) にクロップ（背景動画の元音声はミュート）
- `assets/bgm/` のBGMと、`assets/se/` の効果音（冒頭フック・話者切り替え・重要ポイント強調）を自動ミックス
- 画面中央のクロスヘア・ターゲットを一切隠さない上下分離レイアウト：
  - 上部: 省略なしの全文記事タイトル（角丸の半透明黒座布団つき大文字）＋ 登場デバイス＆評価ポップアップバッジ
  - 下部: 話者タグを省いて文字サイズを最大化したセリフテロップ（話者別カラーの角丸黒座布団つき）
"""

from __future__ import annotations

import datetime as dt
import http.server
import json
import math
import os
import random
import re
import shutil
import struct
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request
import wave
import webbrowser
from pathlib import Path
from typing import Any

VOICEVOX_URL = "http://127.0.0.1:50021"
SPEAKER_MAP = {
    "zundamon": 3,   # ずんだもん（ノーマル）
    "tsumugi": 8,    # 春日部つむぎ（ノーマル）
    "aoyama": 8,     # 旧データの aoyama も春日部つむぎに自動マッピング
}

# ショート動画向けのテンポ設定（平均視聴率70%超えを狙う1.24倍速・文末の間0.06秒で小気味よく進行）
VOICE_SPEED_SCALE = 1.24
VOICE_POST_PHONEME_LENGTH = 0.06

# ミックス音量設定
VOICE_VOLUME = 1.25
BGM_VOLUME = 0.15
SE_VOLUME = 0.80
# 最初のずんだもんのセリフはディレイなし（0.0秒）で即座に開始する
HOOK_LEAD_SEC = 0.0
# `assets/se/` にユーザーが置ける音声ファイルの拡張子（同名の自動生成 .wav より優先）
SE_USER_EXTS = (".mp3", ".ogg", ".m4a", ".flac", ".wav")
# 効果音ラボの定番SE URL（未配置時に Referer 付きで自動取得を試みる）
SOUNDEFFECT_LAB_URLS = {
    "hook": (
        "https://soundeffect-lab.info/sound/various/mp3/cork-plug1.mp3",
        "https://soundeffect-lab.info/sound/anime/",
    ),  # スポッ（冒頭フック）
    "point": (
        "https://soundeffect-lab.info/sound/anime/mp3/pa1.mp3",
        "https://soundeffect-lab.info/sound/anime/",
    ),  # パッ（重要ポイント表示）
}

ENV_FILE = Path(".env")
ARTICLES_FILE = Path("data/articles.json")
SHORTS_HISTORY_FILE = Path("data/shorts_history.json")
BG_DIR = Path("assets/bg")
BGM_DIR = Path("assets/bgm")
SE_DIR = Path("assets/se")
SHORTS_OUT_DIR = Path("dist/shorts")

# YouTube Data API v3 の無料クォータ (10,000 units/day, 1本あたり約1,600 units = 最大6本/日) を考慮した1回あたりの上限
DEFAULT_MAX_UPLOADS_PER_RUN = 5
YOUTUBE_OAUTH_SCOPE = "https://www.googleapis.com/auth/youtube.upload"
# ショートフィードの連投ロック（1〜2回再生止まり）を防ぎ、日本のFPS層がアクティブな時間帯に1本ずつ公開するJST時刻スロット
YOUTUBE_SCHEDULE_SLOTS_JST: list[tuple[int, int]] = [
    (7, 30),   # 朝の通勤・通学枠
    (12, 15),  # 昼休み枠
    (18, 0),   # 夕方の帰宅・放課後枠
    (21, 0),   # 夜のゴールデンタイム枠
]
YOUTUBE_MIN_GAP_HOURS = 4.0


# VOICEVOX がアルファベット綴り読み（A-R-T-I-S-A-N 等）や誤読（キーチロン等）するのを防ぐ読み仮名辞書
VOICEVOX_READING_RULES: list[tuple[str, str]] = [
    (r"(?i)\bARTISAN\b", "アーティザン"),
    (r"(?i)\bRaiden\b", "ライデン"),
    (r"(?i)\bHayate\s*Otsu\b", "ハヤテオツ"),
    (r"(?i)\bHien\b", "ヒエン"),
    (r"(?i)\bKeychron\s*M6\b", "キークロン エムシックス"),
    (r"(?i)\bKeychron\b", "キークロン"),
    (r"(?i)\bMX\s*Master\s*3S\b", "エムエックスマスター スリーエス"),
    (r"(?i)\bMX\s*Master\s*4\b", "エムエックスマスター フォー"),
    (r"(?i)\bMX\s*Master\b", "エムエックスマスター"),
    (r"(?i)\bLogicool\b", "ロジクール"),
    (r"(?i)\bLogitech\b", "ロジクール"),
    (r"(?i)\bG\s*PRO\s*X\s*SUPERLIGHT\s*2\b", "ジープロエックス スーパーライトツー"),
    (r"(?i)\bG\s*PRO\s*X\s*SUPERLIGHT\b", "ジープロエックス スーパーライト"),
    (r"(?i)\bG\s*Pro\s*Superlight\s*2\b", "ジープロ スーパーライトツー"),
    (r"(?i)\bG\s*Pro\s*Superlight\b", "ジープロ スーパーライト"),
    (r"(?i)\bSUPERLIGHT\s*2\b", "スーパーライトツー"),
    (r"(?i)\bSUPERLIGHT\b", "スーパーライト"),
    (r"(?i)\bSuperstrike\s*Pro\s*X3\b", "スーパーストライク プロ エックススリー"),
    (r"(?i)\bSuperstrike\s*X3\b", "スーパーストライク エックススリー"),
    (r"(?i)\bSuperstrike\b", "スーパーストライク"),
    (r"(?i)\bG502\s*X\b", "ジーゴーマルニ エックス"),
    (r"(?i)\bG740\b", "ジーナナヨンマル"),
    (r"(?i)\bViper\s*V4\s*Pro\b", "ヴァイパー ブイフォープロ"),
    (r"(?i)\bViper\s*V3\s*Pro\b", "ヴァイパー ブイスリープロ"),
    (r"(?i)\bViper\s*Ultimate\b", "ヴァイパー アルティメット"),
    (r"(?i)\bViper\b", "ヴァイパー"),
    (r"(?i)\bDeathAdder\s*V3\s*Pro\b", "デスアダー ブイスリープロ"),
    (r"(?i)\bDeathAdder\b", "デスアダー"),
    (r"(?i)\bBasilisk\s*V3\b", "バシリスク ブイスリー"),
    (r"(?i)\bRazer\b", "レイザー"),
    (r"(?i)\bWallhack\s*SP-004\b", "ウォールハック エスピーゼロゼロヨン"),
    (r"(?i)\bWallhack\b", "ウォールハック"),
    (r"(?i)\bSP-004\b", "エスピーゼロゼロヨン"),
    (r"(?i)\bSP-005\b", "エスピーゼロゼロゴ"),
    (r"(?i)\bSuperglide\b", "スーパーグライド"),
    (r"(?i)\bPulsar\b", "パルサー"),
    (r"(?i)\bKovaaK'?s\b", "コバークス"),
    (r"(?i)\bAimlabs?\b", "エイムラボ"),
    (r"(?i)\bVoltaic\b", "ボルチック"),
    (r"(?i)\bX-?raypad\b", "エックスレイパッド"),
    (r"(?i)\bU9\s*titanium\b", "ユーナイン チタン"),
    (r"(?i)\bJade\s*Skates\b", "ジェイドスケート"),
    (r"(?i)\bJade\b", "ジェイド"),
    (r"(?i)\bCorepad\b", "コアパッド"),
    (r"(?i)\bZOWIE\b", "ゾーイ"),
    (r"(?i)\bLamzu\b", "ラムズ"),
    (r"(?i)\bNinjutso\s*Sora\s*V2\b", "ニンジュツォ ソラブイツー"),
    (r"(?i)\bEndgame\s*Gear\b", "エンドゲームギア"),
    (r"(?i)\bOP1\s*8k\b", "オーピーワン エイトケー"),
    (r"(?i)\bOP1\b", "オーピーワン"),
    (r"(?i)\bXM1r?\b", "エックスエムワン"),
    (r"(?i)\bTOPO\s*Glass\b", "トポ グラス"),
    (r"(?i)\bTOPO\b", "トポ"),
    (r"(?i)\bMoonstone\s*Ace\b", "ムーンストーン エース"),
    (r"(?i)\bASUS\b", "エイスース"),
    (r"(?i)\bDarmoshark\s*M9\b", "ダーモシャーク エムナイン"),
    (r"(?i)\bDarmoshark\b", "ダーモシャーク"),
    (r"(?i)\bG-?Wolves\b", "ジーウルブズ"),
    (r"(?i)\bFenrir\s*Asym\b", "フェンリル アシム"),
    (r"(?i)\bFenrir\b", "フェンリル"),
    (r"(?i)\bFlickshot\b", "フリックショット"),
    (r"(?i)\bMX518\b", "エムエックス ゴーイチハチ"),
    (r"(?i)\bIE\s*3\.0\b", "アイイー サンテンゼロ"),
    (r"(?i)\bMad\s*Catz\b", "マッドキャッツ"),
    (r"(?i)\bR\.?A\.?T\.?\s*8\+", "ラット エイトプラス"),
    (r"(?i)\bR\.?A\.?T\.?\b", "ラット"),
    (r"(?i)\bBest\s*Buy\b", "ベストバイ"),
    (r"(?i)\bEloShapes\b", "エロシェイプス"),
    (r"(?i)\bPMM\b", "ピーエムエム"),
    (r"(?i)\bHITS\b", "ヒッツ"),
    (r"(?i)\bPING\b", "ピン"),
    (r"(?i)\bPTFE\b", "ピーティーエフイー"),
    (r"(?i)\bUPE\b", "ユーピーイー"),
    (r"(?i)\bCS2\b", "シーエスツー"),
    (r"(?i)\bVALORANT\b", "ヴァロラント"),
    (r"(?i)\bOverwatch\b", "オーバーウォッチ"),
    (r"(?i)\bOW\b", "オーバーウォッチ"),
    (r"(?i)\bApex\b", "エイペックス"),
    (r"(?i)\bSojourn\b", "ソジョーン"),
    (r"(?i)\bAshe\b", "アッシュ"),
    (r"(?i)\bWindows\b", "ウィンドウズ"),
    (r"(?i)\bPC\b", "ピーシー"),
    (r"(?i)\bFPS\b", "エフピーエス"),
    (r"(?i)\bTTK\b", "ティーティーケー"),
    (r"(?i)\b1440p\b", "イチヨンヨンゼロピー"),
    (r"(?i)\b1080p\b", "フルエイチディー"),
    (r"(?i)\b8K\b", "エイトケー"),
    (r"(?i)\b4K\b", "フォーケー"),
    (r"(?i)\bcm/360\b", "振り向き"),
    (r"(\d+)\s*[Hh]z\b", r"\1ヘルツ"),
    (r"(\d+)\s*ms\b", r"\1ミリ秒"),
    (r"(\d+)\s*g(?!\w)", r"\1グラム"),
    (r"(?i)(\d+)\s*e?DPI", r"\1ディーピーアイ"),
    (r"(?i)\be?DPI\b", "ディーピーアイ"),
]


def to_voicevox_reading(text: str) -> str:
    """字幕用の表記は崩さず、VOICEVOX に渡す読み上げテキストだけ自然なカナに変換する。"""
    out = text
    for pattern, repl in VOICEVOX_READING_RULES:
        # 日本語文字（助詞の「の」「が」等）が直後に続いても \b が境界として機能するよう re.ASCII を指定
        out = re.sub(pattern, repl, out, flags=re.ASCII)
    return out


def normalize_tsumugi_tone(text: str) -> str:
    """旧 aoyama 用の硬い文末（「〜である」「〜だな」「〜だぞ」等）を春日部つむぎの自然な口調に整える。"""
    t = text.strip()
    replacements = [
        ("無難である。", "無難だよ！"),
        ("べきである。", "のがおすすめだよ！"),
        ("推奨されている。", "おすすめされてるよ！"),
        ("である。", "だよ！"),
        ("存在しないな。", "存在しないんだよね。"),
        ("寿命だな。", "寿命なんだよね。"),
        ("注意が必要だな。", "注意してね！"),
        ("必要だな。", "必要だよ！"),
        ("だな。", "だね！"),
        ("ないぞ。", "ないよ！"),
        ("完成するぞ。", "完成するよ！"),
        ("選択だぞ。", "選び方だね！"),
        ("だぞ。", "だよ！"),
        ("からだ。", "からなんだよね。"),
        ("調整しろ。", "調整してね！"),
        ("注意しろ。", "気をつけてね！"),
        ("掴むのだ。", "掴むといいよ！"),
        ("になるのだ。", "になるよ！"),
        ("跳ね上がる。", "上がるよ！"),
        ("軽減できる。", "減らせるよ！"),
        ("候補になる。", "候補になるよ！"),
        ("力みだ。", "力みなんだよね。"),
        ("重要だ。", "大事だよ！"),
    ]
    for old, new in replacements:
        if t.endswith(old):
            t = t[: -len(old)] + new
            break
    t = t.replace("結論から言えば、", "結論から言うと、").replace("だがプレイ前", "でもプレイ前")
    return t


def _char_visual_width(c: str) -> float:
    """半角英数字は 0.55 文字分、全角文字は 1.0 文字分として視覚上の幅を計算する。"""
    return 0.55 if c.isascii() else 1.0


def _visual_len(text: str) -> float:
    return sum(_char_visual_width(c) for c in text)


def wrap_japanese_telop(text: str, max_chars: int = 13) -> str:
    """
    英単語の途中や単語の真ん中（ゴ/ミ、ソー/ル等）で不自然に改行されるのを防ぎ、
    視覚上の文字幅（全角1.0 / 半角0.55）を基準に句読点や助詞の直後で綺麗に折り返して
    ASS 改行コード (`\\N`) を挿入する。末尾に1〜3文字の孤立行（オーファン）が残らないよう均等割りを行う。
    """
    clean = text.strip()
    if _visual_len(clean) <= max_chars + 1.2:
        return clean

    lines: list[str] = []
    remaining = clean
    while _visual_len(remaining) > max_chars + 1.2:
        rem_vlen = _visual_len(remaining)
        # 残り2行で収まる長さなら、末尾が2〜3文字だけ余らないよう中央付近を目標幅にする
        if rem_vlen <= max_chars * 1.85:
            target_vlen = max(rem_vlen * 0.52, rem_vlen - max_chars)
        else:
            target_vlen = float(max_chars)

        acc = 0.0
        target_idx = len(remaining)
        for idx, ch in enumerate(remaining):
            acc += _char_visual_width(ch)
            if acc >= target_vlen:
                target_idx = max(1, idx + 1)
                break

        best_cut = -1
        search_start = max(4, target_idx - 4)
        search_end = min(len(remaining) - 3, target_idx + 3)
        # 改行後の残り文字列が 3.5 文字幅未満の孤立行にならないよう探索上限を制限
        while search_end > search_start and _visual_len(remaining[search_end:]) < 3.8:
            search_end -= 1

        # 1. 句読点・感嘆符・疑問符・閉じ括弧・空白を最優先
        for i in range(search_end, search_start - 1, -1):
            if remaining[i - 1] in "、。！？!?』】）) ":
                best_cut = i
                break

        # 2. 助詞の直後（ただし英数字の途中やカタカナ語の途中は絶対に切らない）
        if best_cut == -1:
            for i in range(search_end, search_start - 1, -1):
                prev_c = remaining[i - 1]
                next_c = remaining[i]
                if prev_c.isascii() and next_c.isascii():
                    continue
                if prev_c in "はがをにでとものてばやへ" and next_c not in "、。！？っッーなだ":
                    best_cut = i
                    break

        # 3. 英数字の途中や小書き文字・長音符の直前を避けて target_idx で切る
        if best_cut == -1:
            best_cut = min(target_idx, search_end)
            while (
                best_cut < len(remaining) - 2
                and remaining[best_cut - 1].isascii()
                and remaining[best_cut].isascii()
            ):
                best_cut += 1
            while best_cut < len(remaining) - 2 and remaining[best_cut] in "、。！？!?っッー）)】』」":
                best_cut += 1

        lines.append(remaining[:best_cut].strip())
        remaining = remaining[best_cut:].strip()

    if remaining:
        lines.append(remaining)
    return r"\N".join(lines)


def format_ass_time(seconds: float) -> str:
    """秒数を ASS 字幕フォーマット (H:MM:SS.cc) に変換する。"""
    cs = int(round((seconds % 1) * 100))
    total_sec = int(seconds)
    if cs >= 100:
        total_sec += 1
        cs -= 100
    s = total_sec % 60
    m = (total_sec // 60) % 60
    h = total_sec // 3600
    return f"{h}:{m:02d}:{s:02d}.{cs:02d}"


def format_srt_time(seconds: float) -> str:
    """秒数を SRT 字幕フォーマット (HH:MM:SS,mmm) に変換する（セルフテスト互換用）。"""
    ms = int(round((seconds % 1) * 1000))
    total_sec = int(seconds)
    s = total_sec % 60
    m = (total_sec // 60) % 60
    h = total_sec // 3600
    return f"{h:02d}:{m:02d}:{s:02d},{ms:03d}"


def ensure_default_sound_assets() -> tuple[Path, dict[str, Path]]:
    """
    `assets/se/` および `assets/bgm/` を確認し、ファイルが未配置の場合は
    標準ライブラリの波形合成で耳馴染みの良いデフォルトSE・チルBGMを自動生成する。
    ユーザーが任意の音声ファイルを置いた場合はそちらを優先使用する。
    """
    SE_DIR.mkdir(parents=True, exist_ok=True)
    BGM_DIR.mkdir(parents=True, exist_ok=True)
    sample_rate = 44100

    def _write_wav(path: Path, samples: list[float]) -> None:
        raw = bytearray()
        for s in samples:
            clamped = max(-0.98, min(0.98, s))
            raw.extend(struct.pack("<h", int(clamped * 32767)))
        with wave.open(str(path), "wb") as wf:
            wf.setnchannels(1)
            wf.setsampwidth(2)
            wf.setframerate(sample_rate)
            wf.writeframes(bytes(raw))

    # 1. 効果音ラボの定番SE（「スポッ」= hook.mp3、「パッ」= point.mp3）が未配置なら Referer 付きで自動取得を試みる
    for key, (url, referer) in SOUNDEFFECT_LAB_URLS.items():
        if not any((SE_DIR / f"{key}{ext}").exists() for ext in SE_USER_EXTS):
            target_mp3 = SE_DIR / f"{key}.mp3"
            try:
                req = urllib.request.Request(
                    url,
                    headers={"User-Agent": "Mozilla/5.0", "Referer": referer},
                )
                with urllib.request.urlopen(req, timeout=10) as resp:
                    target_mp3.write_bytes(resp.read())
                print(f"[INFO] 効果音ラボから定番SEを取得しました: {target_mp3}")
            except Exception as exc:
                print(f"[WARN] 効果音ラボからのSE取得をスキップしました ({key}): {exc}")

    # 2. オフライン時用のフォールバック波形生成 (hook.wav = スポッ風バブルポップ / point.wav = パッ風ポップ)
    hook_path = SE_DIR / "hook.wav"
    if not any((SE_DIR / f"hook{ext}").exists() for ext in SE_USER_EXTS):
        dur = 0.16
        n = int(sample_rate * dur)
        buf: list[float] = []
        phase = 0.0
        for i in range(n):
            t = i / sample_rate
            # 「スポッ」に近い急激なピッチアップ (240Hz -> 980Hz)
            freq = 240.0 + 740.0 * ((t / dur) ** 1.7)
            phase += 2 * math.pi * freq / sample_rate
            env = math.sin(math.pi * min(1.0, t / dur)) * math.exp(-t * 9.0)
            buf.append(math.sin(phase) * env * 0.85)
        _write_wav(hook_path, buf)

    point_path = SE_DIR / "point.wav"
    if not any((SE_DIR / f"point{ext}").exists() for ext in SE_USER_EXTS):
        dur = 0.11
        n = int(sample_rate * dur)
        buf = []
        phase = 0.0
        for i in range(n):
            t = i / sample_rate
            # 「パッ」に近い歯切れの良いショートポップ (520Hz -> 1040Hz)
            freq = 520.0 + 520.0 * (t / dur)
            phase += 2 * math.pi * freq / sample_rate
            env = math.exp(-t * 28.0) * min(1.0, t * 500.0)
            buf.append((math.sin(phase) + 0.3 * math.sin(phase * 2.0)) * env * 0.80)
        _write_wav(point_path, buf)

    # 3. BGM: `assets/bgm/` 内のユーザー配置ファイルを最優先（.wav 優先・更新日時が新しい順）し、無ければ Lo-Fi チルシンセループを生成
    bgm_candidates: list[Path] = []
    for ext in ("*.wav", "*.mp3", "*.m4a", "*.ogg"):
        for p in sorted(BGM_DIR.glob(ext)):
            if p.name != "default_chill_loop.wav":
                bgm_candidates.append(p)
    bgm_candidates.sort(key=lambda p: (p.suffix.lower() == ".wav", p.stat().st_mtime), reverse=True)

    if bgm_candidates:
        bgm_path = bgm_candidates[0]
        print(f"[INFO] BGMを使用します: {bgm_path}")
    else:
        bgm_path = BGM_DIR / "default_chill_loop.wav"
        # 16秒（4小節・BPM 90）のローファイ・エレクトリックピアノ風コードループ
        # Voices (200Hz〜1.5kHz) を邪魔しないウォームなローパス風倍音構成
        chords = [
            (220.00, 261.63, 329.63, 392.00),  # Am7
            (174.61, 220.00, 261.63, 349.23),  # Fmaj7
            (196.00, 246.94, 293.66, 392.00),  # G6
            (164.81, 196.00, 246.94, 329.63),  # Em7
        ]
        bar_sec = 3.2
        total_bgm_sec = bar_sec * len(chords)
        n_total = int(sample_rate * total_bgm_sec)
        bgm_buf: list[float] = []
        beat_sec = bar_sec / 4.0
        for i in range(n_total):
            t = i / sample_rate
            bar_idx = min(len(chords) - 1, int(t // bar_sec))
            bar_t = t % bar_sec
            beat_t = t % beat_sec
            chord = chords[bar_idx]

            # コードパッド（ゆっくり減衰するエレピ風）
            pad_env = math.exp(-bar_t * 0.55) * min(1.0, bar_t * 25.0)
            # ループ境界のクリック防止フェード
            if bar_t > bar_sec - 0.06:
                pad_env *= max(0.0, (bar_sec - bar_t) / 0.06)
            pad = sum(math.sin(2 * math.pi * f * t) for f in chord) * 0.16 * pad_env

            # ルートベース音（1拍目と3拍目後半）
            bass_freq = chord[0] * 0.5
            bass_env = math.exp(-beat_t * 4.5) * min(1.0, beat_t * 80.0)
            bass = math.sin(2 * math.pi * bass_freq * t) * 0.24 * bass_env

            # 軽いアルペジオパルス（8分音符）
            arp_step = int((bar_t / (beat_sec * 0.5)) % 4)
            arp_t = bar_t % (beat_sec * 0.5)
            arp_env = math.exp(-arp_t * 14.0) * min(1.0, arp_t * 150.0)
            arp = math.sin(2 * math.pi * (chord[arp_step] * 2.0) * t) * 0.07 * arp_env

            bgm_buf.append(pad + bass + arp)
        _write_wav(bgm_path, bgm_buf)

    se_defaults = {
        "hook": hook_path,
        "point": point_path,
    }
    # ユーザーが `assets/se/hook.mp3` 等を置いていればそちらを優先し、44.1kHz/モノラル/16bit WAV に正規化して使う
    se_resolved = {key: _resolve_se_file(key, default) for key, default in se_defaults.items()}
    return bgm_path, se_resolved


def _resolve_se_file(key: str, default_path: Path) -> Path:
    """
    `assets/se/<key>.<拡張子>` のユーザー配置ファイルを探し、見つかれば FFmpeg で
    44.1kHz・モノラル・16bit WAV（`assets/se/_converted/<key>.wav`）に変換して返す。
    mp3 以外の 24bit WAV 等も SE トラック合成で確実に読めるよう、常に正規化を通す。
    """
    src: Path | None = None
    for ext in SE_USER_EXTS:
        cand = SE_DIR / f"{key}{ext}"
        if cand.exists():
            src = cand
            break
    if src is None:
        src = default_path

    out = SE_DIR / "_converted" / f"{key}.wav"
    out.parent.mkdir(parents=True, exist_ok=True)
    # 変換済みファイルが元ファイルより新しければ再変換しない
    if out.exists() and out.stat().st_mtime >= src.stat().st_mtime:
        return out
    try:
        subprocess.run(
            ["ffmpeg", "-y", "-loglevel", "error", "-i", str(src),
             "-ac", "1", "-ar", "44100", "-sample_fmt", "s16", str(out)],
            check=True,
        )
        if src != default_path:
            print(f"[INFO] カスタムSEを使用します: {src}")
        return out
    except (subprocess.CalledProcessError, FileNotFoundError) as exc:
        print(f"[WARN] SE ファイルの変換に失敗したためデフォルトSEを使用します ({src}): {exc}")
        return default_path


def _read_wav_mono_float(path: Path, target_sr: int = 44100) -> list[float]:
    """WAVファイルを読み込み、target_sr のモノラル float 配列 (-1.0..1.0) に変換する。"""
    with wave.open(str(path), "rb") as wf:
        n_ch = wf.getnchannels()
        sampwidth = wf.getsampwidth()
        sr = wf.getframerate()
        n_frames = wf.getnframes()
        raw = wf.readframes(n_frames)

    if sampwidth == 2:
        fmt = f"<{n_frames * n_ch}h"
        ints = struct.unpack(fmt, raw)
        floats = [ints[i] / 32768.0 for i in range(0, len(ints), n_ch)]
    else:
        return []

    if sr != target_sr and floats:
        # 簡易線形リサンプリング
        ratio = sr / float(target_sr)
        out_len = int(len(floats) / ratio)
        resampled: list[float] = []
        for i in range(out_len):
            src_pos = i * ratio
            idx = int(src_pos)
            frac = src_pos - idx
            if idx + 1 < len(floats):
                resampled.append(floats[idx] * (1.0 - frac) + floats[idx + 1] * frac)
            else:
                resampled.append(floats[idx])
        floats = resampled

    # 素材ごとの録音レベル差（peak 0.4〜0.5等）を揃えるためピーク 0.90 に正規化
    peak = max((abs(v) for v in floats), default=0.0)
    if peak > 0.01:
        scale = 0.90 / peak
        floats = [v * scale for v in floats]
    return floats


def build_se_track_wav(
    timed_lines: list[dict[str, Any]],
    total_sec: float,
    se_paths: dict[str, Path],
    out_wav: Path,
) -> None:
    """
    動画全体の尺に合わせた効果音（SE）トラック WAV を生成する。
    - 動画の先頭 (0秒): hook（冒頭フック音「スポッ」）
    - 重要キーワード（結論・原因・最大・おすすめ・ただし等）を含む解説行の開始時: point（強調音「パッ」）
    - 掛け合いのテンポを崩さないよう、話者交代時にはSEを鳴らさない
    """
    sr = 44100
    total_samples = int(total_sec * sr) + sr
    track = [0.0] * total_samples

    se_samples = {k: _read_wav_mono_float(p, sr) for k, p in se_paths.items()}
    point_keywords = ("結論", "原因", "最大", "重要", "大事", "おすすめ", "ただし", "注意", "解決", "無難")

    for idx, item in enumerate(timed_lines):
        start_idx = max(0, int(item["start"] * sr))
        text = item.get("text", "")

        if idx == 0:
            # 冒頭フック「スポッ」は動画の先頭 (0秒) でやや控えめに鳴らす
            start_idx = 0
            chosen = se_samples.get("hook", [])
            gain = 0.48
        elif any(kw in text for kw in point_keywords) or (len(timed_lines) == 2 and idx == 1):
            chosen = se_samples.get("point", [])
            gain = 0.80
        else:
            chosen = []
            gain = 0.0

        for offset, val in enumerate(chosen):
            pos = start_idx + offset
            if pos < total_samples:
                track[pos] += val * gain

    raw = bytearray()
    for s in track[: int(total_sec * sr)]:
        clamped = max(-0.98, min(0.98, s))
        raw.extend(struct.pack("<h", int(clamped * 32767)))

    with wave.open(str(out_wav), "wb") as wf:
        wf.setnchannels(1)
        wf.setsampwidth(2)
        wf.setframerate(sr)
        wf.writeframes(bytes(raw))


def get_video_duration(video_path: Path) -> float:
    """ffprobe を使って動画の総再生秒数を取得する。取得失敗時は 0.0 を返す。"""
    if not shutil.which("ffprobe"):
        return 0.0
    try:
        res = subprocess.run(
            [
                "ffprobe",
                "-v",
                "error",
                "-show_entries",
                "format=duration",
                "-of",
                "csv=p=0",
                str(video_path),
            ],
            capture_output=True,
            text=True,
            check=True,
        )
        return float(res.stdout.strip())
    except Exception:
        return 0.0


def _find_voicevox_engine_exe() -> Path | None:
    """Windows 環境でインストール済みの VOICEVOX Engine (`run.exe`) を自動検索する。"""
    candidates: list[Path] = []
    local_app = os.environ.get("LOCALAPPDATA", "")
    if local_app:
        candidates.append(Path(local_app) / "Programs" / "VOICEVOX" / "vv-engine" / "run.exe")
        candidates.append(Path(local_app) / "Programs" / "VOICEVOX" / "run.exe")
    candidates.append(Path(r"C:\Program Files\VOICEVOX\vv-engine\run.exe"))
    for c in candidates:
        if c.exists():
            return c
    return None


def check_prerequisites(base_url: str = VOICEVOX_URL) -> bool:
    """FFmpeg と VOICEVOX Engine の起動状態を事前チェックし、未起動なら自動起動を試みる。"""
    if not shutil.which("ffmpeg"):
        print(
            "[ERROR] ffmpeg が見つかりません。コマンドプロンプトで `winget install Gyan.FFmpeg` 等を実行し、PATH を通してください。",
            file=sys.stderr,
        )
        return False

    try:
        with urllib.request.urlopen(f"{base_url}/version", timeout=3) as resp:
            version = resp.read().decode("utf-8").strip().strip('"')
            print(f"[INFO] VOICEVOX Engine 接続OK (version: {version})")
            return True
    except Exception:
        pass

    # 未起動の場合はインストール済みの VOICEVOX Engine を自動でバックグラウンド起動する
    engine_exe = _find_voicevox_engine_exe()
    if engine_exe:
        print(f"[INFO] VOICEVOX Engine を自動起動しています: {engine_exe}")
        subprocess.Popen(
            [str(engine_exe)],
            cwd=str(engine_exe.parent),
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        for _ in range(30):
            time.sleep(1.0)
            try:
                with urllib.request.urlopen(f"{base_url}/version", timeout=2) as resp:
                    version = resp.read().decode("utf-8").strip().strip('"')
                    print(f"[INFO] VOICEVOX Engine 自動起動＆接続OK (version: {version})")
                    return True
            except Exception:
                continue

    print(
        f"[ERROR] VOICEVOX Engine ({base_url}) に接続できません。\n"
        "        VOICEVOX アプリを起動した状態で再度 `python make_short.py` を実行してください。",
        file=sys.stderr,
    )
    return False


def synthesize_voicevox(text: str, speaker_id: int, out_wav: Path, base_url: str = VOICEVOX_URL) -> float:
    """VOICEVOX Engine API を叩いてWAV音声を生成し、秒数を返す。"""
    reading_text = to_voicevox_reading(text)
    q_url = f"{base_url}/audio_query?text={urllib.parse.quote(reading_text)}&speaker={speaker_id}"
    req_q = urllib.request.Request(q_url, method="POST")
    with urllib.request.urlopen(req_q, timeout=15) as resp:
        query_json = json.loads(resp.read().decode("utf-8"))

    # ショート動画向けに読み上げ速度をテンポアップ (1.20倍) し、文末の間 (0.10秒) でサクサク進める
    query_json["speedScale"] = VOICE_SPEED_SCALE
    query_json["postPhonemeLength"] = VOICE_POST_PHONEME_LENGTH

    s_url = f"{base_url}/synthesis?speaker={speaker_id}"
    req_s = urllib.request.Request(
        s_url,
        data=json.dumps(query_json).encode("utf-8"),
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    with urllib.request.urlopen(req_s, timeout=30) as resp:
        wav_bytes = resp.read()

    out_wav.write_bytes(wav_bytes)
    with wave.open(str(out_wav), "rb") as wf:
        return wf.getnframes() / float(wf.getframerate())


def _ass_rounded_rect_path(width: int, height: int, radius: int = 24) -> str:
    """ASS ベクター描画 (`\\p1`) 用の角丸矩形パス文字列を返す。"""
    w = width
    h = height
    r = min(radius, w // 2, h // 2)
    return (
        f"m {r} 0 "
        f"l {w - r} 0 "
        f"b {w} 0 {w} 0 {w} {r} "
        f"l {w} {h - r} "
        f"b {w} {h} {w} {h} {w - r} {h} "
        f"l {r} {h} "
        f"b 0 {h} 0 {h} 0 {h - r} "
        f"l 0 {r} "
        f"b 0 0 0 0 {r} 0"
    )


def assign_device_overlays(article: dict[str, Any], timed_lines: list[dict[str, Any]]) -> None:
    """
    記事内の登場デバイス (`article['devices']`) を各セリフ行に紐付ける。
    - セリフ内にデバイス名（または主要トークン）が含まれていればその行に優先割り当て
    - まだ表示されていない注目デバイスがあれば中盤〜後半の解説行に割り当てて画面上部サブ枠でポップアップ紹介する
    """
    devices = article.get("devices") or []
    if not devices or not timed_lines:
        return

    sentiment_label = {
        "positive": "【高評価】",
        "neutral": "【賛否両論】",
        "negative": "【要注意】",
    }
    category_icon = {
        "mouse": "◆",
        "mousepad": "■",
        "skates": "▲",
    }

    formatted_devices: list[dict[str, Any]] = []
    for d in devices:
        name = (d.get("name") or "").strip()
        if not name:
            continue
        cat = d.get("category", "mouse")
        sent = d.get("sentiment", "neutral")
        icon = category_icon.get(cat, "◆")
        s_tag = sentiment_label.get(sent, "【注目】")
        # 長すぎるデバイス名は枠内に綺麗に収まるよう調整
        short_name = re.sub(r"\s*ガラスマウスパッド$", "", name)
        tokens = [
            tok for tok in re.split(r"[\s\-/]+", short_name)
            if len(tok) >= 2 and tok.lower() not in ("pro", "gaming", "gears", "edition", "mouse", "soft")
        ]
        formatted_devices.append({
            "display": f"{icon} 登場デバイス：{short_name} {s_tag}",
            "tokens": tokens,
            "sentiment": sent,
        })

    if not formatted_devices:
        return

    used_indices: set[int] = set()
    # 1. セリフ本文にトークンが含まれる行へ優先マッチ
    for line in timed_lines:
        text_lower = line["text"].lower()
        for d_idx, dev in enumerate(formatted_devices):
            if any(tok.lower() in text_lower for tok in dev["tokens"]):
                line["matched_device"] = dev["display"]
                used_indices.add(d_idx)
                break

    # 2. セリフ内で直接名前が出なかった上位デバイスも、2行目以降の空き行で順番にポップアップ表示
    unused_devs = [d for i, d in enumerate(formatted_devices) if i not in used_indices]
    dev_cursor = 0
    for line_idx, line in enumerate(timed_lines):
        if line_idx == 0 or line_idx == len(timed_lines) - 1:
            continue
        if not line.get("matched_device") and dev_cursor < len(unused_devs):
            line["matched_device"] = unused_devs[dev_cursor]["display"]
            dev_cursor += 1


def build_ass_subtitles(article: dict[str, Any], timed_lines: list[dict[str, Any]], total_sec: float) -> str:
    """
    1080x1920 縦型ショート動画用の ASS 字幕を生成する。
    - 画面中央（クロスヘア＆ターゲット y=520..1280）を一切隠さない上下分離レイアウト
    - 上部 (y=75..345):
      - `【海外r/...】` の括弧見出しを廃止し、記事タイトルを省略せず全文そのまま大文字＋半透明の角丸黒座布団で常時表示
      - そのすぐ下 (y=365..445) に、登場デバイス＆評価バッジをポップアップ表示
    - 下部 (y=1340..1680):
      - `▼ ずんだもん｜...` の小見出しを廃止し、セリフ本文のフォントサイズを最大化 (68pt)
      - 話者別カラー（ずんだもん＝グリーン枠、春日部つむぎ＝アンバー枠）の角丸黒座布団を敷いて視認性を最大化
    """
    header = """[Script Info]
ScriptType: v4.00+
PlayResX: 1080
PlayResY: 1920
WrapStyle: 2
ScaledBorderAndShadow: yes

[V4+ Styles]
Format: Name, Fontname, Fontsize, PrimaryColour, SecondaryColour, OutlineColour, BackColour, Bold, Italic, Underline, StrikeOut, ScaleX, ScaleY, Spacing, Angle, BorderStyle, Outline, Shadow, Alignment, MarginL, MarginR, MarginV, Encoding
Style: BoxShape,Yu Gothic UI,20,&H3014100C,&H000000FF,&H2070FF66,&H00000000,0,0,0,0,100,100,0,0,1,3,0,7,0,0,0,1
Style: TopTitle,Yu Gothic UI,58,&H00FFFFFF,&H000000FF,&H00140E08,&H80000000,-1,0,0,0,100,100,1,0,1,7,3,5,40,40,0,1
Style: DevicePill,Yu Gothic UI,40,&H0088F8FF,&H000000FF,&H00181008,&H80000000,-1,0,0,0,100,100,1,0,1,5,2,5,40,40,0,1
Style: ZundaMain,Yu Gothic UI,68,&H00FFFFFF,&H000000FF,&H00164A0E,&H80000000,-1,0,0,0,100,100,1,0,1,9,3,5,40,40,0,1
Style: TsumugiMain,Yu Gothic UI,68,&H00FFFFFF,&H000000FF,&H00083268,&H80000000,-1,0,0,0,100,100,1,0,1,9,3,5,40,40,0,1

[Events]
Format: Layer, Start, End, Style, Name, MarginL, MarginR, MarginV, Effect, Text
"""
    end_all = format_ass_time(total_sec)
    raw_title = (article.get("title_ja") or "").strip()
    # タイトルは省略せず全文を自然な位置で折り返す（1行あたり約15.5文字幅）
    wrapped_title = wrap_japanese_telop(raw_title, max_chars=15)
    title_lines = wrapped_title.split(r"\N")
    n_title_lines = len(title_lines)

    # 上部タイトル座布団のサイズ・位置計算
    title_box_w = 1000
    title_box_h = n_title_lines * 74 + 46
    title_box_x = (1080 - title_box_w) // 2
    title_box_y = 80
    title_center_y = title_box_y + title_box_h // 2
    title_rect = _ass_rounded_rect_path(title_box_w, title_box_h, radius=26)

    events: list[str] = [
        # Layer 0: 上部タイトルの角丸ダーク座布団（エメラルドグリーンの細枠つき）
        (
            f"Dialogue: 0,0:00:00.00,{end_all},BoxShape,,0,0,0,,"
            f"{{\\an7\\pos({title_box_x},{title_box_y})\\p1\\1c&H14100C&\\1a&H28&\\3c&H78FF68&\\3a&H30&\\bord3}}{title_rect}{{\\p0}}"
        ),
        # Layer 1: 上部タイトル全文（省略なし）
        f"Dialogue: 1,0:00:00.00,{end_all},TopTitle,,0,0,0,,{{\\an5\\pos(540,{title_center_y})}}{wrapped_title}",
    ]

    # デバイスバッジの表示Y座標（タイトル座布団のすぐ下、中央のクロスヘアには一切被らない）
    dev_box_w = 960
    dev_box_h = 70
    dev_box_x = (1080 - dev_box_w) // 2
    dev_box_y = title_box_y + title_box_h + 18
    dev_center_y = dev_box_y + dev_box_h // 2
    dev_rect = _ass_rounded_rect_path(dev_box_w, dev_box_h, radius=35)

    for item in timed_lines:
        st = format_ass_time(item["start"])
        et = format_ass_time(item["end"])
        is_zunda = item["speaker"] == "zundamon"
        main_style = "ZundaMain" if is_zunda else "TsumugiMain"

        # メインセリフの折り返し（フォントサイズ68ptに合わせて1行あたり全角13文字幅）
        wrapped_spoken = wrap_japanese_telop(item["text"], max_chars=13)
        spoken_lines = wrapped_spoken.split(r"\N")
        n_spoken_lines = len(spoken_lines)

        # 下部セリフ座布団のサイズ・位置計算（中心Y=1500付近に配置）
        sub_box_w = 1000
        sub_box_h = n_spoken_lines * 86 + 54
        sub_box_x = (1080 - sub_box_w) // 2
        sub_center_y = 1500
        sub_box_y = sub_center_y - sub_box_h // 2
        sub_rect = _ass_rounded_rect_path(sub_box_w, sub_box_h, radius=28)

        # 話者ごとの座布団枠線カラー（ずんだもん＝グリーン、春日部つむぎ＝アンバーゴールド）
        border_col = "&H68F058&" if is_zunda else "&H40B0FF&"

        events.append(
            f"Dialogue: 0,{st},{et},BoxShape,,0,0,0,,"
            f"{{\\an7\\pos({sub_box_x},{sub_box_y})\\p1\\1c&H120E0B&\\1a&H26&\\3c{border_col}\\3a&H20&\\bord4}}{sub_rect}{{\\p0}}"
        )
        events.append(
            f"Dialogue: 1,{st},{et},{main_style},,0,0,0,,"
            f"{{\\an5\\pos(540,{sub_center_y})}}{wrapped_spoken}"
        )

        # 登場デバイスバッジがある行は上部サブ枠にポップアップ表示
        dev_text = item.get("matched_device")
        if dev_text:
            events.append(
                f"Dialogue: 0,{st},{et},BoxShape,,0,0,0,,"
                f"{{\\fad(150,150)\\an7\\pos({dev_box_x},{dev_box_y})\\p1\\1c&H1C140E&\\1a&H24&\\3c&H78E8FF&\\3a&H28&\\bord3}}{dev_rect}{{\\p0}}"
            )
            events.append(
                f"Dialogue: 1,{st},{et},DevicePill,,0,0,0,,"
                f"{{\\fad(150,150)\\an5\\pos(540,{dev_center_y})}}{dev_text}"
            )

    return header + "\n".join(events) + "\n"


def build_short_for_article(
    article: dict[str, Any],
    bg_video: Path | None,
    bgm_path: Path,
    se_paths: dict[str, Path],
    out_mp4: Path,
) -> None:
    """1記事分のショート動画 (1080x1920 MP4) を合成する。"""
    script = article.get("short_script") or []
    if not script:
        print(f"[WARN] 記事 {article.get('id')} に short_script がないためスキップします。")
        return

    out_mp4_abs = out_mp4.resolve()
    out_mp4_abs.parent.mkdir(parents=True, exist_ok=True)
    bg_video_abs = bg_video.resolve() if bg_video else None
    bgm_abs = bgm_path.resolve()

    with tempfile.TemporaryDirectory() as tmp:
        tmp_dir = Path(tmp)
        concat_list_path = tmp_dir / "wavs.txt"
        ass_path = tmp_dir / "captions.ass"
        se_track_path = tmp_dir / "se_track.wav"

        # 冒頭「スポッ」のアタックがクリアに聞こえるよう、声の開始を HOOK_LEAD_SEC (0.18秒) 遅らせる
        hook_lead = HOOK_LEAD_SEC
        current_time = hook_lead
        timed_lines: list[dict[str, Any]] = []
        concat_lines: list[str] = []

        for idx, line in enumerate(script, start=1):
            raw_speaker = line.get("speaker", "zundamon")
            speaker_key = "zundamon" if raw_speaker == "zundamon" else "tsumugi"
            speaker_id = SPEAKER_MAP.get(speaker_key, 8)
            spoken_text = line["text"]
            if speaker_key == "tsumugi":
                spoken_text = normalize_tsumugi_tone(spoken_text)

            wav_name = f"line_{idx:03d}.wav"
            wav_path = tmp_dir / wav_name
            print(f"  -> 音声合成中 ({idx}/{len(script)}) [{speaker_key}]: {spoken_text}")
            duration = synthesize_voicevox(spoken_text, speaker_id, wav_path)

            timed_lines.append({
                "speaker": speaker_key,
                "text": spoken_text,
                "caption": line.get("caption") or "",
                "start": 0.0 if idx == 1 else current_time,
                "end": current_time + duration,
            })
            concat_lines.append(f"file '{wav_name}'")
            current_time += duration

        # 末尾の無音余白を最小限（0.15秒）に引き締めて平均視聴維持率を高める
        total_sec = current_time + 0.15
        # 登場デバイスポップアップの紐付けと SE トラックの生成
        assign_device_overlays(article, timed_lines)
        build_se_track_wav(timed_lines, total_sec, se_paths, se_track_path)

        ass_content = build_ass_subtitles(article, timed_lines, total_sec)
        ass_path.write_text(ass_content, encoding="utf-8-sig")
        concat_list_path.write_text("\n".join(concat_lines), encoding="utf-8")

        subprocess.run(
            ["ffmpeg", "-y", "-loglevel", "error", "-f", "concat", "-safe", "0", "-i", "wavs.txt", "-c", "copy", "merged.wav"],
            cwd=str(tmp_dir),
            check=True,
        )

        # Windows のドライブレター (C:) によるフィルタのパス解析不具合を防ぐため、cwd=tmp_dir で相対パスを渡す
        total_duration = f"{total_sec:.2f}"
        fade_start = f"{max(0.0, total_sec - 0.8):.2f}"
        # 背景動画の元音声は使わず、VOICEVOX音声(1:a) + SEトラック(2:a) + BGM(3:a) の3系統をクリアにミックス
        lead_ms = int(round(hook_lead * 1000))
        delay_filter = f",adelay={lead_ms}:all=1" if lead_ms > 0 else ""
        audio_filter = (
            f"[1:a]aresample=44100{delay_filter},volume={VOICE_VOLUME}[voice];"
            f"[2:a]aresample=44100,volume={SE_VOLUME}[se];"
            f"[3:a]aresample=44100,volume={BGM_VOLUME},afade=t=out:st={fade_start}:d=0.8[bgm];"
            f"[voice][se][bgm]amix=inputs=3:duration=longest:dropout_transition=0,volume=2.8,alimiter=limit=0.95[aout]"
        )

        if bg_video_abs:
            bg_dur = get_video_duration(bg_video_abs)
            # 背景動画の開始位置をランダムに決定（動画末尾で切れないよう余白を確保）
            if bg_dur > total_sec + 2.0:
                max_seek = max(0.0, bg_dur - total_sec - 1.0)
                start_offset = random.uniform(0.0, max_seek)
            elif bg_dur > 5.0:
                start_offset = random.uniform(0.0, bg_dur - 3.0)
            else:
                start_offset = 0.0

            if start_offset > 0.0:
                print(f"  -> 背景動画の開始位置: {start_offset:.1f}秒 (総尺: {bg_dur:.1f}秒)")

            vf = (
                "scale=1080:1920:force_original_aspect_ratio=increase,"
                "crop=1080:1920,"
                "eq=brightness=-0.06:contrast=1.04,"
                "subtitles=captions.ass"
            )
            filter_complex = f"[0:v]{vf}[vout];{audio_filter}"
            cmd = [
                "ffmpeg",
                "-y",
                "-loglevel",
                "error",
                "-ss",
                f"{start_offset:.2f}",
                "-stream_loop",
                "-1",
                "-i",
                str(bg_video_abs),
                "-i",
                "merged.wav",
                "-i",
                "se_track.wav",
                "-stream_loop",
                "-1",
                "-i",
                str(bgm_abs),
                "-t",
                total_duration,
                "-filter_complex",
                filter_complex,
                "-map",
                "[vout]",
                "-map",
                "[aout]",
                "-c:v",
                "libx264",
                "-preset",
                "fast",
                "-crf",
                "21",
                "-c:a",
                "aac",
                "-b:a",
                "192k",
                "-shortest",
                str(out_mp4_abs),
            ]
        else:
            filter_complex = f"[0:v]subtitles=captions.ass[vout];{audio_filter}"
            cmd = [
                "ffmpeg",
                "-y",
                "-loglevel",
                "error",
                "-f",
                "lavfi",
                "-i",
                f"color=c=0x0b0f17:s=1080x1920:r=30:d={total_duration}",
                "-i",
                "merged.wav",
                "-i",
                "se_track.wav",
                "-stream_loop",
                "-1",
                "-i",
                str(bgm_abs),
                "-t",
                total_duration,
                "-filter_complex",
                filter_complex,
                "-map",
                "[vout]",
                "-map",
                "[aout]",
                "-c:v",
                "libx264",
                "-preset",
                "fast",
                "-crf",
                "21",
                "-c:a",
                "aac",
                "-b:a",
                "192k",
                "-shortest",
                str(out_mp4_abs),
            ]

        print("  -> FFmpeg で動画・角丸座布団テロップ・音声・BGM・SEを合成中...")
        subprocess.run(cmd, cwd=str(tmp_dir), check=True)
        print(f"[OK] ショート動画を出力しました: {out_mp4}")


# ============================================================================
# 6. 環境変数・生成履歴管理（MP4削除後の再生成防止）＆ YouTube Data API v3 自動投稿
# ============================================================================


def load_dotenv(env_path: Path = ENV_FILE) -> None:
    """外部ライブラリ不要でプロジェクト直下の `.env` ファイルを読み込み環境変数に反映する。"""
    if not env_path.exists():
        return
    for raw_line in env_path.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, _, val = line.partition("=")
        key = key.strip()
        val = val.strip().strip("'").strip('"')
        if key and key not in os.environ:
            os.environ[key] = val


def save_env_var(key: str, value: str, env_path: Path = ENV_FILE) -> None:
    """`.env` ファイル内の指定キーを更新（存在しなければ末尾に追記）し、`os.environ` にも反映する。"""
    os.environ[key] = value
    lines: list[str] = []
    if env_path.exists():
        lines = env_path.read_text(encoding="utf-8").splitlines()

    updated = False
    new_lines: list[str] = []
    for line in lines:
        stripped = line.strip()
        if stripped and not stripped.startswith("#") and "=" in stripped:
            k, _, _ = stripped.partition("=")
            if k.strip() == key:
                new_lines.append(f"{key}={value}")
                updated = True
                continue
        new_lines.append(line)

    if not updated:
        if new_lines and new_lines[-1].strip() != "":
            new_lines.append("")
        new_lines.append(f"{key}={value}")

    env_path.write_text("\n".join(new_lines) + "\n", encoding="utf-8")


def load_shorts_history(history_path: Path = SHORTS_HISTORY_FILE) -> dict[str, dict[str, Any]]:
    """
    ショート動画の生成・YouTubeアップロード履歴を読み込む。
    HDD容量節約のために `dist/shorts/*.mp4` を削除した後でも再生成されないよう永続管理する。
    """
    if not history_path.exists():
        return {}
    try:
        data = json.loads(history_path.read_text(encoding="utf-8"))
        if isinstance(data, dict):
            return data
    except Exception:
        pass
    return {}


def save_shorts_history(history: dict[str, dict[str, Any]], history_path: Path = SHORTS_HISTORY_FILE) -> None:
    """ショート動画の生成・アップロード履歴を JSON ファイルに保存する。"""
    history_path.parent.mkdir(parents=True, exist_ok=True)
    history_path.write_text(
        json.dumps(history, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )


def save_articles_json(articles: list[dict[str, Any]], articles_path: Path = ARTICLES_FILE) -> None:
    """`data/articles.json` を整形して上書き保存する。"""
    articles_path.parent.mkdir(parents=True, exist_ok=True)
    articles_path.write_text(
        json.dumps(articles, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )


def sync_state_between_articles_and_history(
    articles: list[dict[str, Any]],
    history: dict[str, dict[str, Any]],
    shorts_dir: Path = SHORTS_OUT_DIR,
) -> bool:
    """
    `data/articles.json`・`data/shorts_history.json`・既存の `dist/shorts/*.mp4` の間で
    生成済みフラグ (`short_generated`) と YouTube 投稿情報 (`youtube_video_id` 等) を双方向同期する。
    変更があった場合は True を返す。
    """
    changed = False
    for art in articles:
        aid = str(art.get("id") or "").strip()
        if not aid:
            continue
        h = history.get(aid, {})
        mp4_exists = (shorts_dir / f"{aid}.mp4").exists()

        is_gen = bool(
            art.get("short_generated")
            or h.get("short_generated")
            or art.get("youtube_video_id")
            or h.get("youtube_video_id")
            or mp4_exists
        )
        yt_id = str(art.get("youtube_video_id") or h.get("youtube_video_id") or "").strip()
        yt_url = str(art.get("youtube_url") or h.get("youtube_url") or "").strip()
        if yt_id and not yt_url:
            yt_url = f"https://youtube.com/shorts/{yt_id}"
        yt_at = str(art.get("youtube_uploaded_at") or h.get("youtube_uploaded_at") or "").strip()
        yt_pub_at = str(art.get("youtube_publish_at") or h.get("youtube_publish_at") or "").strip()
        gen_at = str(
            art.get("short_generated_at")
            or h.get("short_generated_at")
            or (dt.datetime.now(dt.timezone.utc).isoformat() if is_gen else "")
        ).strip()

        if is_gen and not art.get("short_generated"):
            art["short_generated"] = True
            changed = True
        if gen_at and art.get("short_generated_at") != gen_at:
            art["short_generated_at"] = gen_at
            changed = True
        if yt_id and art.get("youtube_video_id") != yt_id:
            art["youtube_video_id"] = yt_id
            art["youtube_url"] = yt_url
            if yt_at:
                art["youtube_uploaded_at"] = yt_at
            changed = True
        if yt_pub_at and art.get("youtube_publish_at") != yt_pub_at:
            art["youtube_publish_at"] = yt_pub_at
            changed = True

        if is_gen or yt_id:
            new_h = {
                "id": aid,
                "title_ja": str(art.get("title_ja") or h.get("title_ja") or ""),
                "short_generated": is_gen,
                "short_generated_at": gen_at,
                "youtube_video_id": yt_id,
                "youtube_url": yt_url,
                "youtube_uploaded_at": yt_at,
                "youtube_publish_at": yt_pub_at,
            }
            if history.get(aid) != new_h:
                history[aid] = new_h
                changed = True

    return changed


def _detect_client_secret_json() -> tuple[str, str, str] | None:
    """
    プロジェクト直下に Google Cloud Console からダウンロードした `client_secret*.json` があれば
    更新日時が新しい順（かつ `installed`＝デスクトップアプリ優先）で
    `(client_id, client_secret, client_type)` を自動抽出する。
    """
    candidates = sorted(
        Path(".").glob("client_secret*.json"),
        key=lambda p: p.stat().st_mtime,
        reverse=True,
    )
    # まず installed (デスクトップアプリ) を優先探索し、無ければ web を探索
    for preferred_type in ("installed", "web"):
        for p in candidates:
            try:
                data = json.loads(p.read_text(encoding="utf-8"))
                if preferred_type in data and isinstance(data[preferred_type], dict):
                    block = data[preferred_type]
                    cid = str(block.get("client_id") or "").strip()
                    csec = str(block.get("client_secret") or "").strip()
                    if cid and csec:
                        return cid, csec, preferred_type
            except Exception:
                continue
    return None


def get_youtube_client_credentials() -> tuple[str, str] | None:
    """`client_secret*.json` または `.env` から YouTube OAuth クライアントID・シークレットを取得する。"""
    detected = _detect_client_secret_json()
    if detected:
        cid, csec, ctype = detected
        old_cid = (os.environ.get("YOUTUBE_CLIENT_ID") or "").strip()
        if cid != old_cid:
            save_env_var("YOUTUBE_CLIENT_ID", cid)
            save_env_var("YOUTUBE_CLIENT_SECRET", csec)
            print(f"[INFO] `client_secret*.json` ({ctype}) から YouTube OAuth クライアント情報を読み込み `.env` を更新しました。")
        if ctype == "web" and not (os.environ.get("YOUTUBE_REFRESH_TOKEN") or "").strip():
            print(
                "[NOTE] 現在のOAuthクライアントは『ウェブ アプリケーション』として作成されています。\n"
                "       もし `Error 400: redirect_uri_mismatch` が出る場合は、Google Cloud Console の\n"
                "       「承認済みのリダイレクト URI」に `http://127.0.0.1:8765/` を追加して保存してください。"
            )
        return cid, csec

    cid = (os.environ.get("YOUTUBE_CLIENT_ID") or "").strip()
    csec = (os.environ.get("YOUTUBE_CLIENT_SECRET") or "").strip()
    if cid and csec:
        return cid, csec
    return None


def run_youtube_oauth_flow(client_id: str, client_secret: str) -> str:
    """
    ローカルHTTPサーバを一時起動し、ブラウザで Google OAuth 2.0 同意画面を開いて
    リフレッシュトークンを取得・`.env` に保存する。
    """
    port = 8765
    redirect_uri = f"http://127.0.0.1:{port}/"
    auth_code_holder: dict[str, str] = {}

    class _OAuthCallbackHandler(http.server.BaseHTTPRequestHandler):
        def do_GET(self) -> None:
            parsed = urllib.parse.urlparse(self.path)
            qs = urllib.parse.parse_qs(parsed.query)
            if "code" in qs:
                auth_code_holder["code"] = qs["code"][0]
                body = (
                    "<html><head><meta charset='utf-8'><title>認証完了</title></head>"
                    "<body style='font-family:sans-serif;padding:40px;text-align:center;'>"
                    "<h2>YouTube 自動アップロードの認証が完了しました！</h2>"
                    "<p>このブラウザタブを閉じて、ターミナルに戻ってください。</p>"
                    "</body></html>"
                )
                self.send_response(200)
            else:
                err = qs.get("error", ["unknown_error"])[0]
                auth_code_holder["error"] = err
                body = f"<html><head><meta charset='utf-8'></head><body><h2>認証エラー: {err}</h2></body></html>"
                self.send_response(400)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.end_headers()
            self.wfile.write(body.encode("utf-8"))

        def log_message(self, format: str, *args: Any) -> None:
            return

    auth_params = {
        "client_id": client_id,
        "redirect_uri": redirect_uri,
        "response_type": "code",
        "scope": YOUTUBE_OAUTH_SCOPE,
        "access_type": "offline",
        "prompt": "consent",
    }
    auth_url = f"https://accounts.google.com/o/oauth2/v2/auth?{urllib.parse.urlencode(auth_params)}"

    print("\n" + "=" * 72)
    print("【YouTube 初回OAuth認証】ブラウザでGoogleアカウント認証画面を開きます...")
    print("自動で開かない場合は、以下のURLをブラウザに貼り付けて開いてください：")
    print(auth_url)
    print("=" * 72 + "\n")

    server = http.server.HTTPServer(("127.0.0.1", port), _OAuthCallbackHandler)
    server.timeout = 180
    webbrowser.open(auth_url)

    while "code" not in auth_code_holder and "error" not in auth_code_holder:
        server.handle_request()
    server.server_close()

    if "error" in auth_code_holder:
        raise RuntimeError(f"Google OAuth 認証がキャンセルまたは失敗しました: {auth_code_holder['error']}")
    code = auth_code_holder.get("code", "")
    if not code:
        raise RuntimeError("Google OAuth 認証コードを取得できませんでした。")

    token_data = urllib.parse.urlencode({
        "code": code,
        "client_id": client_id,
        "client_secret": client_secret,
        "redirect_uri": redirect_uri,
        "grant_type": "authorization_code",
    }).encode("utf-8")

    req = urllib.request.Request(
        "https://oauth2.googleapis.com/token",
        data=token_data,
        headers={"Content-Type": "application/x-www-form-urlencoded"},
        method="POST",
    )
    with urllib.request.urlopen(req, timeout=20) as resp:
        token_json = json.loads(resp.read().decode("utf-8"))

    refresh_token = str(token_json.get("refresh_token") or "").strip()
    if not refresh_token:
        raise RuntimeError("refresh_token が返却されませんでした。Googleアカウントの権限設定を確認してください。")

    save_env_var("YOUTUBE_REFRESH_TOKEN", refresh_token)
    print("[OK] YouTube OAuth 認証が完了し、`.env` に YOUTUBE_REFRESH_TOKEN を保存しました！")
    return refresh_token


def get_youtube_access_token() -> str | None:
    """
    `.env` の認証情報から YouTube Data API v3 用のアクセストークンを取得する。
    `YOUTUBE_CLIENT_ID` と `YOUTUBE_CLIENT_SECRET` が設定済みで `YOUTUBE_REFRESH_TOKEN` が未取得なら
    自動的に初回ブラウザ認証フローを起動する。
    """
    creds = get_youtube_client_credentials()
    if not creds:
        return None
    client_id, client_secret = creds
    refresh_token = (os.environ.get("YOUTUBE_REFRESH_TOKEN") or "").strip()
    if not refresh_token:
        refresh_token = run_youtube_oauth_flow(client_id, client_secret)

    token_data = urllib.parse.urlencode({
        "client_id": client_id,
        "client_secret": client_secret,
        "refresh_token": refresh_token,
        "grant_type": "refresh_token",
    }).encode("utf-8")

    req = urllib.request.Request(
        "https://oauth2.googleapis.com/token",
        data=token_data,
        headers={"Content-Type": "application/x-www-form-urlencoded"},
        method="POST",
    )
    with urllib.request.urlopen(req, timeout=20) as resp:
        token_json = json.loads(resp.read().decode("utf-8"))
    access_token = str(token_json.get("access_token") or "").strip()
    if not access_token:
        raise RuntimeError("YouTube アクセストークンの更新に失敗しました。")
    return access_token


def build_youtube_metadata(article: dict[str, Any]) -> tuple[str, str, list[str]]:
    """
    記事データから YouTube Shorts 用の (タイトル, 概要欄テキスト, タグ配列) を生成する。
    - タイトルは 100 文字制限内に収め、末尾に `#Shorts` を付与
    - 概要欄には要約・記事リンク・登場デバイス・VOICEVOXクレジット表記を記載
    """
    raw_title = (article.get("title_ja") or "").strip()
    if not raw_title or raw_title == "title_ja":
        raw_title = (article.get("title_en") or "海外エイム＆マウス議論まとめ").strip()
    # YouTubeタイトルで利用不可の山括弧 < > を置換
    clean_title = raw_title.replace("<", "＜").replace(">", "＞")
    suffix = " #Shorts"
    if "#shorts" in clean_title.lower():
        title = clean_title[:100]
    else:
        max_base = 100 - len(suffix)
        if len(clean_title) > max_base:
            clean_title = clean_title[: max_base - 1] + "…"
        title = clean_title + suffix

    hook = (article.get("hook_ja") or "").strip()
    points = article.get("consensus_points") or []
    article_url = (article.get("article_url") or "https://aimswamp.github.io/aimlog/").strip()
    subreddit = (article.get("subreddit") or "FPSAimTrainer").strip()

    desc_lines: list[str] = [
        "▼ スレッド全訳・登場デバイスの詳細（Amazon/楽天）はこちら",
        "📱 スマホの方：チャンネルアイコンをタップ ➔ プロフィールのリンク『エイム沼の海外ログ』から1タップで開けます！",
        f"💻 PC・ブラウザの方：{article_url} （または『エイム沼の海外ログ』で検索）",
        "",
    ]
    if hook:
        desc_lines.append(hook)
        desc_lines.append("")
    if points:
        desc_lines.append("【スレッドの要点】")
        for pt in points[:3]:
            desc_lines.append(f"・{pt}")
        desc_lines.append("")

    devices = article.get("devices") or []
    dev_names = [str(d.get("name") or "").strip() for d in devices if d.get("name")]
    if dev_names:
        desc_lines.append(f"【登場デバイス】{', '.join(dev_names[:6])}")
        desc_lines.append("")

    desc_lines.extend([
        f"出典: Reddit r/{subreddit}",
        "音声: VOICEVOX:ずんだもん / VOICEVOX:春日部つむぎ",
        "",
        "#Shorts #FPS #エイム #ゲーミングマウス #マウスパッド #KovaaKs #Aimlabs #VALORANT #ApexLegends #ずんだもん",
    ])
    description = "\n".join(desc_lines).replace("<", "＜").replace(">", "＞")[:4900]

    tags = [
        "Shorts",
        "FPS",
        "エイム",
        "エイム練習",
        "ゲーミングマウス",
        "マウスパッド",
        "KovaaKs",
        "Aimlabs",
        "VALORANT",
        "ApexLegends",
        "ずんだもん",
        "春日部つむぎ",
        subreddit,
    ]
    for dn in dev_names[:4]:
        clean_dn = dn.replace("<", "").replace(">", "")
        if len(clean_dn) <= 30 and clean_dn not in tags:
            tags.append(clean_dn)

    return title, description, tags


def _parse_iso_datetime(val: str) -> dt.datetime | None:
    """ISO 8601 文字列を UTC aware な datetime に変換する。"""
    s = (val or "").strip()
    if not s:
        return None
    try:
        if s.endswith("Z"):
            s = s[:-1] + "+00:00"
        d = dt.datetime.fromisoformat(s)
        if d.tzinfo is None:
            d = d.replace(tzinfo=dt.timezone.utc)
        return d.astimezone(dt.timezone.utc)
    except Exception:
        return None


def _next_golden_slot_jst(after_jst: dt.datetime) -> dt.datetime:
    """`after_jst` より後にある直近のゴールデンタイム枠（JST: 07:30, 12:15, 18:00, 21:00）を返す。"""
    jst_tz = dt.timezone(dt.timedelta(hours=9))
    base_date = after_jst.date()
    for day_offset in range(0, 8):
        cur_date = base_date + dt.timedelta(days=day_offset)
        for hour, minute in YOUTUBE_SCHEDULE_SLOTS_JST:
            cand = dt.datetime(cur_date.year, cur_date.month, cur_date.day, hour, minute, 0, tzinfo=jst_tz)
            if cand > after_jst:
                return cand
    return after_jst + dt.timedelta(hours=6)


def plan_youtube_publish_schedule(
    count: int,
    history: dict[str, dict[str, Any]],
    immediate_all: bool = False,
    now_utc: dt.datetime | None = None,
) -> list[str | None]:
    """
    ショートフィードの連投ロック（1〜2回再生止まり）を防ぐため、アップロードする `count` 本の公開スケジュールを計算する。
    - 戻り値の要素が `None` の場合は「即時公開 (public)」
    - 戻り値の要素が ISO 文字列 (`YYYY-MM-DDTHH:MM:SSZ`) の場合は「指定時刻に自動公開される予約投稿 (private + publishAt)」
    - 過去の投稿・予約履歴を参照し、直近4時間以内に投稿がない場合は1本目を即時公開、2本目以降をJSTゴールデンタイム枠へ順番に予約する。
      既に直近で投稿済み、または未来の予約枠が埋まっている場合は、そのさらに後ろの空きゴールデンタイム枠へ自動連結する。
    """
    if count <= 0:
        return []
    if immediate_all:
        return [None] * count

    jst_tz = dt.timezone(dt.timedelta(hours=9))
    if now_utc is None:
        now_utc = dt.datetime.now(dt.timezone.utc)
    now_jst = now_utc.astimezone(jst_tz)

    latest_scheduled_utc: dt.datetime | None = None
    for h in history.values():
        if not h.get("youtube_video_id"):
            continue
        pub_dt = _parse_iso_datetime(str(h.get("youtube_publish_at") or "")) or _parse_iso_datetime(
            str(h.get("youtube_uploaded_at") or "")
        )
        if pub_dt and (latest_scheduled_utc is None or pub_dt > latest_scheduled_utc):
            latest_scheduled_utc = pub_dt

    schedule: list[str | None] = []
    min_gap = dt.timedelta(hours=YOUTUBE_MIN_GAP_HOURS)

    if latest_scheduled_utc is None or (now_utc - latest_scheduled_utc) >= min_gap:
        # 直近4時間以内に公開された動画がなく、未来の予約もなければ1本目は即時公開
        schedule.append(None)
        cursor_jst = now_jst + dt.timedelta(hours=3)
    else:
        # 直近で公開済み、または未来に予約済みの動画がある場合は、最後の公開予定時刻の後ろからスロットを探す
        base_utc = max(now_utc + dt.timedelta(minutes=30), latest_scheduled_utc + dt.timedelta(hours=2, minutes=30))
        cursor_jst = base_utc.astimezone(jst_tz)

    while len(schedule) < count:
        next_slot_jst = _next_golden_slot_jst(cursor_jst)
        slot_utc = next_slot_jst.astimezone(dt.timezone.utc)
        schedule.append(slot_utc.strftime("%Y-%m-%dT%H:%M:%SZ"))
        # 次の動画はその次のゴールデンタイム枠に入るようカーソルを2時間半進める
        cursor_jst = next_slot_jst + dt.timedelta(hours=2, minutes=30)

    return schedule


def format_publish_at_jst_label(publish_at_iso: str | None) -> str:
    """ログ表示用に予約時刻を日本時間（JST）の分かりやすい文字列に変換する。"""
    if not publish_at_iso:
        return "即時公開 (public)"
    dt_utc = _parse_iso_datetime(publish_at_iso)
    if not dt_utc:
        return f"予約公開 ({publish_at_iso})"
    jst_tz = dt.timezone(dt.timedelta(hours=9))
    dt_jst = dt_utc.astimezone(jst_tz)
    return f"予約公開 ({dt_jst.strftime('%Y-%m-%d %H:%M')} JST)"


def upload_video_to_youtube(
    mp4_path: Path,
    article: dict[str, Any],
    access_token: str,
    privacy_status: str = "public",
    publish_at: str | None = None,
) -> str:
    """
    YouTube Data API v3 の Resumable Upload プロトコルを用いて MP4 動画をアップロードし、
    発行された YouTube Video ID を返す（標準ライブラリのみ）。
    `publish_at` (ISO 8601 UTC文字列) が指定された場合はスケジュール予約公開 (`private` + `publishAt`) として登録する。
    """
    title, description, tags = build_youtube_metadata(article)
    file_size = mp4_path.stat().st_size

    status_block: dict[str, Any] = {
        "selfDeclaredMadeForKids": False,
    }
    if publish_at:
        # YouTube API の仕様上、publishAt（予約投稿）を使う場合は privacyStatus を "private" にする必要がある
        status_block["privacyStatus"] = "private"
        status_block["publishAt"] = publish_at
    else:
        status_block["privacyStatus"] = privacy_status

    metadata = {
        "snippet": {
            "title": title,
            "description": description,
            "tags": tags,
            "categoryId": "20",  # Gaming
            "defaultLanguage": "ja",
            "defaultAudioLanguage": "ja",
        },
        "status": status_block,
    }
    meta_bytes = json.dumps(metadata, ensure_ascii=False).encode("utf-8")

    init_url = "https://www.googleapis.com/upload/youtube/v3/videos?uploadType=resumable&part=snippet,status"
    init_req = urllib.request.Request(
        init_url,
        data=meta_bytes,
        headers={
            "Authorization": f"Bearer {access_token}",
            "Content-Type": "application/json; charset=UTF-8",
            "X-Upload-Content-Length": str(file_size),
            "X-Upload-Content-Type": "video/mp4",
        },
        method="POST",
    )

    try:
        with urllib.request.urlopen(init_req, timeout=30) as resp:
            upload_url = resp.headers.get("Location")
    except urllib.error.HTTPError as e:
        err_body = ""
        try:
            err_body = e.read().decode("utf-8", errors="replace")
        except Exception:
            pass
        raise RuntimeError(f"YouTube Upload 初期化エラー (HTTP {e.code}): {err_body}") from e

    if not upload_url:
        raise RuntimeError("YouTube Resumable Upload の Location URL が取得できませんでした。")

    video_bytes = mp4_path.read_bytes()
    put_req = urllib.request.Request(
        upload_url,
        data=video_bytes,
        headers={
            "Authorization": f"Bearer {access_token}",
            "Content-Length": str(file_size),
            "Content-Type": "video/mp4",
        },
        method="PUT",
    )

    try:
        with urllib.request.urlopen(put_req, timeout=300) as resp:
            res_json = json.loads(resp.read().decode("utf-8"))
            video_id = str(res_json.get("id") or "").strip()
            if not video_id:
                raise RuntimeError(f"レスポンスに動画IDが含まれていません: {res_json}")
            return video_id
    except urllib.error.HTTPError as e:
        err_body = ""
        try:
            err_body = e.read().decode("utf-8", errors="replace")
        except Exception:
            pass
        raise RuntimeError(f"YouTube 動画データ送信エラー (HTTP {e.code}): {err_body}") from e


def interactive_youtube_setup() -> None:
    """`python make_short.py --youtube-setup` 実行時の対話式セットアップウィザード。"""
    load_dotenv()
    print("\n" + "=" * 72)
    print("🎬 YouTube Shorts 自動アップロード 初回セットアップ")
    print("=" * 72)
    creds = get_youtube_client_credentials()
    if not creds:
        print(
            "\n【事前準備（Google Cloud Console で1回だけ行います・無料）】\n"
            "1. https://console.cloud.google.com/ を開き、プロジェクトを作成（または選択）\n"
            "2. 「APIとサービス」＞「ライブラリ」から『YouTube Data API v3』を検索して「有効にする」\n"
            "3. 「APIとサービス」＞「OAuth 同意画面」を設定（外部 / テストユーザーに自分のGoogleアカウントを追加）\n"
            "4. 「APIとサービス」＞「認証情報」＞「認証情報を作成」＞「OAuth クライアント ID」\n"
            "   - アプリケーションの種類: 『デスクトップ アプリ』\n"
            "5. 発行された JSON（client_secret_xxx.json）をこのフォルダ（D:\\antigrav\\svngs）に置くか、\n"
            "   以下に クライアントID と クライアントシークレット を貼り付けてください。\n"
        )
        cid = input("YOUTUBE_CLIENT_ID を入力してください: ").strip()
        csec = input("YOUTUBE_CLIENT_SECRET を入力してください: ").strip()
        if not cid or not csec:
            print("[ERROR] クライアントIDまたはシークレットが空のため中断しました。", file=sys.stderr)
            sys.exit(1)
        save_env_var("YOUTUBE_CLIENT_ID", cid)
        save_env_var("YOUTUBE_CLIENT_SECRET", csec)
        creds = (cid, csec)

    run_youtube_oauth_flow(creds[0], creds[1])
    print("\n[DONE] セットアップ完了！次回から `python make_short.py` で自動的にYouTubeへ公開投稿＆MP4削除が行われます。")


def score_article_for_shorts(article: dict[str, Any]) -> float:
    """
    YouTube Shorts の実測アナリティクスに基づき、1,000再生超え＆サイト誘導・アフィリエイト成約が
    出やすい「鉄板テーマ記事」を優先するためのスコアを計算する。
    - 加点:
      1) 全FPS層に刺さる設定・エイム理論 (DPI, 感度, 振り向き, トラッキング, マイクロフリック, 脱力, 持ち方)
      2) 購買直結のデバイス比較・組み合わせ (ガラスパッド, ソール, ARTISAN, Viper, SUPERLIGHT, OP1, Wallhack 等)
      3) 登場デバイス (`devices`) が登録されている記事（画面上部に登場デバイスバッジが表示される）
      4) 元スレッドのコメント数・スコア
    - 減点:
      海外ローカル店舗や個人の身の上話（Best Buy, ギフト券, 盗難, アレルギー, カスタムペイント代行 等）
    """
    title = str(article.get("title_ja") or "")
    hook = str(article.get("hook_ja") or "")
    devs = article.get("devices") or []
    dev_names = " ".join(str(d.get("name") or "") for d in devs if isinstance(d, dict))
    text = f"{title} {hook} {dev_names}".lower()

    score = 0.0

    # 1. 台本行数が充実している（5行以上）記事を最優先ベースにする
    script_len = len(article.get("short_script") or [])
    if script_len >= 5:
        score += 100.0

    # 2. 登場デバイス数ボーナス（画面上部バッジ表示＆アフィリエイト成約に直結）
    if devs:
        score += min(len(devs), 4) * 12.0

    # 3. 1,000再生超え実績のある鉄板キーワード加点
    high_impact_keywords = [
        ("dpi", 28.0),
        ("感度", 22.0),
        ("センシ", 22.0),
        ("振り向き", 20.0),
        ("ガラス", 26.0),
        ("ソール", 26.0),
        ("ptfe", 18.0),
        ("u9", 18.0),
        ("jade", 18.0),
        ("obsidian", 18.0),
        ("artisan", 25.0),
        ("零", 20.0),
        ("飛燕", 20.0),
        ("疾風", 20.0),
        ("雷電", 20.0),
        ("99式", 20.0),
        ("viper", 25.0),
        ("superlight", 25.0),
        ("gpx", 24.0),
        ("deathadder", 20.0),
        ("wallhack", 22.0),
        ("sp-004", 22.0),
        ("op1", 22.0),
        ("zowie", 18.0),
        ("pulsar", 18.0),
        ("lamzu", 18.0),
        ("kovaak", 16.0),
        ("voltaic", 16.0),
        ("トラッキング", 16.0),
        ("マイクロフリック", 18.0),
        ("フリック", 14.0),
        ("脱力", 18.0),
        ("力み", 16.0),
        ("つかみ持ち", 18.0),
        ("つまみ持ち", 18.0),
        ("かぶせ持ち", 18.0),
        ("グリップ", 14.0),
        ("軽量", 16.0),
        ("比較", 15.0),
        ("おすすめ", 14.0),
        ("移行", 14.0),
    ]
    for kw, pts in high_impact_keywords:
        if kw in text:
            score += pts

    # 4. ニッチすぎる個人雑談・海外店舗固有ネタは後回しにする減点
    low_appeal_keywords = [
        ("盗難", -45.0),
        ("ギフト券", -45.0),
        ("best buy", -45.0),
        ("アレルギー", -35.0),
        ("ペイント代行", -30.0),
        ("カスタムペイント", -25.0),
        ("偽物", -20.0),
        ("aliexpress", -20.0),
    ]
    for kw, penalty in low_appeal_keywords:
        if kw in text:
            score += penalty

    # 5. 元スレッドのコメント数による微調整（最大+15点）
    num_comments = int(article.get("num_comments") or 0)
    score += min(num_comments, 50) * 0.3

    return score


def _parse_max_uploads_arg(argv: list[str]) -> int:
    """コマンドライン引数 `--max-uploads N` または環境変数 `YOUTUBE_MAX_UPLOADS_PER_RUN` から1回あたりの上限を取得する。"""
    for i, arg in enumerate(argv):
        if arg == "--max-uploads" and i + 1 < len(argv):
            try:
                return max(0, int(argv[i + 1]))
            except ValueError:
                pass
        elif arg.startswith("--max-uploads="):
            try:
                return max(0, int(arg.split("=", 1)[1]))
            except ValueError:
                pass
    env_val = (os.environ.get("YOUTUBE_MAX_UPLOADS_PER_RUN") or "").strip()
    if env_val:
        try:
            return max(0, int(env_val))
        except ValueError:
            pass
    return DEFAULT_MAX_UPLOADS_PER_RUN


def main() -> None:
    if "--self-test" in sys.argv:
        assert format_srt_time(65.432) == "00:01:05,432"
        assert "アーティザン" in to_voicevox_reading("ARTISANのパッド")
        assert "キークロン エムシックス" in to_voicevox_reading("Keychron M6が候補")
        assert "スーパーストライク" in to_voicevox_reading("Superstrike X3")
        t, d, tags = build_youtube_metadata({
            "id": "demo",
            "title_ja": "【検証】ガラスマウスパッドのメリットと弱点まとめ",
            "hook_ja": "海外Redditで話題のガラスパッド議論を要約！",
            "consensus_points": ["初動が軽い", "アームカバー必須"],
            "devices": [{"name": "Wallhack SP-004"}],
            "subreddit": "MousepadReview",
        })
        assert t.endswith("#Shorts") and len(t) <= 100
        assert "VOICEVOX:ずんだもん" in d and "Wallhack SP-004" in d
        assert "Shorts" in tags
        # 予約投稿スケジュールのテスト（1本目は即時、2本目以降はJSTゴールデンタイム予約）
        test_now = dt.datetime(2026, 11, 5, 0, 0, 0, tzinfo=dt.timezone.utc)  # 09:00 JST
        sched_empty = plan_youtube_publish_schedule(3, {}, immediate_all=False, now_utc=test_now)
        assert sched_empty[0] is None
        assert sched_empty[1] == "2026-11-05T03:15:00Z"  # 12:15 JST
        assert sched_empty[2] == "2026-11-05T09:00:00Z"  # 18:00 JST
        # 直近投稿ありの場合は1本目から予約枠に入ることを確認
        sched_recent = plan_youtube_publish_schedule(
            2,
            {"prev": {"youtube_video_id": "v1", "youtube_uploaded_at": "2026-11-04T23:00:00Z"}},
            immediate_all=False,
            now_utc=test_now,
        )
        assert sched_recent[0] == "2026-11-05T03:15:00Z"
        assert sched_recent[1] == "2026-11-05T09:00:00Z"
        # 鉄板テーマ優先スコアリングのテスト
        high_art = {
            "title_ja": "400DPIから1600DPIへ移行すべきか？ガラスパッドとViper V3 Proの比較",
            "devices": [{"name": "Razer Viper V3 Pro"}],
            "short_script": [{}] * 8,
        }
        low_art = {
            "title_ja": "Best Buyのギフト券で盗難被害の代替え機探し",
            "devices": [],
            "short_script": [{}] * 8,
        }
        assert score_article_for_shorts(high_art) > score_article_for_shorts(low_art) + 80
        print("SHORT_SELF_TEST_OK")
        return

    load_dotenv()

    if "--youtube-setup" in sys.argv:
        interactive_youtube_setup()
        return

    if not ARTICLES_FILE.exists():
        print("[ERROR] `data/articles.json` が見つかりません。先に `python pipeline.py` を実行してください。", file=sys.stderr)
        sys.exit(1)

    articles: list[dict[str, Any]] = json.loads(ARTICLES_FILE.read_text(encoding="utf-8"))
    history = load_shorts_history()
    if sync_state_between_articles_and_history(articles, history):
        save_articles_json(articles)
        save_shorts_history(history)

    target_articles = [a for a in articles if a.get("status") == "published"]
    if not target_articles:
        print("[INFO] `published` 状態の記事がないため、`draft` 記事を対象にします。")
        target_articles = list(articles)

    # 1,000再生超え＆アフィリエイト成約が出やすい鉄板テーマ（DPI・ガラスパッド・人気デバイス比較等）のスコア順で優先処理する
    target_articles.sort(
        key=lambda a: (score_article_for_shorts(a), a.get("created_at", "")),
        reverse=True,
    )

    force_regen = "--force" in sys.argv
    upload_only = "--upload-only" in sys.argv
    no_upload = "--no-upload" in sys.argv
    keep_mp4 = "--keep-mp4" in sys.argv or (os.environ.get("YOUTUBE_KEEP_MP4") or "").strip().lower() in ("1", "true", "yes")
    privacy_status = (os.environ.get("YOUTUBE_PRIVACY_STATUS") or "public").strip() or "public"
    max_uploads = _parse_max_uploads_arg(sys.argv)

    # --- Step 1: 未生成記事のショート動画生成（一度生成した記事はMP4を消しても再生成しない） ---
    generated_count = 0
    if not upload_only:
        existing_ready_mp4s = sum(
            1 for art in target_articles
            if (SHORTS_OUT_DIR / f"{art['id']}.mp4").exists()
            and not (art.get("youtube_video_id") or history.get(str(art.get("id") or ""), {}).get("youtube_video_id"))
        )

        need_gen_articles = [
            art for art in target_articles
            if force_regen or not (
                art.get("short_generated")
                or history.get(str(art.get("id") or ""), {}).get("short_generated")
                or art.get("youtube_video_id")
                or (SHORTS_OUT_DIR / f"{art['id']}.mp4").exists()
            )
        ]

        # HDD圧迫＆長時間待機を防ぐため、`--all` 指定時以外は今回のアップロード上限（max_uploads）に必要な本数だけ生成する
        if "--all" not in sys.argv and not force_regen and max_uploads > 0:
            gen_budget = max(0, max_uploads - existing_ready_mp4s)
            if len(need_gen_articles) > gen_budget:
                print(
                    f"[INFO] 未生成の公開記事が {len(need_gen_articles)} 件あります。"
                    f"HDD節約のため、今回のアップロード枠（最大{max_uploads}本、既存未投稿MP4 {existing_ready_mp4s}本）に合わせて "
                    f"{gen_budget} 本を生成します。"
                )
                need_gen_articles = need_gen_articles[:gen_budget]

        if need_gen_articles:
            if not check_prerequisites():
                sys.exit(1)
            bgm_path, se_paths = ensure_default_sound_assets()

            BG_DIR.mkdir(parents=True, exist_ok=True)
            bg_files: list[Path] = []
            for ext in ("*.mp4", "*.mov", "*.mkv", "*.webm"):
                bg_files.extend(sorted(BG_DIR.glob(ext)))
            if not bg_files:
                print("[WARN] `assets/bg/` に背景用の動画 (.mp4 等) が見つからないため、ダーク背景で動画を生成します。")

            for idx, art in enumerate(need_gen_articles):
                aid = str(art["id"])
                out_mp4 = SHORTS_OUT_DIR / f"{aid}.mp4"
                bg = bg_files[idx % len(bg_files)] if bg_files else None
                print(f"\n[INFO] ({idx + 1}/{len(need_gen_articles)}) ショート動画生成開始: [{aid}] {art.get('title_ja')}")
                build_short_for_article(art, bg, bgm_path, se_paths, out_mp4)
                if out_mp4.exists():
                    now_iso = dt.datetime.now(dt.timezone.utc).isoformat()
                    art["short_generated"] = True
                    art["short_generated_at"] = now_iso
                    sync_state_between_articles_and_history(articles, history)
                    save_articles_json(articles)
                    save_shorts_history(history)
                    generated_count += 1
        elif existing_ready_mp4s > 0:
            print(f"[INFO] 既に未アップロードの生成済みMP4が {existing_ready_mp4s} 本あるため、新規生成をスキップしてアップロードに進みます。")
        else:
            print("[INFO] すべての対象記事はショート動画生成済みです（生成済み動画はMP4削除後も再生成されません）。")

    # --- Step 2: YouTube Shorts への自動アップロード ＆ アップロード完了後の MP4 自動削除 ---
    uploaded_count = 0
    deleted_count = 0
    if not no_upload:
        pending_uploads: list[tuple[dict[str, Any], Path]] = []
        for art in target_articles:
            aid = str(art.get("id") or "").strip()
            if not aid:
                continue
            mp4_path = SHORTS_OUT_DIR / f"{aid}.mp4"
            already_uploaded = bool(
                art.get("youtube_video_id")
                or history.get(aid, {}).get("youtube_video_id")
            )
            if mp4_path.exists():
                if already_uploaded and not keep_mp4:
                    # 既にYouTube投稿済みの動画ファイルが残っていれば自動削除してHDDを空ける
                    try:
                        mp4_path.unlink()
                        deleted_count += 1
                        print(f"[CLEAN] YouTube投稿済みのローカル動画を削除しました: {mp4_path}")
                    except Exception as e:
                        print(f"[WARN] 動画削除失敗 ({mp4_path}): {e}", file=sys.stderr)
                elif not already_uploaded:
                    pending_uploads.append((art, mp4_path))

        if pending_uploads:
            try:
                access_token = get_youtube_access_token()
            except Exception as e:
                print(f"[WARN] YouTube OAuth 認証に失敗したためアップロードをスキップしました: {e}", file=sys.stderr)
                access_token = None

            if not access_token:
                print(
                    "\n[INFO] YouTube 自動アップロードを行うには、初回のみ以下のコマンドでOAuth設定を行ってください：\n"
                    "       python make_short.py --youtube-setup\n"
                    f"       （未アップロードの動画 {len(pending_uploads)} 本は {SHORTS_OUT_DIR} に保持されています）"
                )
            else:
                to_upload = pending_uploads[:max_uploads] if max_uploads > 0 else []
                immediate_all = "--now" in sys.argv
                schedule_list = plan_youtube_publish_schedule(
                    len(to_upload),
                    history,
                    immediate_all=immediate_all,
                )
                mode_desc = "全件即時公開 (--now)" if immediate_all else "連投ロック防止・ゴールデンタイム自動予約モード (07:30 / 12:15 / 18:00 / 21:00 JST)"
                print(
                    f"\n[INFO] YouTube Shorts 自動アップロードを開始します "
                    f"(対象: {len(to_upload)}/{len(pending_uploads)}本 / モード: {mode_desc})"
                )
                for idx, ((art, mp4_path), pub_at) in enumerate(zip(to_upload, schedule_list), start=1):
                    aid = str(art["id"])
                    pub_label = format_publish_at_jst_label(pub_at)
                    print(f"  -> ({idx}/{len(to_upload)}) アップロード中 [{pub_label}]: [{aid}] {art.get('title_ja')} ...")
                    try:
                        video_id = upload_video_to_youtube(
                            mp4_path,
                            art,
                            access_token,
                            privacy_status=privacy_status,
                            publish_at=pub_at,
                        )
                        yt_url = f"https://youtube.com/shorts/{video_id}"
                        now_iso = dt.datetime.now(dt.timezone.utc).isoformat()
                        effective_pub_at = pub_at or now_iso
                        art["short_generated"] = True
                        art["youtube_video_id"] = video_id
                        art["youtube_url"] = yt_url
                        art["youtube_uploaded_at"] = now_iso
                        art["youtube_publish_at"] = effective_pub_at
                        sync_state_between_articles_and_history(articles, history)
                        save_articles_json(articles)
                        save_shorts_history(history)
                        uploaded_count += 1
                        print(f"  [OK] YouTubeアップロード完了 ({pub_label}): {yt_url}")

                        if not keep_mp4:
                            try:
                                mp4_path.unlink()
                                deleted_count += 1
                                print(f"  [CLEAN] HDD容量節約のためアップロード済みMP4を削除しました: {mp4_path}")
                            except Exception as del_err:
                                print(f"  [WARN] MP4削除失敗 ({mp4_path}): {del_err}", file=sys.stderr)
                    except Exception as up_err:
                        err_msg = str(up_err)
                        print(f"  [WARN] YouTubeアップロード失敗 ({aid}): {err_msg}", file=sys.stderr)
                        if "quotaExceeded" in err_msg or "uploadLimitExceeded" in err_msg:
                            print("  [INFO] YouTube API の1日あたりアップロード上限に達したため、残りは次回実行時に持ち越します。")
                            break

    print(
        f"\n[DONE] 処理完了！（新規動画生成: {generated_count}本 / "
        f"YouTube投稿: {uploaded_count}本 / HDD解放削除: {deleted_count}本）"
    )


if __name__ == "__main__":
    main()


