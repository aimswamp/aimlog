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
from pathlib import Path
from typing import Any

VOICEVOX_URL = "http://127.0.0.1:50021"
SPEAKER_MAP = {
    "zundamon": 3,   # ずんだもん（ノーマル）
    "tsumugi": 8,    # 春日部つむぎ（ノーマル）
    "aoyama": 8,     # 旧データの aoyama も春日部つむぎに自動マッピング
}

# ショート動画向けのテンポ設定（1.20倍速・文末の間0.10秒でサクサク進行）
VOICE_SPEED_SCALE = 1.20
VOICE_POST_PHONEME_LENGTH = 0.10

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

ARTICLES_FILE = Path("data/articles.json")
BG_DIR = Path("assets/bg")
BGM_DIR = Path("assets/bgm")
SE_DIR = Path("assets/se")
SHORTS_OUT_DIR = Path("dist/shorts")

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

        total_sec = current_time + 0.4
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


def main() -> None:
    if "--self-test" in sys.argv:
        assert format_srt_time(65.432) == "00:01:05,432"
        assert "アーティザン" in to_voicevox_reading("ARTISANのパッド")
        assert "キークロン エムシックス" in to_voicevox_reading("Keychron M6が候補")
        assert "スーパーストライク" in to_voicevox_reading("Superstrike X3")
        print("SHORT_SELF_TEST_OK")
        return

    if not ARTICLES_FILE.exists():
        print("[ERROR] `data/articles.json` が見つかりません。先に `python pipeline.py` を実行してください。", file=sys.stderr)
        sys.exit(1)

    if not check_prerequisites():
        sys.exit(1)

    bgm_path, se_paths = ensure_default_sound_assets()

    BG_DIR.mkdir(parents=True, exist_ok=True)
    bg_files: list[Path] = []
    for ext in ("*.mp4", "*.mov", "*.mkv", "*.webm"):
        bg_files.extend(sorted(BG_DIR.glob(ext)))

    if not bg_files:
        print("[WARN] `assets/bg/` に背景用の動画 (.mp4 等) が見つからないため、ダーク背景で動画を生成します。")

    articles = json.loads(ARTICLES_FILE.read_text(encoding="utf-8"))
    target_articles = [a for a in articles if a.get("status") == "published"]
    if not target_articles:
        print("[INFO] `published` 状態の記事がないため、`draft` 記事からショート動画を生成します。")
        target_articles = list(articles)

    # 8行構成の新しい台本（または新しい記事）を優先して処理する
    target_articles.sort(
        key=lambda a: (len(a.get("short_script") or []) >= 5, a.get("created_at", "")),
        reverse=True,
    )

    generated_count = 0
    for idx, art in enumerate(target_articles):
        out_mp4 = SHORTS_OUT_DIR / f"{art['id']}.mp4"
        if out_mp4.exists() and "--force" not in sys.argv:
            print(f"[SKIP] 既に生成済みです: {out_mp4} (上書き再生成する場合は `python make_short.py --force` を実行)")
            continue
        bg = bg_files[idx % len(bg_files)] if bg_files else None
        print(f"\n[INFO] ({idx + 1}/{len(target_articles)}) ショート動画生成開始: {art['title_ja']}")
        build_short_for_article(art, bg, bgm_path, se_paths, out_mp4)
        generated_count += 1

    print(f"\n[DONE] ショート動画の生成処理が完了しました（新規生成: {generated_count}本 / 保存先: {SHORTS_OUT_DIR}）")


if __name__ == "__main__":
    main()

