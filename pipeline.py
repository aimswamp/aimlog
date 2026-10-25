#!/usr/bin/env python3
"""
海外AIM＆マウス界隈 集合知キュレーション＆自動アフィリエイトDB パイプライン (Phase 1)
- Reddit 3大サブレ (r/FPSAimTrainer, r/MouseReview, r/MousepadReview) から議論スレを厳選収集
- Gemini API (gemini-3.8-flash) で集合知まとめ・登場デバイス評判・X投稿文・ショート動画台本を一括生成
- Amazon直 / 楽天 / もしもアフィリエイトの検索リンク自動生成 ＋ 商品マスター表キャッシュ解決
- Googleスプレッドシート連携 (GAS Webhook または ローカルJSON/CSV)
- 特化型Webサイト＆「海外Reddit話題度ランキング」静的HTML出力 + Xツリー投稿
"""

from __future__ import annotations

import base64
import csv
import datetime as dt
import hashlib
import hmac
import html
import json
import os
import secrets
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path
from typing import Any

# --- 定数・設定 ---
SUBREDDITS = ["FPSAimTrainer", "MouseReview", "MousepadReview"]
MIN_COMMENTS = 15
MAX_DRAFTS_PER_RUN = 5
# Reddit公式ガイドライン準拠のBot形式User-Agent（Mozilla偽装によるFastly 403 Blockedを回避）
USER_AGENT = "windows:com.svngs.aimcurator:v1.1.0 (by /u/aimcurator_jp)"
GEMINI_MODEL = "gemini-3.8-flash"

DATA_DIR = Path("data")
ARTICLES_FILE = DATA_DIR / "articles.json"
PRODUCTS_FILE = DATA_DIR / "products.csv"
DIST_DIR = Path("dist")
ENV_FILE = Path(".env")


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


# ============================================================================
# 1. アフィリエイトリンク解決エンジン（Amazon直 / 楽天 / もしも 両対応）
# ============================================================================

import re

# 海外表記 → 日本国内Amazon/楽天でヒットしやすい表記への正規化ルール
JP_NAME_RULES: list[tuple[re.Pattern[str], str]] = [
    (re.compile(r"\bLogitech\b", re.IGNORECASE), "Logicool"),
    (re.compile(r"\bG\s*Pro\s*(?:X\s*)?Superlight\s*2\b", re.IGNORECASE), "G PRO X SUPERLIGHT 2"),
    (re.compile(r"\bG\s*Pro\s*X\s*Superlight\b", re.IGNORECASE), "G PRO X SUPERLIGHT"),
    (re.compile(r"\bArtisan\s+Raiden\b", re.IGNORECASE), "ARTISAN 雷電"),
    (re.compile(r"\bArtisan\s+Zero\b", re.IGNORECASE), "ARTISAN 零"),
    (re.compile(r"\bArtisan\s+(?:Hayate\s*)?Otsu\b", re.IGNORECASE), "ARTISAN 疾風乙"),
    (re.compile(r"\bArtisan\s+Hien\b", re.IGNORECASE), "ARTISAN 飛燕"),
    (re.compile(r"\bArtisan\s+(?:Type[-\s]*99|99)\b", re.IGNORECASE), "ARTISAN 99式"),
    (re.compile(r"\bXraypad\b", re.IGNORECASE), "X-raypad"),
]


def normalize_product_name_jp(name: str) -> str:
    """海外表記のデバイス名を日本のAmazon/楽天で検索・成約しやすい名称に正規化する。"""
    cleaned = name.strip()
    for pattern, repl in JP_NAME_RULES:
        cleaned = pattern.sub(repl, cleaned)
    # "Logicool Logicool" のような重複を防止
    cleaned = re.sub(r"\b(Logicool)\s+\1\b", r"\1", cleaned, flags=re.IGNORECASE)
    return cleaned


def load_product_master(csv_path: Path = PRODUCTS_FILE) -> dict[str, dict[str, str]]:
    """商品マスター表（CSV）を読み込む。キーは小文字正規化した製品名。"""
    master: dict[str, dict[str, str]] = {}
    if not csv_path.exists():
        return master
    with csv_path.open("r", encoding="utf-8-sig", newline="") as f:
        for row in csv.DictReader(f):
            name = (row.get("name") or "").strip()
            if name:
                master[name.lower()] = row
    return master


def build_affiliate_urls(
    product_name: str,
    master: dict[str, dict[str, str]] | None = None,
    env: dict[str, str] | None = None,
) -> dict[str, str]:
    """
    製品名からAmazon・楽天のアフィリエイトURLを生成する。
    1. 商品マスター表に個別URLが登録されていればそれを優先使用
    2. 未登録なら、API審査不要で初日から使える「製品名検索アフィリエイトURL」を自動生成
       - Amazonアソシエイト直 (AMAZON_ASSOC_TAG)
       - 楽天アフィリエイト直 (RAKUTEN_AFFILIATE_ID)
       - もしもアフィリエイト経由 (MOSHIMO_AMAZON_AID / MOSHIMO_RAKUTEN_AID)
    """
    cfg = env if env is not None else os.environ
    norm_name = normalize_product_name_jp(product_name)
    master_row = (master or {}).get(norm_name.lower(), {}) or (master or {}).get(product_name.strip().lower(), {})

    # 検索キーワード（日本国内のECでヒットしやすい正規化済み製品名）
    q_encoded = urllib.parse.quote_plus(norm_name)
    amazon_search_raw = f"https://www.amazon.co.jp/s?k={q_encoded}"
    rakuten_search_raw = f"https://search.rakuten.co.jp/search/mall/{urllib.parse.quote(norm_name)}/"

    # 1. Amazon URLの決定
    custom_amazon = (master_row.get("amazon_url") or "").strip()
    amazon_tag = (cfg.get("AMAZON_ASSOC_TAG") or "").strip()
    moshimo_amzn_aid = (cfg.get("MOSHIMO_AMAZON_AID") or "").strip()

    if custom_amazon:
        base_amzn = custom_amazon
    else:
        base_amzn = amazon_search_raw

    if moshimo_amzn_aid:
        # もしもアフィリエイト経由のAmazonリンク形式
        amazon_url = (
            f"https://af.moshimo.com/af/c/click?a_id={urllib.parse.quote(moshimo_amzn_aid)}"
            f"&p_id=170&pc_id=185&pl_id=4062&url={urllib.parse.quote(base_amzn, safe='')}"
        )
    elif amazon_tag:
        sep = "&" if "?" in base_amzn else "?"
        amazon_url = f"{base_amzn}{sep}tag={urllib.parse.quote(amazon_tag)}"
    else:
        amazon_url = base_amzn

    # 2. 楽天 URLの決定
    custom_rakuten = (master_row.get("rakuten_url") or "").strip()
    rakuten_id = (cfg.get("RAKUTEN_AFFILIATE_ID") or "").strip()
    moshimo_rakuten_aid = (cfg.get("MOSHIMO_RAKUTEN_AID") or "").strip()

    base_rktn = custom_rakuten if custom_rakuten else rakuten_search_raw

    if moshimo_rakuten_aid:
        # もしもアフィリエイト経由の楽天リンク形式
        rakuten_url = (
            f"https://af.moshimo.com/af/c/click?a_id={urllib.parse.quote(moshimo_rakuten_aid)}"
            f"&p_id=54&pc_id=54&pl_id=616&url={urllib.parse.quote(base_rktn, safe='')}"
        )
    elif rakuten_id:
        rakuten_url = (
            f"https://hb.afl.rakuten.co.jp/hgc/{urllib.parse.quote(rakuten_id)}/"
            f"?pc={urllib.parse.quote(base_rktn, safe='')}"
        )
    else:
        rakuten_url = base_rktn

    return {
        "amazon_url": amazon_url,
        "rakuten_url": rakuten_url,
    }


# ============================================================================
# 2. Reddit スレッド収集＆フィルタリング
# ============================================================================

def is_meaningful_thread(post: dict[str, Any], min_comments: int = MIN_COMMENTS) -> bool:
    """
    単なる「新しいマウス買った！（写真1枚のみ）」の自慢スレや固定メタスレを除外し、
    議論・質問・比較・レビュー・エイム理論が盛り上がっているスレッドのみを通す。
    """
    if post.get("stickied") or post.get("over_18"):
        return False
    num_comments = int(post.get("num_comments") or 0)
    if num_comments < min_comments:
        return False

    selftext = (post.get("selftext") or "").strip()
    is_self = bool(post.get("is_self"))
    # 画像直リンク等で本文が短すぎる投稿は、コメント数が非常に多い議論（40件以上）でない限り除外
    if not is_self and len(selftext) < 40 and num_comments < 40:
        return False
    return True


def fetch_json(url: str) -> Any:
    """
    Reddit等からJSONを取得する共通ヘルパー。
    1. Reddit規約準拠のUser-Agentで urllib から取得
    2. ブロック時やHTML応答時は OS標準の curl で再試行
    """
    headers = {
        "User-Agent": USER_AGENT,
        "Accept": "application/json",
    }
    try:
        req = urllib.request.Request(url, headers=headers)
        with urllib.request.urlopen(req, timeout=20) as resp:
            raw = resp.read().decode("utf-8", errors="replace").strip()
            if raw.startswith("{") or raw.startswith("["):
                return json.loads(raw)
    except urllib.error.HTTPError as e:
        if e.code not in (403, 429):
            raise
    except Exception:
        pass

    # フォールバック: OS標準の curl コマンド経由で取得
    import subprocess
    cmd = [
        "curl",
        "-sL",
        "--max-time", "20",
        "-A", USER_AGENT,
        "-H", "Accept: application/json",
        url,
    ]
    proc = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8", errors="replace")
    out = (proc.stdout or "").strip()
    if proc.returncode == 0 and (out.startswith("{") or out.startswith("[")):
        return json.loads(out)
    raise RuntimeError(f"JSON取得失敗 ({url})")


def _extract_comment_tree(raw_data: Any, max_comments: int = 35) -> list[dict[str, Any]]:
    """
    Reddit本体・Arctic Shift (tree / search) のJSON構造から、
    実際の親子関係 (id, parent_id)・投稿者名 (author)・フレア (flair)・スレ主判定 (is_op)・スコアを保った
    コメントツリー配列を抽出する（水増し・捏造なしの100%実在コメントのみ）。
    """
    nodes: list[dict[str, Any]] = []
    seen_ids: set[str] = set()

    def _walk(node: Any) -> None:
        if len(nodes) >= max_comments:
            return
        if isinstance(node, list):
            for item in node:
                _walk(item)
        elif isinstance(node, dict):
            # Reddit T1 comment object の判定
            is_t1 = (node.get("kind") == "t1" and isinstance(node.get("data"), dict))
            d = node["data"] if is_t1 else node

            if isinstance(d, dict) and "body" in d and "id" in d:
                cid = str(d.get("id") or "").strip()
                body = (d.get("body") or "").strip()
                # 削除済みや画像URL単体のコメントは除外し、通常の短文リプライはすべて保持する
                is_pure_image = body.startswith("https://preview.redd.it/") and "\n" not in body and " " not in body
                if cid and cid not in seen_ids and body and body not in ("[deleted]", "[removed]") and not is_pure_image:
                    seen_ids.add(cid)
                    raw_parent = str(d.get("parent_id") or "").strip()
                    parent_id = raw_parent[3:] if raw_parent.startswith("t1_") else None
                    author = str(d.get("author") or "redditor").strip()
                    flair = str(d.get("author_flair_text") or "").strip()
                    # リッチテキスト配列からフレア文字列を補完
                    if not flair and isinstance(d.get("author_flair_richtext"), list):
                        flair = " ".join(
                            str(part.get("t") or "").strip()
                            for part in d["author_flair_richtext"]
                            if isinstance(part, dict) and part.get("t")
                        ).strip()
                    nodes.append({
                        "id": cid,
                        "parent_id": parent_id,
                        "author": author,
                        "flair": flair,
                        "is_op": bool(d.get("is_submitter")),
                        "score": int(d.get("score") if d.get("score") is not None else 1),
                        "body_en": body[:1500],
                    })

            # 子要素の走査
            if is_t1:
                replies = d.get("replies")
                if isinstance(replies, dict):
                    _walk(replies)
                elif isinstance(replies, list):
                    _walk(replies)
            else:
                for key in ("data", "children", "comments", "replies"):
                    if key in node and isinstance(node[key], (dict, list)):
                        _walk(node[key])

    if isinstance(raw_data, list) and len(raw_data) == 2 and isinstance(raw_data[1], dict):
        _walk(raw_data[1])
    else:
        _walk(raw_data)

    # 親コメントが抽出範囲外または削除済みの場合はトップレベル (parent_id=None) に正規化し、階層 depth を計算
    id_map = {n["id"]: n for n in nodes}
    for n in nodes:
        pid = n.get("parent_id")
        if pid and pid not in id_map:
            n["parent_id"] = None
    for n in nodes:
        depth = 0
        curr_p = n.get("parent_id")
        visited: set[str] = set()
        while curr_p and curr_p in id_map and curr_p not in visited and depth < 6:
            visited.add(curr_p)
            depth += 1
            curr_p = id_map[curr_p].get("parent_id")
        n["depth"] = depth

    return _anonymize_comment_tree(nodes)


def _anonymize_comment_tree(nodes: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """
    トラブル防止のため、実在のRedditユーザー名をスレッド内で一貫した匿名表記
    （スレ主は『スレ主』、他ユーザーは登場順に『海外ユーザー1』『海外ユーザー2』…）へ変換する。
    """
    anon_map: dict[str, str] = {}
    counter = 1
    out: list[dict[str, Any]] = []
    for n in nodes:
        raw_au = str(n.get("author") or "anonymous").removeprefix("u/").strip()
        is_op = bool(n.get("is_op")) or raw_au in ("スレ主", "OP", "OriginalPoster")
        if is_op:
            anon_name = "スレ主"
        elif re.match(r"^海外ユーザー\d+$", raw_au):
            anon_name = raw_au
        else:
            if raw_au not in anon_map:
                anon_map[raw_au] = f"海外ユーザー{counter}"
                counter += 1
            anon_name = anon_map[raw_au]
        out.append({
            **n,
            "author": anon_name,
            "is_op": is_op,
        })
    return out


def _extract_comment_list(raw_data: Any) -> list[str]:
    """後方互換用のテキストリスト抽出ヘルパー。"""
    tree = _extract_comment_tree(raw_data, max_comments=35)
    return [f"[+{c['score']}] {c['body_en'][:800]}" for c in tree]


def _is_video_url(u: str) -> bool:
    """URLが動画リンク（v.redd.it / YouTube / Streamable / mp4等）かどうかを判定する。"""
    low = u.lower()
    return (
        "v.redd.it/" in low
        or "packaged-media.redd.it/" in low
        or "youtube.com/watch" in low
        or "youtu.be/" in low
        or "streamable.com/" in low
        or bool(re.search(r"\.(?:mp4|webm|mov)(?:\?.*)?$", low))
    )


def _extract_post_image_urls(post: dict[str, Any]) -> list[str]:
    """スレ主が投稿に添付した画像・動画（単一画像・Reddit動画・ギャラリー・本文内メディアURL）を抽出する。"""
    urls: list[str] = []

    def _add(u: str) -> None:
        clean_u = html.unescape(str(u or "").strip())
        if clean_u and clean_u.startswith("http") and clean_u not in urls:
            urls.append(clean_u)

    # 1. ギャラリー投稿 (media_metadata)
    media_meta = post.get("media_metadata")
    if isinstance(media_meta, dict) and media_meta:
        gallery_items = (post.get("gallery_data") or {}).get("items") if isinstance(post.get("gallery_data"), dict) else None
        ordered_ids: list[str] = []
        if isinstance(gallery_items, list):
            for g in gallery_items:
                if isinstance(g, dict) and g.get("media_id"):
                    ordered_ids.append(str(g["media_id"]))
        for mid in list(ordered_ids) + [k for k in media_meta.keys() if k not in ordered_ids]:
            m_obj = media_meta.get(mid)
            if not isinstance(m_obj, dict):
                continue
            s_obj = m_obj.get("s")
            if isinstance(s_obj, dict):
                img_u = s_obj.get("u") or s_obj.get("gif") or s_obj.get("mp4")
                if img_u:
                    m_ext = str(m_obj.get("m") or "image/jpeg").split("/")[-1]
                    if "i.redd.it/" in str(img_u) or "v.redd.it/" in str(img_u):
                        _add(str(img_u))
                    elif mid:
                        ext = "jpg" if m_ext == "jpg" else ("png" if m_ext == "png" else "jpeg")
                        _add(f"https://i.redd.it/{mid}.{ext}")

    # 2. 単一画像・動画リンク (post["url"] / is_video)
    post_url = str(post.get("url") or "").strip()
    post_hint = str(post.get("post_hint") or "").strip()
    is_video = bool(post.get("is_video"))
    if post_url and (
        post_hint in ("image", "hosted:video", "rich:video")
        or is_video
        or re.search(r"\.(?:jpg|jpeg|png|webp|gif|mp4|webm)(?:\?.*)?$", post_url, re.IGNORECASE)
        or post_url.startswith("https://i.redd.it/")
        or post_url.startswith("https://v.redd.it/")
        or post_url.startswith("https://i.imgur.com/")
        or "youtube.com/watch" in post_url
        or "youtu.be/" in post_url
        or "streamable.com/" in post_url
    ):
        _add(post_url)
    elif is_video:
        media_obj = post.get("media") or post.get("secure_media") or {}
        if isinstance(media_obj, dict) and isinstance(media_obj.get("reddit_video"), dict):
            rv = media_obj["reddit_video"]
            if rv.get("fallback_url"):
                _add(str(rv["fallback_url"]))

    # 3. 本文 (selftext) 内の直画像・動画URL
    selftext = str(post.get("selftext") or post.get("selftext_en") or "")
    for m in re.finditer(
        r"https?://(?:i\.redd\.it|v\.redd\.it|preview\.redd\.it|i\.imgur\.com|(?:www\.)?youtube\.com/watch|youtu\.be|streamable\.com)/[^\s\)\]\>\"']+",
        selftext,
    ):
        _add(m.group(0))

    return urls


def fetch_thread_comment_tree(sub: str, post_id: str, max_comments: int = 35) -> list[dict[str, Any]]:
    """指定スレッドIDの実際のコメントツリーをRedditまたはArctic Shiftから取得する。"""
    urls = [
        f"https://arctic-shift.photon-reddit.com/api/comments/tree?link_id=t3_{urllib.parse.quote(post_id)}&limit=100",
        f"https://www.reddit.com/r/{urllib.parse.quote(sub)}/comments/{urllib.parse.quote(post_id)}.json?limit=80&sort=top&raw_json=1",
        f"https://arctic-shift.photon-reddit.com/api/comments/search?link_id=t3_{urllib.parse.quote(post_id)}&limit=80",
    ]
    for c_url in urls:
        try:
            c_data = fetch_json(c_url)
            tree = _extract_comment_tree(c_data, max_comments=max_comments)
            if tree:
                return tree
        except Exception:
            continue
    return []


def _fetch_arctic_shift_threads(sub: str, existing_ids: set[str], needed: int) -> list[dict[str, Any]]:
    """
    Reddit本体が403を返す場合の公式ミラーアーカイブ (Arctic Shift API) フォールバック。
    ※Arctic Shiftでは直近投稿の `num_comments` スナップショットが 0 になる仕様があるため、
      本文のあるディスカッション投稿を対象にコメントAPIを直接引いて判定する。
    """
    results: list[dict[str, Any]] = []
    listing: dict[str, Any] = {}
    # 議論が成熟している1〜3日前のスレッドおよび最新スレッドを順に走査
    posts_pool: list[dict[str, Any]] = []
    for query_suffix in (
        f"?subreddit={urllib.parse.quote(sub)}&before=1d&limit=15",
        f"?subreddit={urllib.parse.quote(sub)}&before=2d&limit=15",
        f"?subreddit={urllib.parse.quote(sub)}&limit=15",
    ):
        try:
            listing = fetch_json(f"https://arctic-shift.photon-reddit.com/api/posts/search{query_suffix}")
            rows = listing.get("data") if isinstance(listing, dict) else []
            if isinstance(rows, list) and rows:
                posts_pool.extend(rows)
                if len(posts_pool) >= 15:
                    break
        except Exception:
            time.sleep(1.0)

    for post in posts_pool:
        if len(results) >= needed:
            break
        post_id = str(post.get("id") or "").strip()
        if not post_id or post_id in existing_ids:
            continue
        existing_ids.add(post_id)
        if post.get("stickied") or post.get("over_18"):
            continue
        selftext = (post.get("selftext") or "").strip()
        if selftext in ("[deleted]", "[removed]"):
            selftext = ""
        image_urls = _extract_post_image_urls(post)
        # 本文30文字以上、または添付画像・動画があるスレッドを対象にする
        if len(selftext) < 30 and not image_urls:
            continue

        # コメントツリー取得（t3_ プレフィックス付き link_id で tree / search を試行）
        comment_tree = fetch_thread_comment_tree(sub, post_id, max_comments=32)
        if len(comment_tree) < 4:
            continue

        top_comments = [f"[+{c['score']}] {c['body_en'][:800]}" for c in comment_tree]
        permalink = post.get("permalink") or f"/r/{sub}/comments/{post_id}/"
        results.append({
            "id": post_id,
            "subreddit": sub,
            "op_author": "スレ主",
            "op_flair": str(post.get("author_flair_text") or "").strip(),
            "title_en": post.get("title", ""),
            "selftext_en": selftext[:2500],
            "image_urls": image_urls,
            "score": int(post.get("score") or 0),
            "num_comments": max(int(post.get("num_comments") or 0), len(comment_tree)),
            "permalink": f"https://www.reddit.com{permalink}",
            "comments": top_comments[:32],
            "comment_tree": comment_tree,
        })
        print(f"[INFO] ミラーから良スレ発見: [r/{sub}] {post.get('title', '')[:55]} (実コメント{len(comment_tree)}件)")
        time.sleep(0.8)
    return results


def fetch_reddit_threads(
    existing_ids: set[str],
    max_total: int = MAX_DRAFTS_PER_RUN,
) -> list[dict[str, Any]]:
    """3大サブレディットから未処理の良スレと実コメントツリーを取得する（各サブレからバランスよく収集）。"""
    collected: list[dict[str, Any]] = []
    per_sub_limit = max(2, (max_total + len(SUBREDDITS) - 1) // len(SUBREDDITS))

    for sub in SUBREDDITS:
        if len(collected) >= max_total:
            break
        needed = min(per_sub_limit, max_total - len(collected))
        print(f"[INFO] r/{sub} から話題のスレッドを検索中...")

        url = f"https://www.reddit.com/r/{sub}/top.json?t=week&limit=25&raw_json=1"
        children: list[ Any ] = []
        try:
            listing = fetch_json(url)
            children = listing.get("data", {}).get("children", [])
        except Exception:
            pass

        if not children:
            print(f"[INFO] r/{sub} ミラーアーカイブ(Arctic Shift)からスレッドを検索中...")
            try:
                sub_items = _fetch_arctic_shift_threads(sub, existing_ids, needed)
                collected.extend(sub_items)
            except Exception as e2:
                print(f"[WARN] r/{sub} の取得に失敗しました: {e2}", file=sys.stderr)
            continue

        sub_count = 0
        for item in children:
            if sub_count >= needed or len(collected) >= max_total:
                break
            post = item.get("data", {})
            post_id = str(post.get("id") or "").strip()
            if not post_id or post_id in existing_ids:
                continue
            existing_ids.add(post_id)
            if not is_meaningful_thread(post):
                continue

            comment_tree = fetch_thread_comment_tree(sub, post_id, max_comments=32)
            if len(comment_tree) < 4:
                continue

            top_comments = [f"[+{c['score']}] {c['body_en'][:800]}" for c in comment_tree]
            collected.append({
                "id": post_id,
                "subreddit": sub,
                "op_author": "スレ主",
                "op_flair": str(post.get("author_flair_text") or "").strip(),
                "title_en": post.get("title", ""),
                "selftext_en": (post.get("selftext") or "")[:2500],
                "image_urls": _extract_post_image_urls(post),
                "score": int(post.get("score") or 0),
                "num_comments": int(post.get("num_comments") or 0),
                "permalink": f"https://www.reddit.com{post.get('permalink', '')}",
                "comments": top_comments[:32],
                "comment_tree": comment_tree,
            })
            sub_count += 1
            time.sleep(1.2)  # Redditへの負荷軽減マナー
    return collected


# ============================================================================
# 3. Gemini (gemini-3.8-flash) による集合知構造化＆デバイス抽出
# ============================================================================

SUMMARY_JSON_SCHEMA: dict[str, Any] = {
    "type": "object",
    "properties": {
        "title_ja": {
            "type": "string",
            "description": "ゲーマーが思わずクリックしたくなる日本語記事タイトル（40〜65文字程度）",
        },
        "hook_ja": {
            "type": "string",
            "description": "記事冒頭およびショート動画冒頭で3秒で惹きつける結論フック（1〜2文）",
        },
        "consensus_points": {
            "type": "array",
            "description": "コメント欄50人の集合知から導き出された主要結論（3〜5点）",
            "items": {"type": "string"},
        },
        "detailed_analysis_ja": {
            "type": "string",
            "description": "賛成派・反対派・持ち方やAIMスタイル別の詳しい解説（改行を含む400〜800文字）",
        },
        "dialogue": {
            "type": "array",
            "description": "5chまとめ風のテンポの良い海外ニキたちの掛け合い（4〜6発言）",
            "items": {
                "type": "object",
                "properties": {
                    "speaker": {"type": "string", "description": "例: スレ主 / 海外エイム猛者A / マウス沼ニキB"},
                    "text": {"type": "string", "description": "自然な日本語の口語コメント"},
                },
                "required": ["speaker", "text"],
            },
        },
        "devices": {
            "type": "array",
            "description": "スレッドおよびコメント内で言及・推奨・比較された具体的なマウス・マウスパッド・ソール製品名",
            "items": {
                "type": "object",
                "properties": {
                    "name": {"type": "string", "description": "正確な製品名（例: Razer Viper V3 Pro, Artisan 零 Soft, Wallhack SP-004）"},
                    "category": {"type": "string", "enum": ["mouse", "mousepad", "skates", "other"]},
                    "sentiment": {"type": "string", "enum": ["positive", "neutral", "negative"]},
                    "comment_ja": {"type": "string", "description": "その製品に対する海外ニキの評価要約（1〜2文）"},
                },
                "required": ["name", "category", "sentiment", "comment_ja"],
            },
        },
        "x_main_post": {
            "type": "string",
            "description": "X（旧Twitter）の本ツイート用テキスト。外部URLは含めず、結論箇条書きでブックマークしたくなる120〜135文字",
        },
        "x_reply_post": {
            "type": "string",
            "description": "Xのリプライ欄に繋げる記事誘導文（末尾に {{ARTICLE_URL}} プレースホルダーを含める）",
        },
        "short_script": {
            "type": "array",
            "description": "YouTube Shorts / TikTok用の45〜60秒の台本（8〜12行）",
            "items": {
                "type": "object",
                "properties": {
                    "speaker": {"type": "string", "enum": ["zundamon", "tsumugi"]},
                    "text": {"type": "string", "description": "読み上げセリフ（1文40文字以内）"},
                    "caption": {"type": "string", "description": "画面下部に表示する要約見出し（16文字以内）"},
                },
                "required": ["speaker", "text", "caption"],
            },
        },
    },
    "required": [
        "title_ja",
        "hook_ja",
        "consensus_points",
        "detailed_analysis_ja",
        "dialogue",
        "devices",
        "x_main_post",
        "x_reply_post",
        "short_script",
    ],
}


_CACHED_MODELS: list[str] | None = None


def get_available_flash_models(api_key: str) -> list[str]:
    """
    ユーザーのAPIキーで利用可能なFlash系モデル一覧を `/v1beta/models` から自動取得し、
    高速・低コストな順（gemini-3.5-flash-lite -> gemini-3.8-flash -> gemini-3.5-flash 等）に並べて返す。
    """
    global _CACHED_MODELS
    if _CACHED_MODELS is not None:
        return _CACHED_MODELS

    preferred_order = [
        "gemini-3.8-flash",
        "gemini-3.5-flash",
        "gemini-3.5-flash-lite",
        "gemini-3.1-flash-lite",
        "gemini-3-flash-preview",
        "gemini-2.5-flash",
        "gemini-2.5-flash-lite",
    ]
    available: list[str] = []
    try:
        url = f"https://generativelanguage.googleapis.com/v1beta/models?key={urllib.parse.quote(api_key)}"
        req = urllib.request.Request(url, headers={"Accept": "application/json"})
        with urllib.request.urlopen(req, timeout=15) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        for m in data.get("models", []):
            methods = m.get("supportedGenerationMethods") or []
            if "generateContent" not in methods:
                continue
            name = (m.get("name") or "").removeprefix("models/")
            # 音声・画像・埋め込み専用モデルを除外
            if any(x in name for x in ("tts", "image", "embedding", "transcribe", " omni", "live", "aqa", "bison")):
                continue
            if "flash" in name or "gemini" in name:
                available.append(name)
    except Exception as e:
        print(f"[WARN] モデル一覧の自動取得に失敗しました ({e})。既定のリストを使用します。", file=sys.stderr)

    if not available:
        _CACHED_MODELS = preferred_order
        return _CACHED_MODELS

    # preferred_order に含まれるものを最優先し、残りの flash モデルを後ろに繋げる
    ordered: list[str] = [p for p in preferred_order if p in available]
    for a in available:
        if a not in ordered and "flash" in a:
            ordered.append(a)
    for a in available:
        if a not in ordered:
            ordered.append(a)

    _CACHED_MODELS = ordered
    print(f"[INFO] 利用可能なGeminiモデルを検出しました（優先順）: {', '.join(ordered[:4])}")
    return _CACHED_MODELS


def summarize_with_gemini(thread: dict[str, Any]) -> dict[str, Any]:
    """
    Gemini 3.x (`gemini-3.5-flash-lite` / `gemini-3.8-flash`) を使ってRedditスレッドの
    スレ主本文と実在コメントツリーを1対1で忠実に全文翻訳し（水増し・捏造ゼロ）、
    深掘り解説・登場デバイス・ショート動画台本を生成する。
    """
    api_key = (os.environ.get("GEMINI_API_KEY") or "").strip()
    if not api_key:
        raise RuntimeError("環境変数 GEMINI_API_KEY が設定されていません。")

    # 実コメントツリーが未取得の場合はAPIから取得する
    comment_tree: list[dict[str, Any]] = list(thread.get("comment_tree") or [])
    if not comment_tree and thread.get("id") and thread.get("subreddit"):
        comment_tree = fetch_thread_comment_tree(str(thread["subreddit"]), str(thread["id"]), max_comments=30)

    # オフラインまたはフォールバック時のみ既存の comments 配列からノード化する
    if not comment_tree:
        for idx, raw_c in enumerate(thread.get("comments") or [], start=1):
            m = re.match(r"^\[([+-]?\d+)\]\s*(.*)$", str(raw_c), flags=re.DOTALL)
            sc = int(m.group(1)) if m else 1
            bd = m.group(2).strip() if m else str(raw_c).strip()
            comment_tree.append({
                "id": f"c{idx}",
                "parent_id": None,
                "depth": 0,
                "author": f"redditor_{idx}",
                "flair": "",
                "is_op": False,
                "score": sc,
                "body_en": bd,
            })

    target_tree = _anonymize_comment_tree(comment_tree[:30])
    comments_input_lines: list[str] = []
    for c in target_tree:
        op_mark = " (OP/スレ主)" if c.get("is_op") else ""
        parent_mark = f"reply_to={c['parent_id']}" if c.get("parent_id") else "top_level"
        comments_input_lines.append(
            f"[id={c['id']} | author={c['author']}{op_mark} | {parent_mark} | score={c['score']}]\n{c['body_en']}"
        )

    json_template = """{
  "title_ja": "スレッドの議題と結論が自然に伝わる日本語タイトル（36〜60文字、大げさな煽りや嘘は厳禁）",
  "hook_ja": "スレッドの核心と結論を端的に示すリード文（2文程度）",
  "op_post_ja": "スレ主（OP）の本文（selftext_en）の忠実な全文日本語訳（書かれていないことの捏造・脚色は厳禁、省略せず自然な口語で全訳）",
  "consensus_points": [
    "実際のコメント欄で合意・推奨されていた要点1",
    "要点2",
    "要点3"
  ],
  "detailed_analysis_ja": "スレッド内の実際の議論を踏まえた背景知識・用語解説・派閥別の補足ノート（800〜1400文字程度。【論点1：〜】のような小見出しを含める）",
  "comment_translations": [
    {"id": "入力された実在コメントのid文字列", "body_ja": "そのコメント原文の忠実かつ自然な全文日本語訳（省略・要約せず、原文の内容のみを正確に翻訳）"}
  ],
  "devices": [
    {
      "name": "日本のAmazon・楽天で検索しやすい正式製品名（例: Logicool G PRO X SUPERLIGHT 2, Razer Viper V3 Pro, ARTISAN 零 Soft, Wallhack SP-004, X-raypad Jade Skates）",
      "category": "mouse または mousepad または skates",
      "sentiment": "positive または neutral または negative",
      "comment_ja": "その製品がどう評価・言及されたかの要約（1〜2文。『スレ主が〜』『OPが〜』といった主語は使わず、製品の特徴やユーザーからの評価として記述すること）"
    }
  ],
  "x_main_post": "Xの本ツイート用テキスト（外部URLは含めず、結論箇条書きで120〜135文字）",
  "x_reply_post": "スレッド全文＆登場デバイス一覧はこちら\\n{{ARTICLE_URL}}",
  "short_script": [
    {"speaker": "zundamon", "text": "導入の疑問・悩み（「〜なのだ！」「〜のだ？」口調、35文字以内）", "caption": "要約テロップ（16文字以内）"},
    {"speaker": "tsumugi", "text": "海外猛者の結論提示（明るく親しみやすいギャル風「〜だよ！」「〜なんだよね」口調）", "caption": "海外猛者の結論"},
    {"speaker": "zundamon", "text": "リアクションや理由の深掘り（「〜なのだ？」）", "caption": "なぜそうなる？"},
    {"speaker": "tsumugi", "text": "理由1の解説（「〜だからなんだよね」）", "caption": "ポイント①"},
    {"speaker": "tsumugi", "text": "理由2や具体的デバイス・対策の解説（「〜がおすすめされてるよ！」）", "caption": "ポイント②"},
    {"speaker": "zundamon", "text": "納得のリアクション（「〜なのだ！」）", "caption": "目からウロコ！"},
    {"speaker": "tsumugi", "text": "注意点や補足（「ただ〜には気をつけてね！」）", "caption": "注意点"},
    {"speaker": "zundamon", "text": "締めの一言（「みんなも試してみてほしいのだ！」）", "caption": "詳細はプロフ・概要欄へ"}
  ]
}"""

    prompt = (
        "あなたはFPSの競技エイム（KovaaK's / Aimlabs / Voltaic）およびゲーミングマウス・マウスパッドに精通した専門翻訳者・キュレーターです。\n"
        "以下の海外Redditスレッドの本文と【実在コメント一覧】を分析し、正確な全文翻訳と解説を作成してください。\n"
        "【絶対厳守ルール】:\n"
        "1. **嘘・創作・水増しの完全禁止**: スレッドに実在しないコメントや発言を勝手に作ったり、原文にない内容を付け足したりすることは絶対に行わないでください。\n"
        "2. **1対1の忠実な全文翻訳**: `op_post_ja` にはスレ主の本文を省略せず全文翻訳してください。`comment_translations` には、入力された【実在コメント一覧】のすべての `id` に対して1対1で、省略・要約せず自然な日本語の全文翻訳（`body_ja`）を返してください。親コメントへの返信（`reply_to=...`）は文脈を踏まえて自然な口語で訳してください。\n"
        "3. `devices` にはスレッド内で実際に言及された市販のマウス (`mouse`)・マウスパッド (`mousepad`)・ソール (`skates`) のみを抽出し、国内名称（`Logitech` → `Logicool`、`Artisan Raiden` → `ARTISAN 雷電`、`Artisan Zero` → `ARTISAN 零`）に統一してください。また `comment_ja` には『スレ主が〜』『OPが〜』という主語は入れず、製品への評価として記述してください。\n"
        "4. `short_script` は必ず8発言以上で、`zundamon`（ずんだもん：「〜なのだ！」）と `tsumugi`（春日部つむぎ：埼玉ギャル風「〜だよ！」「〜なんだよね」）の2人で構成してください。\n"
        "出力は必ず以下のJSON形式（キー名を完全一致）のみを返してください。\n\n"
        f"【出力JSON形式】:\n{json_template}\n\n"
        f"【サブレディット】: r/{thread['subreddit']}\n"
        f"【英語タイトル】: {thread['title_en']}\n"
        f"【スレ主の本文 (OP)】:\n{thread['selftext_en']}\n\n"
        f"【実在コメント一覧 (全{len(target_tree)}件)】:\n" + "\n---\n".join(comments_input_lines)
    )

    models_to_try = get_available_flash_models(api_key)
    last_err: Exception | None = None

    for model_name in models_to_try[:5]:
        gen_cfg: dict[str, Any] = {"responseMimeType": "application/json"}
        if model_name.startswith("gemini-3.8") or model_name.startswith("gemini-3.7"):
            gen_cfg["thinkingConfig"] = {"thinkingLevel": "low"}
        elif model_name.startswith("gemini-3.5-flash") and "lite" not in model_name:
            gen_cfg["thinkingConfig"] = {"thinkingLevel": "minimal"}

        fb_url = (
            f"https://generativelanguage.googleapis.com/v1beta/models/{model_name}:generateContent"
            f"?key={urllib.parse.quote(api_key)}"
        )
        fb_payload = {
            "contents": [{"parts": [{"text": prompt}]}],
            "generationConfig": gen_cfg,
        }
        try:
            req_fb = urllib.request.Request(
                fb_url,
                data=json.dumps(fb_payload).encode("utf-8"),
                headers={"Content-Type": "application/json"},
                method="POST",
            )
            with urllib.request.urlopen(req_fb, timeout=150) as resp_fb:
                fb_data = json.loads(resp_fb.read().decode("utf-8"))

            parts = fb_data.get("candidates", [{}])[0].get("content", {}).get("parts", [])
            text_out = ""
            for p in parts:
                if not p.get("thought") and p.get("text"):
                    text_out = p["text"].strip()
            if not text_out and parts:
                text_out = (parts[-1].get("text") or "").strip()

            if text_out.startswith("```"):
                text_out = text_out.strip("`").removeprefix("json").strip()
            parsed = json.loads(text_out)
            if isinstance(parsed, dict) and parsed.get("title_ja"):
                # 翻訳結果を実コメントツリーへ1対1でマージ（水増しゼロ保証）
                trans_list = parsed.get("comment_translations") or []
                trans_map: dict[str, str] = {}
                if isinstance(trans_list, list):
                    for item in trans_list:
                        if isinstance(item, dict) and item.get("id") and item.get("body_ja"):
                            trans_map[str(item["id"]).strip()] = str(item["body_ja"]).strip()

                enriched_tree: list[dict[str, Any]] = []
                dialogue_mirror: list[dict[str, Any]] = []
                for c in target_tree:
                    cid = str(c["id"]).strip()
                    ja_text = trans_map.get(cid) or str(c.get("body_ja") or "").strip() or str(c["body_en"]).strip()
                    node_copy = {
                        **c,
                        "body_ja": ja_text,
                    }
                    enriched_tree.append(node_copy)
                    speaker_label = str(c["author"])
                    dialogue_mirror.append({
                        "id": cid,
                        "parent_id": c.get("parent_id"),
                        "depth": c.get("depth", 0),
                        "speaker": speaker_label,
                        "flair": c.get("flair", ""),
                        "is_op": bool(c.get("is_op")),
                        "score": int(c.get("score", 1)),
                        "text": ja_text,
                    })

                if isinstance(parsed.get("devices"), list):
                    for d_obj in parsed["devices"]:
                        if isinstance(d_obj, dict) and d_obj.get("comment_ja"):
                            d_obj["comment_ja"] = _clean_device_comment_ja(str(d_obj["comment_ja"]))

                parsed["comment_tree"] = enriched_tree
                parsed["dialogue"] = dialogue_mirror
                parsed.pop("comment_translations", None)
                return parsed
        except Exception as e:
            last_err = e
            continue

    raise RuntimeError(f"Gemini API呼び出し失敗: {last_err}")


# ============================================================================
# 4. X (旧Twitter) ワンクリックIntent URL生成 ＆ OAuth 1.0a ツリー自動連投
# ============================================================================

def build_x_intent_url(main_post: str, article_url: str) -> str:
    """スプレッドシートから1クリックでXの投稿画面を開くIntent URLを生成する。"""
    text = f"{main_post}\n\n詳細・登場デバイスまとめ👇\n{article_url}"
    return f"https://twitter.com/intent/tweet?text={urllib.parse.quote(text)}"


def _oauth1_header(
    method: str,
    url: str,
    consumer_key: str,
    consumer_secret: str,
    token: str,
    token_secret: str,
) -> str:
    """外部ライブラリ不要の標準ライブラリOAuth 1.0a署名ヘッダ生成。"""
    oauth_params = {
        "oauth_consumer_key": consumer_key,
        "oauth_nonce": secrets.token_hex(16),
        "oauth_signature_method": "HMAC-SHA1",
        "oauth_timestamp": str(int(time.time())),
        "oauth_token": token,
        "oauth_version": "1.0",
    }
    param_str = "&".join(
        f"{urllib.parse.quote(k, safe='')}={urllib.parse.quote(v, safe='')}"
        for k, v in sorted(oauth_params.items())
    )
    base_str = "&".join([
        method.upper(),
        urllib.parse.quote(url, safe=""),
        urllib.parse.quote(param_str, safe=""),
    ])
    signing_key = f"{urllib.parse.quote(consumer_secret, safe='')}&{urllib.parse.quote(token_secret, safe='')}"
    signature = base64.b64encode(
        hmac.new(signing_key.encode("utf-8"), base_str.encode("utf-8"), hashlib.sha1).digest()
    ).decode("utf-8")
    oauth_params["oauth_signature"] = signature
    header_parts = ", ".join(
        f'{urllib.parse.quote(k, safe="")}="{urllib.parse.quote(v, safe="")}"'
        for k, v in sorted(oauth_params.items())
    )
    return f"OAuth {header_parts}"


def post_tree_to_x(main_text: str, reply_text: str) -> str | None:
    """
    X Free API v2 を用いて、
    1. 本ツイート（外部リンクなし・拡散重視）
    2. セルフリプライ（記事URL・アフィリエイト誘導）
    をツリー連投する。APIキー未設定ならスキップして None を返す。
    """
    ck = (os.environ.get("X_API_KEY") or "").strip()
    cs = (os.environ.get("X_API_SECRET") or "").strip()
    at = (os.environ.get("X_ACCESS_TOKEN") or "").strip()
    ats = (os.environ.get("X_ACCESS_SECRET") or "").strip()
    if not (ck and cs and at and ats):
        return None

    endpoint = "https://api.twitter.com/2/tweets"

    def _send_tweet(body: dict[str, Any]) -> str:
        auth = _oauth1_header("POST", endpoint, ck, cs, at, ats)
        req = urllib.request.Request(
            endpoint,
            data=json.dumps(body).encode("utf-8"),
            headers={"Authorization": auth, "Content-Type": "application/json"},
            method="POST",
        )
        try:
            with urllib.request.urlopen(req, timeout=20) as resp:
                res_json = json.loads(resp.read().decode("utf-8"))
                return str(res_json["data"]["id"])
        except urllib.error.HTTPError as e:
            err_body = ""
            try:
                err_body = e.read().decode("utf-8", errors="replace")
            except Exception:
                pass
            raise RuntimeError(f"X API HTTP {e.code}: {err_body}") from e

    main_id = _send_tweet({"text": main_text})
    time.sleep(2)
    reply_id = _send_tweet({"text": reply_text, "reply": {"in_reply_to_tweet_id": main_id}})
    print(f"[OK] Xツリー投稿完了 (main_id={main_id}, reply_id={reply_id})")
    return main_id


def publish_pending_to_x(articles: list[dict[str, Any]]) -> bool:
    """
    公開済み (status == 'published') かつ X未投稿の記事をツリー投稿し、更新有無を返す。
    ※X APIの従量課金（402 credits depleted）回避のため、既定ではAPI自動投稿を行わず、
      環境変数 X_AUTO_POST=true が明示設定されている場合のみAPIを叩く。
    """
    if (os.environ.get("X_AUTO_POST") or "").strip().lower() not in ("1", "true", "yes", "on"):
        return False

    updated = False
    for art in articles:
        if art.get("status") == "published" and not art.get("x_posted"):
            aid = str(art.get("id") or "")
            title = str(art.get("title_ja") or "")[:40]
            print(f"[INFO] Xへツリー投稿中: [{aid}] {title}...")
            reply_text = str(art.get("x_reply_post", "")).replace("{{ARTICLE_URL}}", art.get("article_url", ""))
            try:
                tweet_id = post_tree_to_x(str(art.get("x_main_post", "")), reply_text)
                if tweet_id:
                    art["x_posted"] = True
                    art["x_tweet_id"] = tweet_id
                    updated = True
                else:
                    print("[WARN] X APIキーが未設定のためX投稿をスキップしました。")
            except Exception as e:
                print(f"[WARN] Xツリー投稿失敗 ({aid}): {e}", file=sys.stderr)
    return updated


# ============================================================================
# 5. Googleスプレッドシート (GAS Webhook) ＆ ローカルデータ同期
# ============================================================================

def load_articles(path: Path = ARTICLES_FILE) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    return json.loads(path.read_text(encoding="utf-8"))


def save_articles(articles: list[dict[str, Any]], path: Path = ARTICLES_FILE) -> None:
    """記事データを保存する（万が一同一スレッドIDが重複していた場合は最新を残して重複排除）。"""
    deduped: list[dict[str, Any]] = []
    seen_ids: set[str] = set()
    for a in articles:
        aid = str(a.get("id") or "").strip()
        if aid and aid in seen_ids:
            continue
        if aid:
            seen_ids.add(aid)
        deduped.append(a)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(deduped, ensure_ascii=False, indent=2), encoding="utf-8")


def sync_with_google_sheets(articles: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """
    環境変数 GAS_WEBHOOK_URL が設定されている場合、Googleスプレッドシートと双方向同期する。
    - スプレッドシート側で人間が `status` を `published`（公開）や `rejected`（却下）に変更した状態を反映
    - スプレッドシート側で微修正された `title_ja` / `hook_ja` を反映
    - 新しく生成した下書き（`draft`）行をスプレッドシートへ追加（50,000文字制限回避のため軽量データのみ送信）
    """
    webhook_url = (os.environ.get("GAS_WEBHOOK_URL") or "").strip()
    if not webhook_url:
        return articles

    light_payload = [
        {
            "id": str(a.get("id") or ""),
            "status": a.get("status") or "draft",
            "subreddit": a.get("subreddit") or "",
            "title_ja": a.get("title_ja") or "",
            "hook_ja": a.get("hook_ja") or "",
            "x_intent_url": a.get("x_intent_url") or "",
            "article_url": a.get("article_url") or "",
            "devices": [{"name": d.get("name")} for d in (a.get("devices") or []) if isinstance(d, dict)],
            "created_at": a.get("created_at") or "",
        }
        for a in articles
        if a.get("id")
    ]

    try:
        req = urllib.request.Request(
            webhook_url,
            data=json.dumps({"action": "sync", "articles": light_payload}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
            method="POST",
        )
        with urllib.request.urlopen(req, timeout=30) as resp:
            res = json.loads(resp.read().decode("utf-8"))
            sheet_items = res.get("articles")
            if isinstance(sheet_items, list):
                sheet_map = {
                    str(item.get("id")): item
                    for item in sheet_items
                    if isinstance(item, dict) and item.get("id")
                }
                for art in articles:
                    aid = str(art.get("id") or "")
                    if aid in sheet_map:
                        s_item = sheet_map[aid]
                        if s_item.get("status"):
                            art["status"] = str(s_item["status"]).strip()
                        if s_item.get("title_ja"):
                            art["title_ja"] = str(s_item["title_ja"]).strip()
                        if s_item.get("hook_ja"):
                            art["hook_ja"] = str(s_item["hook_ja"]).strip()
                print(f"[OK] Googleスプレッドシートと同期完了 ({len(sheet_map)}件)")
    except Exception as e:
        print(f"[WARN] Googleスプレッドシート同期エラー: {e}", file=sys.stderr)
    return articles


# ============================================================================
# 6. 海外Reddit話題度ランキング集計 ＆ 特化型Webサイト(静的HTML)生成
# ============================================================================

def aggregate_device_ranking(
    articles: list[dict[str, Any]],
    master: dict[str, dict[str, str]] | None = None,
    env: dict[str, str] | None = None,
) -> list[dict[str, Any]]:
    """
    対象記事で言及された市販デバイス（mouse / mousepad / skates）を自動集計し、
    「ポジティブ評価が1件以上あるもの」または「複数回話題に上がった定番機（ネガティブ単独は除外）」のみを
    高評価数×言及回数順のランキングとして返す。
    """
    stats: dict[str, dict[str, Any]] = {}
    for art in articles:
        for dev in art.get("devices", []):
            cat = (dev.get("category") or "other").strip().lower()
            if cat not in ("mouse", "mousepad", "skates"):
                continue
            raw_name = normalize_product_name_jp(dev.get("name") or "")
            if not raw_name or "modkit" in raw_name.lower():
                continue
            key = raw_name.lower()
            if key not in stats:
                links = build_affiliate_urls(raw_name, master, env)
                stats[key] = {
                    "name": raw_name,
                    "category": cat,
                    "mentions": 0,
                    "positive": 0,
                    "negative": 0,
                    "comments": [],
                    "amazon_url": links["amazon_url"],
                    "rakuten_url": links["rakuten_url"],
                }
            entry = stats[key]
            entry["mentions"] += 1
            sentiment = dev.get("sentiment")
            if sentiment == "positive":
                entry["positive"] += 1
            elif sentiment == "negative":
                entry["negative"] += 1
            comment = _clean_device_comment_ja(dev.get("comment_ja") or "")
            if comment and comment not in entry["comments"]:
                if sentiment == "positive":
                    entry["comments"].insert(0, comment)
                elif len(entry["comments"]) < 2:
                    entry["comments"].append(comment)
            entry["comments"] = entry["comments"][:2]

    # ネガティブ評価のみのデバイスはおすすめランキングから除外
    filtered = [
        item for item in stats.values()
        if item["positive"] > 0 or (item["mentions"] >= 2 and item["negative"] == 0)
    ]
    ranked = sorted(
        filtered,
        key=lambda x: (x["positive"], x["mentions"]),
        reverse=True,
    )
    return ranked


def _clean_device_comment_ja(text: str) -> str:
    """デバイス評価コメントから『スレ主』等の不要な主語やノイズを自然な日本語へ整形する。"""
    s = text.strip().replace("souris", "マウス")
    s = re.sub(r"^ているマウス[。、]\s*", "", s)
    s = re.sub(r"^気に入っていた(?:マウスの一つ|軽量マウス)[。、]\s*", "定番の軽量マウスとして好評。", s)
    s = re.sub(r"スレ主[がはも]", "ユーザーが", s)
    s = re.sub(r"スレ主の", "ユーザーの", s)
    return s.strip()


CATEGORY_LABELS = {
    "mouse": "マウス",
    "mousepad": "マウスパッド",
    "skates": "ソール",
    "other": "周辺機器",
}

SENTIMENT_BADGES = {
    "positive": ("status-pos", "高評価"),
    "neutral": ("status-neu", "比較・言及"),
    "negative": ("status-neg", "注意点あり"),
}

SUBREDDIT_LABELS = {
    "FPSAimTrainer": "AIM練習・理論",
    "MouseReview": "マウス",
    "MousepadReview": "マウスパッド・ソール",
}


def _format_res_body_html(text: str) -> str:
    """コメント本文をHTMLエスケープし、改行や引用行（>）を整える。"""
    cleaned = re.sub(r"^(?:0*1|１)\s*(?:名前[:：][^\n]+|[：:][^\n]+)\n+", "", text.strip())
    lines = cleaned.splitlines()
    out_lines: list[str] = []
    for ln in lines:
        s = ln.strip()
        if s.startswith(">") and not s.startswith(">>"):
            q_text = html.escape(s.lstrip(">").strip())
            out_lines.append(f'<blockquote class="rc-quote">{q_text}</blockquote>')
        else:
            out_lines.append(html.escape(ln))
    return "<br>".join(out_lines).replace("</blockquote><br>", "</blockquote>")


def _build_reddit_tree_html(art: dict[str, Any]) -> tuple[str, int]:
    """
    記事データの実コメントツリー (`comment_tree`) から、匿名化されたReddit風階層返信ツリーHTMLを生成する。
    戻り値は (HTML文字列, 実コメント数)。
    """
    raw_tree = list(art.get("comment_tree") or [])
    if not raw_tree:
        # セルフテスト等のレガシー形式フォールバック
        for idx, d in enumerate(art.get("dialogue") or [], start=1):
            sp = str(d.get("speaker") or f"海外ユーザー{idx}").removeprefix("u/")
            is_op_flag = bool(d.get("is_op")) or ("スレ主" in sp) or ("(OP)" in sp)
            sp_clean = sp.replace("(OP)", "").strip()
            raw_tree.append({
                "id": str(d.get("id") or f"c{idx}"),
                "parent_id": d.get("parent_id"),
                "depth": int(d.get("depth") or 0),
                "author": sp_clean,
                "flair": str(d.get("flair") or ""),
                "is_op": is_op_flag,
                "score": int(d.get("score") if d.get("score") is not None else 5),
                "body_ja": str(d.get("text") or ""),
            })

    raw_tree = _anonymize_comment_tree(raw_tree)
    known_ids = {str(c.get("id")) for c in raw_tree if c.get("id")}
    author_by_id = {str(c.get("id")): str(c.get("author") or "海外ユーザー") for c in raw_tree if c.get("id")}
    children_map: dict[str | None, list[dict[str, Any]]] = {None: []}

    for c in raw_tree:
        pid = c.get("parent_id")
        pid_str = str(pid) if pid and str(pid) in known_ids else None
        children_map.setdefault(pid_str, []).append(c)

    def _render_node(node: dict[str, Any]) -> str:
        cid = html.escape(str(node.get("id") or ""))
        author_raw = str(node.get("author") or "海外ユーザー").strip()
        author_esc = html.escape(author_raw)
        flair_raw = str(node.get("flair") or "").strip()
        flair_html = f'<span class="rc-flair">{html.escape(flair_raw)}</span>' if flair_raw else ""
        is_op = bool(node.get("is_op"))
        op_html = '<span class="rc-badge-op">OP</span>' if is_op else ""

        pid = node.get("parent_id")
        pid_str = str(pid) if pid and str(pid) in known_ids else None
        reply_to_html = ""
        if pid_str:
            p_author = html.escape(author_by_id.get(pid_str, ""))
            if p_author:
                reply_to_html = f'<span class="rc-reply-to">↳ {p_author} への返信</span>'

        score_val = int(node.get("score") if node.get("score") is not None else 1)
        score_str = f"{score_val:+d} pts" if score_val != 0 else "0 pts"
        score_cls = "rc-score rc-score-high" if score_val >= 15 else "rc-score"

        body_text = str(node.get("body_ja") or node.get("body_en") or "").strip()
        body_html = _format_res_body_html(body_text)

        child_nodes = children_map.get(str(node.get("id")), [])
        if child_nodes:
            inner_children = "\n".join(_render_node(ch) for ch in child_nodes)
            children_block = f'<div class="rc-children">\n{inner_children}\n</div>'
        else:
            children_block = ""

        return (
            f'<div class="rc-node" id="c-{cid}">'
            f'<div class="rc-comment">'
            f'<div class="rc-head">'
            f'<span class="rc-author">{author_esc}</span>'
            f'{op_html}'
            f'{flair_html}'
            f'{reply_to_html}'
            f'<span class="{score_cls}">{score_str}</span>'
            f'</div>'
            f'<div class="rc-body">{body_html}</div>'
            f'</div>'
            f'{children_block}'
            f'</div>'
        )

    roots = children_map.get(None, [])
    tree_html = '<div class="rc-tree">\n' + "\n".join(_render_node(r) for r in roots) + "\n</div>"
    return tree_html, len(raw_tree)


def _format_analysis_html(raw_text: str) -> str:
    """深掘り解説テキストの【見出し】をセクション小見出しに変換し、段落ごとに組む。"""
    if not raw_text.strip():
        return ""
    blocks: list[str] = []
    for line in raw_text.splitlines():
        s = line.strip()
        if not s:
            continue
        m = re.match(r"^【(.+?)】(.*)$", s)
        if m:
            head_title = html.escape(m.group(1).strip())
            rest = html.escape(m.group(2).strip())
            blocks.append(f'<h3 class="analysis-subhead">{head_title}</h3>')
            if rest:
                blocks.append(f'<p class="analysis-para">{rest}</p>')
        else:
            blocks.append(f'<p class="analysis-para">{html.escape(s)}</p>')
    return "\n".join(blocks)


def _compute_thread_metrics(art: dict[str, Any]) -> tuple[int, int, int]:
    """記事の実コメント数・総文字数・読了目安（分）を実データから正確に算出する。"""
    tree = art.get("comment_tree") or []
    dialogues = art.get("dialogue") or []
    op_ja = (art.get("op_post_ja") or "").strip()
    comment_count = len(tree) if tree else len(dialogues)
    body_chars = (
        sum(len(str(c.get("body_ja") or "")) for c in tree)
        if tree
        else sum(len(str(d.get("text") or "")) for d in dialogues)
    )
    char_count = (
        len(art.get("title_ja") or "")
        + len(art.get("hook_ja") or "")
        + len(op_ja)
        + sum(len(str(p)) for p in (art.get("consensus_points") or []))
        + body_chars
        + len(art.get("detailed_analysis_ja") or "")
    )
    read_min = max(2, round(char_count / 550))
    return comment_count, char_count, read_min


def build_site(
    articles: list[dict[str, Any]],
    out_dir: Path = DIST_DIR,
    master: dict[str, dict[str, str]] | None = None,
    env: dict[str, str] | None = None,
) -> None:
    """
    公開承認済み (status == 'published') の記事（未公開時はdraftプレビュー）と話題度ランキングから、
    掲示板ログ・テキスト特化型の静的Webサイト（『エイム沼の海外ログ』）を生成する。
    """
    articles_dir = out_dir / "articles"
    articles_dir.mkdir(parents=True, exist_ok=True)
    published = [a for a in articles if a.get("status") == "published"]
    if not published and articles:
        published = list(articles)
    published.sort(key=lambda a: a.get("created_at", ""), reverse=True)
    published_ids = {f"{a.get('id')}.html" for a in published if a.get("id")}
    for old_html in articles_dir.glob("*.html"):
        if old_html.name not in published_ids:
            old_html.unlink(missing_ok=True)
    ranking = aggregate_device_ranking(published, master, env)
    updated_date = dt.datetime.now().strftime("%Y.%m.%d")

    cfg = env if env is not None else os.environ
    x_account_raw = (cfg.get("X_ACCOUNT_ID") or "").strip().lstrip("@")
    if x_account_raw:
        x_handle_disp = f"@{html.escape(x_account_raw)}"
        x_profile_url = html.escape(f"https://x.com/{urllib.parse.quote(x_account_raw)}")
        x_sidebar_html = (
            f'<section class="x-account-section">'
            f'<div class="section-header"><h2 class="section-title">X (Twitter)</h2></div>'
            f'<div class="x-account-box">'
            f'<a class="x-account-link" href="{x_profile_url}" target="_blank" rel="noopener">{x_handle_disp} ↗</a>'
            f'</div>'
            f'</section>'
        )
        x_footer_html = f'<div>X: <a href="{x_profile_url}" target="_blank" rel="noopener">{x_handle_disp}</a></div>'
    else:
        x_sidebar_html = (
            '<section class="x-account-section">'
            '<div class="section-header"><h2 class="section-title">X (Twitter)</h2></div>'
            '<div class="x-account-box">'
            '<span class="x-account-unset">.env の X_ACCOUNT_ID を設定すると表示されます</span>'
            '</div>'
            '</section>'
        )
        x_footer_html = '<div>X: <span class="x-account-unset">.env の X_ACCOUNT_ID で設定</span></div>'

    font_links = (
        '<link rel="preconnect" href="https://fonts.googleapis.com">\n'
        '  <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>\n'
        '  <link href="https://fonts.googleapis.com/css2?family=BIZ+UDPGothic:wght@400;700&family=JetBrains+Mono:wght@400;600;700&family=Shippori+Mincho+B1:wght@600;700;800&display=swap" rel="stylesheet">'
    )

    css = """/* Hallmark · pre-emit critique: P5 H5 E5 S5 R5 V5 */
/* Hallmark · genre: editorial · macrostructure: Index-First / Long Document · theme: Almanac · enrichment: none · nav: N6 · footer: Ft4 */
:root {
  --color-paper: oklch(96.8% 0.012 85);
  --color-paper-2: oklch(93.8% 0.016 82);
  --color-paper-3: oklch(90.2% 0.020 80);
  --color-ink: oklch(19.5% 0.015 65);
  --color-ink-2: oklch(34.0% 0.018 65);
  --color-ink-muted: oklch(46.0% 0.018 65);
  --color-ink-faint: oklch(60.0% 0.015 65);
  --color-rule: oklch(86.5% 0.012 75);
  --color-rule-strong: oklch(74.0% 0.015 70);
  --color-accent: oklch(47.0% 0.175 30);
  --color-accent-hover: oklch(39.0% 0.175 30);
  --color-accent-soft: oklch(92.5% 0.038 35);
  --color-op-badge: oklch(32.0% 0.085 245);
  --color-op-bg: oklch(94.8% 0.014 85);
  --color-pos: oklch(40.0% 0.115 155);
  --color-pos-bg: oklch(92.8% 0.035 155);
  --color-neu: oklch(40.0% 0.020 65);
  --color-neu-bg: oklch(91.5% 0.015 80);
  --color-neg: oklch(45.0% 0.160 25);
  --color-neg-bg: oklch(93.0% 0.035 25);
  --color-amzn-bg: oklch(22.0% 0.018 65);
  --color-amzn-fg: oklch(97.0% 0.010 85);
  --color-rktn-bg: oklch(44.0% 0.160 28);
  --color-rktn-fg: oklch(97.5% 0.008 85);
  --font-display: 'Shippori Mincho B1', 'Hiragino Mincho ProN', 'Yu Mincho', serif;
  --font-sans: 'BIZ UDPGothic', 'Hiragino Kaku Gothic ProN', 'Meiryo', sans-serif;
  --font-mono: 'JetBrains Mono', 'Consolas', monospace;
  --space-xs: 0.25rem;
  --space-sm: 0.5rem;
  --space-md: 1rem;
  --space-lg: 1.5rem;
  --space-xl: 2.5rem;
  --space-2xl: 3.5rem;
  --ease-out: cubic-bezier(0.16, 1, 0.3, 1);
  --dur-short: 140ms;
}
*, *::before, *::after { box-sizing: border-box; }
html, body {
  margin: 0;
  padding: 0;
  overflow-x: clip;
  background-color: var(--color-paper);
  color: var(--color-ink);
  font-family: var(--font-sans);
  font-size: 16px;
  line-height: 1.8;
  -webkit-font-smoothing: antialiased;
}
h1, h2, h3, h4 {
  font-family: var(--font-display);
  font-style: normal;
  font-weight: 700;
  color: var(--color-ink);
  overflow-wrap: anywhere;
  min-width: 0;
  margin-top: 0;
}
a {
  color: var(--color-ink);
  text-decoration: underline;
  text-decoration-color: var(--color-rule-strong);
  text-underline-offset: 3px;
  transition: color var(--dur-short) var(--ease-out), text-decoration-color var(--dur-short) var(--ease-out);
}
a:hover {
  color: var(--color-accent);
  text-decoration-color: var(--color-accent);
}
a:focus-visible, button:focus-visible {
  outline: 2px solid var(--color-accent);
  outline-offset: 2px;
}

/* N6 Newspaper Masthead */
.masthead {
  border-bottom: 3px double var(--color-rule-strong);
  background-color: var(--color-paper);
}
.masthead-meta {
  max-width: 1200px;
  margin: 0 auto;
  padding: 0.45rem var(--space-lg);
  display: flex;
  flex-wrap: wrap;
  justify-content: space-between;
  align-items: center;
  gap: var(--space-sm);
  border-bottom: 1px solid var(--color-rule);
  font-family: var(--font-mono);
  font-size: 0.75rem;
  color: var(--color-ink-muted);
  font-variant-numeric: tabular-nums;
}
.masthead-Core {
  max-width: 1200px;
  margin: 0 auto;
  padding: var(--space-lg) var(--space-lg) var(--space-md);
  display: flex;
  flex-wrap: wrap;
  justify-content: space-between;
  align-items: baseline;
  gap: var(--space-md);
}
.site-title {
  font-family: var(--font-display);
  font-size: clamp(1.75rem, 3.4vw, 2.5rem);
  font-weight: 800;
  letter-spacing: -0.02em;
  line-height: 1.15;
  margin: 0;
}
.site-title a {
  text-decoration: none;
  color: var(--color-ink);
}
.site-title a:hover {
  color: var(--color-accent);
}
.site-tagline {
  margin: 0.35rem 0 0;
  font-size: 0.88rem;
  color: var(--color-ink-2);
}
.masthead-Compact {
  max-width: 1200px;
  margin: 0 auto;
  padding: 0.85rem var(--space-lg);
  display: flex;
  flex-wrap: wrap;
  justify-content: space-between;
  align-items: center;
  gap: var(--space-sm);
}
.masthead-Compact-brand {
  font-family: var(--font-display);
  font-size: 1.25rem;
  font-weight: 800;
  text-decoration: none;
}
.back-index-link {
  font-family: var(--font-mono);
  font-size: 0.82rem;
  white-space: nowrap;
  text-decoration: none;
  padding: 0.3rem 0.65rem;
  border: 1px solid var(--color-rule-strong);
  background-color: var(--color-paper-2);
}
.back-index-link:hover {
  background-color: var(--color-ink);
  color: var(--color-paper);
}

/* Filter Strip (Sharp Tabular Bar) */
.filter-strip-wrap {
  border-top: 1px solid var(--color-rule);
  background-color: var(--color-paper-2);
}
.filter-strip {
  max-width: 1200px;
  margin: 0 auto;
  padding: 0 var(--space-lg);
  display: flex;
  flex-wrap: wrap;
  gap: 0;
}
.filter-tab {
  appearance: none;
  background: transparent;
  border: none;
  border-right: 1px solid var(--color-rule);
  border-bottom: 2px solid transparent;
  padding: 0.65rem 1.1rem;
  font-family: var(--font-sans);
  font-size: 0.84rem;
  font-weight: 700;
  color: var(--color-ink-2);
  cursor: pointer;
  white-space: nowrap;
  transition: background-color var(--dur-short) var(--ease-out), color var(--dur-short) var(--ease-out);
}
.filter-tab:first-child {
  border-left: 1px solid var(--color-rule);
}
.filter-tab:hover {
  background-color: var(--color-paper-3);
  color: var(--color-ink);
}
.filter-tab.active {
  background-color: var(--color-paper);
  color: var(--color-accent);
  border-bottom-color: var(--color-accent);
}

/* Main Grid Layout */
.page-wrap {
  max-width: 1200px;
  margin: 0 auto;
  padding: var(--space-xl) var(--space-lg);
}
.index-grid {
  display: grid;
  grid-template-columns: minmax(0, 1fr) 360px;
  gap: var(--space-2xl);
  align-items: start;
}
@media (max-width: 960px) {
  .index-grid {
    grid-template-columns: minmax(0, 1fr);
    gap: var(--space-xl);
  }
}
.article-grid {
  display: grid;
  grid-template-columns: minmax(0, 1fr) 360px;
  gap: var(--space-2xl);
  align-items: start;
}
@media (max-width: 1080px) {
  .article-grid {
    grid-template-columns: minmax(0, 1fr);
    gap: var(--space-xl);
  }
}

.section-header {
  border-bottom: 1px solid var(--color-rule-strong);
  padding-bottom: 0.55rem;
  margin-bottom: 0;
  display: flex;
  flex-wrap: wrap;
  justify-content: space-between;
  align-items: center;
  gap: var(--space-sm);
}
.section-title {
  font-size: 1.2rem;
  line-height: 1.35;
  letter-spacing: 0.01em;
  margin: 0;
}
.section-sub {
  font-family: var(--font-mono);
  font-size: 0.75rem;
  color: var(--color-ink-muted);
  font-variant-numeric: tabular-nums;
}

/* Index Thread Rows (No Rounded Cards) */
.thread-index-row {
  padding: var(--space-lg) 0;
  border-bottom: 1px solid var(--color-rule);
}
.thread-meta-bar {
  font-family: var(--font-mono);
  font-size: 0.76rem;
  color: var(--color-ink-muted);
  font-variant-numeric: tabular-nums;
  display: flex;
  flex-wrap: wrap;
  align-items: center;
  gap: 0.65rem;
  margin-bottom: 0.4rem;
}
.sub-tag {
  font-family: var(--font-mono);
  font-weight: 700;
  color: var(--color-accent);
  letter-spacing: 0.02em;
  text-decoration: none;
}
a.sub-tag:hover {
  color: var(--color-accent-hover);
  text-decoration: underline;
}
.meta-sep {
  color: var(--color-ink-faint);
}
.index-thread-title {
  font-size: 1.32rem;
  line-height: 1.45;
  margin: 0 0 0.55rem;
}
.index-thread-title a {
  text-decoration: none;
}
.index-thread-title a:hover {
  color: var(--color-accent);
  text-decoration: underline;
}
.index-thread-hook {
  margin: 0 0 0.85rem;
  font-size: 0.94rem;
  color: var(--color-ink-2);
}
.log-preview-box {
  background-color: var(--color-paper-2);
  border-top: 1px solid var(--color-rule);
  border-bottom: 1px solid var(--color-rule);
  padding: 0.7rem 0.95rem;
  margin-bottom: 0.75rem;
  font-size: 0.86rem;
}
.log-preview-line {
  margin-bottom: 0.35rem;
  line-height: 1.6;
}
.log-preview-line:last-child {
  margin-bottom: 0;
}
.preview-num {
  font-family: var(--font-mono);
  font-weight: 700;
  color: var(--color-ink-muted);
  font-variant-numeric: tabular-nums;
  margin-right: 0.35rem;
}
.preview-speaker {
  font-weight: 700;
  color: var(--color-pos);
  margin-right: 0.4rem;
}
.thread-footer-bar {
  display: flex;
  flex-wrap: wrap;
  justify-content: space-between;
  align-items: center;
  gap: var(--space-sm);
}
.gear-inline-list {
  display: flex;
  flex-wrap: wrap;
  gap: 0.4rem;
}
.gear-chip {
  font-family: var(--font-mono);
  font-size: 0.73rem;
  padding: 0.1rem 0.45rem;
  border: 1px solid var(--color-rule-strong);
  background-color: var(--color-paper);
  color: var(--color-ink-2);
  text-decoration: none;
  cursor: pointer;
  transition: background-color var(--dur-short) var(--ease-out), color var(--dur-short) var(--ease-out), border-color var(--dur-short) var(--ease-out);
}
a.gear-chip:hover {
  background-color: var(--color-accent);
  border-color: var(--color-accent);
  color: var(--color-paper);
  text-decoration: none;
}
.read-log-link {
  font-family: var(--font-sans);
  font-size: 0.86rem;
  font-weight: 700;
  color: var(--color-accent);
  text-decoration: none;
  white-space: nowrap;
}
.read-log-link:hover {
  color: var(--color-accent-hover);
  text-decoration: underline;
}

/* Sidebar Search & Device Ledger */
.ledger-aside {
  min-width: 0;
}
.search-box-wrap {
  margin: var(--space-md) 0 var(--space-xl);
}
.search-input {
  width: 100%;
  padding: 0.6rem 0.8rem;
  font-family: var(--font-sans);
  font-size: 0.88rem;
  color: var(--color-ink);
  background-color: var(--color-paper-2);
  border: 1px solid var(--color-rule-strong);
  border-radius: 0;
}
.search-input::placeholder {
  color: var(--color-ink-muted);
}
.search-input:focus {
  outline: 2px solid var(--color-accent);
  outline-offset: 0;
  background-color: var(--color-paper);
}
.search-status {
  margin-top: 0.35rem;
  font-family: var(--font-mono);
  font-size: 0.74rem;
  color: var(--color-ink-muted);
  min-height: 1.2em;
}
.ledger-lead {
  margin: 0.5rem 0 var(--space-md);
  font-size: 0.82rem;
  color: var(--color-ink-muted);
  line-height: 1.6;
}
.rank-row {
  padding: 0.9rem 0;
  border-bottom: 1px solid var(--color-rule);
}
.rank-head {
  display: flex;
  justify-content: space-between;
  align-items: baseline;
  gap: var(--space-xs);
  margin-bottom: 0.2rem;
}
.rank-no {
  font-family: var(--font-mono);
  font-size: 0.85rem;
  font-weight: 700;
  color: var(--color-accent);
  font-variant-numeric: tabular-nums;
  margin-right: 0.4rem;
}
.rank-name {
  font-weight: 700;
  font-size: 0.96rem;
}
.rank-cat {
  font-family: var(--font-mono);
  font-size: 0.68rem;
  color: var(--color-ink-muted);
  white-space: nowrap;
}
.rank-stats {
  font-family: var(--font-mono);
  font-size: 0.74rem;
  color: var(--color-pos);
  font-variant-numeric: tabular-nums;
  margin-bottom: 0.3rem;
}
.rank-comment {
  margin: 0 0 0.55rem;
  font-size: 0.82rem;
  color: var(--color-ink-2);
  line-height: 1.55;
}
.shop-actions {
  display: flex;
  flex-wrap: wrap;
  gap: 0.45rem;
}
.shop-btn {
  display: inline-block;
  padding: 0.32rem 0.7rem;
  font-family: var(--font-sans);
  font-size: 0.76rem;
  font-weight: 700;
  text-decoration: none;
  white-space: nowrap;
  border: 1px solid var(--color-rule-strong);
  transition: background-color var(--dur-short) var(--ease-out), color var(--dur-short) var(--ease-out);
}
.shop-btn-amzn {
  background-color: var(--color-amzn-bg);
  color: var(--color-amzn-fg);
  border-color: var(--color-amzn-bg);
}
.shop-btn-amzn:hover {
  background-color: var(--color-ink-2);
  color: var(--color-amzn-fg);
}
.shop-btn-rktn {
  background-color: var(--color-rktn-bg);
  color: var(--color-rktn-fg);
  border-color: var(--color-rktn-bg);
}
.shop-btn-rktn:hover {
  background-color: var(--color-accent-hover);
  color: var(--color-rktn-fg);
}

/* Article / Thread Page (Long Document + Forum Log) */
.article-wrap {
  max-width: 1200px;
  margin: 0 auto;
  padding: var(--space-xl) var(--space-lg);
}
.article-main {
  min-width: 0;
}
.thread-header {
  border-bottom: 1px solid var(--color-rule-strong);
  padding-bottom: var(--space-lg);
  margin-bottom: var(--space-xl);
}
.thread-title {
  font-size: clamp(1.5rem, 2.8vw, 2.05rem);
  line-height: 1.38;
  margin: 0.4rem 0 0.75rem;
}
.thread-source-line {
  font-family: var(--font-mono);
  font-size: 0.78rem;
  color: var(--color-ink-muted);
  margin: 0;
  overflow-wrap: anywhere;
}

/* Consensus Summary Block */
.consensus-sheet {
  background-color: var(--color-paper-2);
  border: 1px solid var(--color-rule);
  padding: var(--space-lg);
  margin-bottom: var(--space-2xl);
}
.consensus-hook {
  font-weight: 700;
  font-size: 1.02rem;
  color: var(--color-ink);
  margin: 0 0 var(--space-md);
  line-height: 1.7;
}
.consensus-head {
  font-family: var(--font-mono);
  font-size: 0.78rem;
  font-weight: 700;
  letter-spacing: 0.04em;
  color: var(--color-accent);
  margin: 0 0 0.5rem;
}
.consensus-list {
  margin: 0;
  padding-left: 1.25rem;
}
.consensus-list li {
  margin-bottom: 0.4rem;
  font-size: 0.94rem;
  color: var(--color-ink-2);
}
.consensus-list li:last-child {
  margin-bottom: 0;
}

/* Reddit-Style Comment Tree & OP Post */
.thread-log-section {
  margin-bottom: var(--space-2xl);
}
.rc-op-post {
  background-color: var(--color-op-bg);
  padding: 1.25rem 1.35rem;
  border: 1px solid var(--color-rule);
  margin-top: var(--space-md);
  margin-bottom: var(--space-lg);
}
.rc-op-media {
  margin-top: 0.9rem;
  padding-top: 0.75rem;
  border-top: 1px solid var(--color-rule);
  font-size: 0.85rem;
}
.rc-op-media-list {
  list-style: none;
  margin: 0;
  padding: 0;
  display: flex;
  flex-wrap: wrap;
  gap: 0.6rem;
}
.rc-op-media-link {
  display: inline-block;
  font-family: var(--font-sans);
  font-size: 0.8rem;
  font-weight: 700;
  color: var(--color-accent);
  background-color: var(--color-paper);
  border: 1px solid var(--color-rule-strong);
  padding: 0.25rem 0.65rem;
  text-decoration: none;
  transition: background-color var(--dur-short) var(--ease-out), color var(--dur-short) var(--ease-out);
}
.rc-op-media-link:hover {
  background-color: var(--color-accent);
  border-color: var(--color-accent);
  color: var(--color-paper);
  text-decoration: none;
}
.rc-head {
  font-family: var(--font-mono);
  font-size: 0.78rem;
  font-variant-numeric: tabular-nums;
  display: flex;
  flex-wrap: wrap;
  align-items: center;
  gap: 0.5rem;
  margin-bottom: 0.45rem;
}
.rc-author {
  font-weight: 700;
  font-size: 0.84rem;
  color: var(--color-ink);
}
.rc-badge-op {
  font-family: var(--font-mono);
  font-size: 0.7rem;
  font-weight: 700;
  padding: 0.08rem 0.45rem;
  background-color: var(--color-op-badge);
  color: var(--color-paper);
  letter-spacing: 0.02em;
}
.rc-flair {
  font-family: var(--font-mono);
  font-size: 0.71rem;
  padding: 0.06rem 0.45rem;
  background-color: var(--color-paper-2);
  border: 1px solid var(--color-rule-strong);
  color: var(--color-ink-2);
}
.rc-reply-to {
  font-family: var(--font-sans);
  font-size: 0.74rem;
  color: var(--color-ink-muted);
}
.rc-score {
  color: var(--color-ink-muted);
  font-size: 0.75rem;
  margin-left: auto;
}
.rc-score-high {
  color: var(--color-accent);
  font-weight: 700;
}
.rc-body {
  font-size: 0.97rem;
  line-height: 1.85;
  color: var(--color-ink);
  max-width: 68ch;
  overflow-wrap: anywhere;
}
.rc-quote {
  margin: 0.4rem 0;
  padding: 0.25rem 0.75rem;
  border-left: 2px solid var(--color-rule-strong);
  background-color: var(--color-paper-2);
  color: var(--color-ink-2);
  font-size: 0.91rem;
}
.rc-tree {
  margin-top: var(--space-sm);
}
.rc-tree > .rc-node {
  padding: 1.05rem 0;
  border-bottom: 1px solid var(--color-rule);
}
.rc-children {
  margin-top: 0.65rem;
  margin-left: 0.55rem;
  padding-left: 1.15rem;
  border-left: 1px solid var(--color-rule);
  transition: border-color var(--dur-short) var(--ease-out);
}
.rc-children:hover {
  border-left-color: var(--color-rule-strong);
}
.rc-children .rc-node {
  padding: 0.7rem 0 0.25rem;
  border-top: 1px solid oklch(90.0% 0.010 75);
}
.rc-children .rc-node:first-child {
  border-top: none;
}
@media (max-width: 600px) {
  .rc-children {
    margin-left: 0.25rem;
    padding-left: 0.75rem;
  }
}

/* Editorial Deep Analysis Note */
.analysis-section {
  margin-bottom: var(--space-2xl);
}
.analysis-prose {
  max-width: 66ch;
  margin-top: var(--space-md);
}
.analysis-subhead {
  font-family: var(--font-display);
  font-size: 1.18rem;
  font-weight: 700;
  line-height: 1.4;
  margin: var(--space-lg) 0 0.5rem;
  padding-bottom: 0.25rem;
  border-bottom: 1px solid var(--color-rule);
}
.analysis-para {
  margin: 0 0 1.1rem;
  font-size: 0.97rem;
  line-height: 1.9;
  color: var(--color-ink-2);
}

/* Mentioned Gear Specification Table */
.gear-section {
  margin-bottom: var(--space-xl);
}
.gear-section > .analysis-para {
  margin-top: var(--space-md);
}
.gear-row {
  padding: 0.95rem 0;
  border-bottom: 1px solid var(--color-rule);
}
.gear-meta-line {
  display: flex;
  flex-wrap: wrap;
  align-items: center;
  gap: 0.5rem;
  margin-bottom: 0.3rem;
}
.gear-cat-code {
  font-family: var(--font-mono);
  font-size: 0.72rem;
  font-weight: 700;
  color: var(--color-ink-muted);
  border: 1px solid var(--color-rule-strong);
  padding: 0.08rem 0.45rem;
}
.status-tag {
  font-family: var(--font-sans);
  font-size: 0.73rem;
  font-weight: 700;
  padding: 0.1rem 0.5rem;
}
.status-pos {
  background-color: var(--color-pos-bg);
  color: var(--color-pos);
}
.status-neu {
  background-color: var(--color-neu-bg);
  color: var(--color-neu);
}
.status-neg {
  background-color: var(--color-neg-bg);
  color: var(--color-neg);
}
.gear-title {
  font-family: var(--font-display);
  font-size: 1.05rem;
  font-weight: 700;
  line-height: 1.4;
  margin: 0 0 0.3rem;
}
.gear-title-link {
  text-decoration: none;
  color: var(--color-ink);
}
.gear-title-link:hover {
  color: var(--color-accent);
  text-decoration: underline;
}
.gear-desc {
  margin: 0 0 0.55rem;
  font-size: 0.85rem;
  color: var(--color-ink-2);
  line-height: 1.6;
}

/* X Account Section (Sidebar & Footer) */
.x-account-section {
  margin-top: var(--space-xl);
}
.x-account-box {
  margin-top: var(--space-sm);
  padding: 0.65rem 0;
}
.x-account-link {
  display: inline-block;
  font-family: var(--font-mono);
  font-size: 0.85rem;
  font-weight: 700;
  color: var(--color-ink);
  background-color: var(--color-paper-2);
  border: 1px solid var(--color-rule-strong);
  padding: 0.35rem 0.8rem;
  text-decoration: none;
  transition: background-color var(--dur-short) var(--ease-out), color var(--dur-short) var(--ease-out);
}
.x-account-link:hover {
  background-color: var(--color-ink);
  color: var(--color-paper);
  text-decoration: none;
}
.x-account-unset {
  font-family: var(--font-mono);
  font-size: 0.78rem;
  color: var(--color-ink-muted);
}

/* Related Threads Navigation (For Longer Site Stay) */
.related-section {
  margin-bottom: var(--space-xl);
}
.related-list {
  list-style: none;
  margin: 0;
  padding: 0;
}
.related-item {
  padding: 0.85rem 0;
  border-bottom: 1px solid var(--color-rule);
  display: flex;
  flex-direction: column;
  align-items: flex-start;
  gap: 0.28rem;
}
.related-link {
  font-family: var(--font-display);
  font-weight: 700;
  font-size: 1.02rem;
  line-height: 1.45;
  text-decoration: none;
}
.related-link:hover {
  color: var(--color-accent);
  text-decoration: underline;
}

/* Pagination & Back-to-top Controls */
.pagination-bar {
  margin-top: var(--space-lg);
  padding-top: var(--space-md);
  display: flex;
  flex-wrap: wrap;
  justify-content: space-between;
  align-items: center;
  gap: var(--space-sm);
}
.page-info {
  font-family: var(--font-mono);
  font-size: 0.78rem;
  color: var(--color-ink-muted);
  font-variant-numeric: tabular-nums;
}
.page-btn-group {
  display: flex;
  flex-wrap: wrap;
  gap: 0.35rem;
}
.page-btn {
  appearance: none;
  background-color: var(--color-paper-2);
  border: 1px solid var(--color-rule-strong);
  padding: 0.35rem 0.75rem;
  font-family: var(--font-mono);
  font-size: 0.8rem;
  font-weight: 700;
  color: var(--color-ink-2);
  cursor: pointer;
  font-variant-numeric: tabular-nums;
  transition: background-color var(--dur-short) var(--ease-out), color var(--dur-short) var(--ease-out);
}
.page-btn:hover:not(:disabled) {
  background-color: var(--color-ink);
  color: var(--color-paper);
}
.page-btn.active {
  background-color: var(--color-accent);
  border-color: var(--color-accent);
  color: var(--color-paper);
}
.page-btn:disabled {
  opacity: 0.4;
  cursor: default;
}
.back-to-top-wrap {
  margin-top: var(--space-2xl);
  padding-top: var(--space-md);
  border-top: 1px solid var(--color-rule);
  display: flex;
  flex-wrap: wrap;
  justify-content: space-between;
  align-items: center;
  gap: var(--space-sm);
}
.back-to-top-btn {
  appearance: none;
  background-color: var(--color-paper-2);
  border: 1px solid var(--color-rule-strong);
  padding: 0.45rem 0.95rem;
  font-family: var(--font-sans);
  font-size: 0.8rem;
  font-weight: 700;
  color: var(--color-ink-2);
  cursor: pointer;
  margin-left: auto;
  transition: background-color var(--dur-short) var(--ease-out), color var(--dur-short) var(--ease-out);
}
.back-to-top-btn:hover {
  background-color: var(--color-ink);
  color: var(--color-paper);
}
.share-group {
  display: inline-flex;
  flex-wrap: wrap;
  align-items: center;
  gap: 0.35rem;
}
.thread-meta-bar .share-group {
  margin-left: auto;
}
.share-btn {
  appearance: none;
  background-color: var(--color-paper-2);
  border: 1px solid var(--color-rule-strong);
  padding: 0.22rem 0.55rem;
  font-family: var(--font-mono);
  font-size: 0.72rem;
  font-weight: 700;
  color: var(--color-ink-2);
  cursor: pointer;
  text-decoration: none;
  line-height: 1.4;
  transition: background-color var(--dur-short) var(--ease-out), color var(--dur-short) var(--ease-out);
}
.share-btn:hover {
  background-color: var(--color-ink);
  color: var(--color-paper);
}

/* Ft4 Dense Colophon Footer */
.colophon {
  border-top: 3px double var(--color-rule-strong);
  background-color: var(--color-paper-2);
  margin-top: var(--space-2xl);
  padding: var(--space-xl) var(--space-lg);
}
.colophon-inner {
  max-width: 1200px;
  margin: 0 auto;
  font-size: 0.8rem;
  color: var(--color-ink-muted);
  line-height: 1.7;
  display: grid;
  grid-template-columns: minmax(0, 2fr) minmax(0, 1fr);
  gap: var(--space-lg);
}
@media (max-width: 768px) {
  .colophon-inner {
    grid-template-columns: minmax(0, 1fr);
  }
}
.colophon-title {
  font-family: var(--font-display);
  font-weight: 700;
  font-size: 0.95rem;
  color: var(--color-ink);
  margin: 0 0 0.35rem;
}
.colophon-mono {
  font-family: var(--font-mono);
  font-size: 0.74rem;
  font-variant-numeric: tabular-nums;
}
"""

    # 各記事の個別HTMLページ生成
    for idx_art, art in enumerate(published):
        art_id = html.escape(str(art["id"]))
        title = html.escape(art.get("title_ja", ""))
        sub_raw = str(art.get("subreddit", ""))
        sub_label = html.escape(SUBREDDIT_LABELS.get(sub_raw, "海外FPS議論"))
        hook = html.escape(art.get("hook_ja", ""))
        total_comments, char_count, read_min = _compute_thread_metrics(art)

        points_html = "".join(
            f"<li>{html.escape(p)}</li>"
            for p in art.get("consensus_points", [])
        )

        # スレ主（OP）の相談・投稿本文ブロック + 添付画像URL誘導 + 匿名化された実コメントツリーHTMLの組み立て
        op_text = (art.get("op_post_ja") or "").strip()
        op_flair_raw = str(art.get("op_flair") or "").strip()
        if not op_flair_raw:
            for c_node in art.get("comment_tree") or []:
                if c_node.get("is_op") and c_node.get("flair"):
                    op_flair_raw = str(c_node["flair"]).strip()
                    break
        op_flair_html = f'<span class="rc-flair">{html.escape(op_flair_raw)}</span>' if op_flair_raw else ""

        img_urls = [str(u).strip() for u in (art.get("image_urls") or []) if str(u).strip()]
        op_media_html = ""
        if img_urls:
            video_count = sum(1 for u in img_urls if _is_video_url(u))
            image_count = len(img_urls) - video_count
            v_idx = 0
            i_idx = 0
            media_li_list: list[str] = []
            for u in img_urls:
                if _is_video_url(u):
                    v_idx += 1
                    lbl = f"添付動画{v_idx}を見る ↗" if video_count > 1 else "添付動画を見る ↗"
                else:
                    i_idx += 1
                    lbl = f"添付画像{i_idx}を見る ↗" if image_count > 1 else "添付画像を見る ↗"
                media_li_list.append(
                    f'<li><a class="rc-op-media-link" href="{html.escape(u)}" target="_blank" rel="noopener">{lbl}</a></li>'
                )
            op_media_html = (
                f'<div class="rc-op-media">'
                f'<ul class="rc-op-media-list">{"".join(media_li_list)}</ul>'
                f'</div>'
            )

        op_block_html = ""
        if op_text or op_media_html:
            op_body_html = _format_res_body_html(op_text) if op_text else ""
            op_block_html = (
                f'<div class="rc-op-post" id="op-post">'
                f'<div class="rc-head">'
                f'<span class="rc-author">スレ主</span>'
                f'<span class="rc-badge-op">OP</span>'
                f'{op_flair_html}'
                f'</div>'
                f'<div class="rc-body">{op_body_html}</div>'
                f'{op_media_html}'
                f'</div>'
            )

        tree_html, actual_comment_count = _build_reddit_tree_html(art)
        dialogue_html = op_block_html + "\n" + tree_html
        analysis_html = _format_analysis_html(art.get("detailed_analysis_ja", ""))

        devices_html = ""
        for dev in art.get("devices", []):
            d_name = normalize_product_name_jp(dev.get("name", ""))
            if not d_name:
                continue
            cat_key = dev.get("category", "other")
            cat_label = CATEGORY_LABELS.get(cat_key, cat_key)
            sent_cls, sent_label = SENTIMENT_BADGES.get(dev.get("sentiment", "neutral"), SENTIMENT_BADGES["neutral"])
            links = build_affiliate_urls(d_name, master, env)
            clean_desc = _clean_device_comment_ja(dev.get("comment_ja", ""))
            d_q_href = html.escape(f"../index.html?q={urllib.parse.quote(d_name)}")
            devices_html += f"""
            <div class="gear-row">
              <div class="gear-meta-line">
                <span class="gear-cat-code">{html.escape(cat_label)}</span>
                <span class="status-tag {sent_cls}">{html.escape(sent_label)}</span>
              </div>
              <h3 class="gear-title"><a class="gear-title-link" href="{d_q_href}">{html.escape(d_name)}</a></h3>
              <p class="gear-desc">{html.escape(clean_desc)}</p>
              <div class="shop-actions">
                <a class="shop-btn shop-btn-amzn" href="{html.escape(links["amazon_url"])}" target="_blank" rel="nofollow sponsored noopener">Amazonで見る ↗</a>
                <a class="shop-btn shop-btn-rktn" href="{html.escape(links["rakuten_url"])}" target="_blank" rel="nofollow sponsored noopener">楽天で見る ↗</a>
              </div>
            </div>
            """

        # 他のスレッドへの回遊リスト（自身を除く最大5件）
        other_threads_html = ""
        others = [a for a in published if str(a.get("id")) != str(art.get("id"))][:5]
        for o_art in others:
            o_id = html.escape(str(o_art["id"]))
            o_sub = html.escape(str(o_art.get("subreddit", "")))
            o_cat = html.escape(SUBREDDIT_LABELS.get(str(o_art.get("subreddit", "")), "海外FPS議論"))
            o_title = html.escape(o_art.get("title_ja", ""))
            o_comments, _, _ = _compute_thread_metrics(o_art)
            other_threads_html += (
                f'<li class="related-item">'
                f'<a class="related-link" href="{o_id}.html">{o_title}</a>'
                f'<div class="section-sub"><a class="sub-tag" href="../index.html?sub={o_sub}">{o_cat}</a> · コメント {o_comments}件</div>'
                f'</li>'
            )

        page_html = f"""<!DOCTYPE html>
<html lang="ja">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>{title} | エイム沼の海外ログ</title>
  {font_links}
  <style>{css}</style>
</head>
<body id="top">
  <header class="masthead">
    <div class="masthead-Compact">
      <a href="../index.html" class="masthead-Compact-brand">エイム沼の海外ログ</a>
      <a href="../index.html" class="back-index-link">← スレッド一覧へ戻る</a>
    </div>
  </header>
  <main class="article-wrap">
    <div class="article-grid">
      <div class="article-main">
        <header class="thread-header">
          <div class="thread-meta-bar">
            <a class="sub-tag" href="../index.html">スレッド一覧</a>
            <span class="meta-sep">/</span>
            <a class="sub-tag" href="../index.html?sub={html.escape(sub_raw)}">{sub_label}</a>
            <span class="meta-sep">/</span>
            <span>コメント {actual_comment_count}件</span>
            <span class="share-group">
              <button type="button" class="share-btn" onclick="shareToX()">Xでシェア ↗</button>
              <button type="button" class="share-btn" onclick="copyPageUrl(this)">URLコピー</button>
            </span>
          </div>
          <h1 class="thread-title">{title}</h1>
          <p class="thread-source-line">
            元スレッド: <a href="{html.escape(art.get('permalink', '#'))}" target="_blank" rel="noopener">{html.escape(art.get('title_en', 'Reddit Thread'))}</a>
          </p>
        </header>

        <section class="consensus-sheet">
          <p class="consensus-hook">{hook}</p>
          <div class="consensus-head">スレッドの要点</div>
          <ul class="consensus-list">{points_html}</ul>
        </section>

        <section class="thread-log-section">
          <div class="section-header">
            <h2 class="section-title">コメント（{actual_comment_count}件）</h2>
          </div>
          {dialogue_html}
        </section>

        <section class="analysis-section">
          <div class="section-header">
            <h2 class="section-title">深掘り解説・考察ノート</h2>
          </div>
          <div class="analysis-prose">
            {analysis_html}
          </div>
        </section>

        <nav class="related-section" aria-label="その他のスレッド">
          <div class="section-header">
            <h2 class="section-title">他のスレッド</h2>
          </div>
          <ul class="related-list">
            {other_threads_html}
          </ul>
        </nav>
      </div>

      <aside class="ledger-aside">
        <div class="section-header">
          <h2 class="section-title">スレッド・機材検索</h2>
        </div>
        <form class="search-box-wrap" action="../index.html" method="get">
          <input type="search" name="q" class="search-input" placeholder="マウス名・用語・悩みで検索..." aria-label="スレッド検索">
        </form>

        <section class="gear-section">
          <div class="section-header">
            <h2 class="section-title">登場デバイス</h2>
          </div>
          {devices_html or '<p class="analysis-para">このスレッドでは特定製品の指定はありません（エイム技術・設定中心の議論）。</p>'}
        </section>

        {x_sidebar_html}
      </aside>
    </div>

    <div class="back-to-top-wrap">
      <div class="share-group">
        <button type="button" class="share-btn" onclick="shareToX()">Xでシェア ↗</button>
        <button type="button" class="share-btn" onclick="copyPageUrl(this)">URLコピー</button>
      </div>
      <button type="button" class="back-to-top-btn" onclick="window.scrollTo({{top: 0, behavior: 'smooth'}})">↑ 一番上へ戻る</button>
    </div>
  </main>

  <footer class="colophon">
    <div class="colophon-inner">
      <div>
        <p class="colophon-title">エイム沼の海外ログ</p>
        <p>海外Reddit（r/FPSAimTrainer・r/MouseReview・r/MousepadReview）の議論スレッドを翻訳・編纂しているアーカイブサイトです。Amazonのアソシエイトおよび楽天アフィリエイトプログラムに参加しています。</p>
      </div>
      <div class="colophon-mono">
        <div>SOURCES: r/FPSAimTrainer / r/MouseReview / r/MousepadReview</div>
        <div>UPDATED: {updated_date} · {len(published)} THREADS</div>
        {x_footer_html}
      </div>
    </div>
  </footer>
  <script>
    function shareToX() {{
      const u = window.location.href;
      const t = document.title;
      window.open('https://twitter.com/intent/tweet?text=' + encodeURIComponent(t) + '&url=' + encodeURIComponent(u), '_blank', 'noopener');
    }}
    function copyPageUrl(btn) {{
      const u = window.location.href;
      if (navigator.clipboard && navigator.clipboard.writeText) {{
        navigator.clipboard.writeText(u);
      }}
      const orig = btn.textContent;
      btn.textContent = 'コピー完了';
      setTimeout(() => {{ btn.textContent = orig; }}, 1600);
    }}
  </script>
</body>
</html>"""
        (articles_dir / f"{art_id}.html").write_text(page_html, encoding="utf-8")

    # サイドバー用: 高評価デバイス番付 (上位10件をスペック台帳風に表示)
    ranking_html = ""
    for idx, item in enumerate(ranking[:10], start=1):
        cat_label = CATEGORY_LABELS.get(item["category"], item["category"])
        comments_str = " / ".join(html.escape(c) for c in item["comments"])
        ranking_html += f"""
        <div class="rank-row">
          <div class="rank-head">
            <div><span class="rank-no">{idx:02d}</span><span class="rank-name">{html.escape(item['name'])}</span></div>
            <span class="rank-cat">{html.escape(cat_label)}</span>
          </div>
          <div class="rank-stats">高評価 {item['positive']}件 / 計{item['mentions']}スレッドで言及</div>
          <p class="rank-comment">{comments_str}</p>
          <div class="shop-actions">
            <a class="shop-btn shop-btn-amzn" href="{html.escape(item['amazon_url'])}" target="_blank" rel="nofollow sponsored noopener">Amazonで見る ↗</a>
            <a class="shop-btn shop-btn-rktn" href="{html.escape(item['rakuten_url'])}" target="_blank" rel="nofollow sponsored noopener">楽天で見る ↗</a>
          </div>
        </div>
        """

    # メインカラム用: スレッドインデックス一覧（匿名化された実コメント抜粋プレビュー付き）
    # 記事番号は一番古い記事が #01 になるよう降順で付与する
    articles_list_html = ""
    total_published = len(published)
    for idx_zero, art in enumerate(published):
        idx_num = total_published - idx_zero
        art_id = html.escape(str(art["id"]))
        sub_raw = str(art.get("subreddit", ""))
        sub_attr = html.escape(sub_raw)
        sub_label = html.escape(SUBREDDIT_LABELS.get(sub_raw, "海外FPS議論"))
        total_comments, char_count, read_min = _compute_thread_metrics(art)

        dev_chips_list: list[str] = []
        for d in (art.get("devices") or [])[:4]:
            d_norm = normalize_product_name_jp(d.get("name", ""))
            if not d_norm:
                continue
            d_esc = html.escape(d_norm)
            q_href = html.escape(f"index.html?q={urllib.parse.quote(d_norm)}")
            dev_chips_list.append(
                f'<a class="gear-chip" href="{q_href}" data-device="{d_esc}" onclick="filterByDevice(this.dataset.device); return false;">{d_esc}</a>'
            )
        dev_chips = "".join(dev_chips_list)

        # スレッド内の実コメントから先頭2件を抜粋プレビュー表示（匿名表記）
        preview_lines: list[str] = []
        tree_preview = _anonymize_comment_tree(list(art.get("comment_tree") or []))
        if tree_preview:
            for c in tree_preview[:2]:
                au = html.escape(str(c.get("author") or "海外ユーザー"))
                tx = str(c.get("body_ja") or c.get("body_en") or "").strip()
                if len(tx) > 88:
                    tx = tx[:88] + "…"
                preview_lines.append(
                    f'<div class="log-preview-line">'
                    f'<span class="preview-speaker">{au}:</span>'
                    f'<span>{html.escape(tx)}</span>'
                    f'</div>'
                )
        else:
            for p_idx, d in enumerate((art.get("dialogue") or [])[:2], start=1):
                sp_raw = str(d.get("speaker") or f"海外ユーザー{p_idx}")
                sp = html.escape("スレ主" if "スレ主" in sp_raw or "(OP)" in sp_raw else f"海外ユーザー{p_idx}")
                tx = str(d.get("text") or "").strip()
                if len(tx) > 88:
                    tx = tx[:88] + "…"
                preview_lines.append(
                    f'<div class="log-preview-line">'
                    f'<span class="preview-speaker">{sp}:</span>'
                    f'<span>{html.escape(tx)}</span>'
                    f'</div>'
                )
        preview_box_html = (
            f'<div class="log-preview-box">{"".join(preview_lines)}</div>'
            if preview_lines else ""
        )

        # ページ分割時でも記事本文・全コメント・全デバイスを横断検索できるように検索インデックス文字列を構築
        search_chunks: list[str] = [
            str(art.get("title_ja") or ""),
            str(art.get("title_en") or ""),
            str(art.get("hook_ja") or ""),
            str(art.get("op_post_ja") or ""),
            str(art.get("detailed_analysis_ja") or ""),
            SUBREDDIT_LABELS.get(sub_raw, ""),
        ]
        search_chunks.extend(str(p) for p in (art.get("consensus_points") or []))
        for d_item in art.get("devices") or []:
            search_chunks.append(str(d_item.get("name") or ""))
            search_chunks.append(normalize_product_name_jp(str(d_item.get("name") or "")))
            search_chunks.append(str(d_item.get("comment_ja") or ""))
        for c_item in art.get("comment_tree") or []:
            search_chunks.append(str(c_item.get("body_ja") or ""))
        search_blob_attr = html.escape(re.sub(r"\s+", " ", " ".join(search_chunks)).strip().lower())

        articles_list_html += f"""
        <article class="thread-index-row" data-sub="{sub_attr}" data-search="{search_blob_attr}">
          <div class="thread-meta-bar">
            <span>#{idx_num:02d}</span>
            <span class="meta-sep">/</span>
            <a class="sub-tag" href="index.html?sub={sub_attr}" onclick="filterSub('{sub_attr}'); return false;">{sub_label}</a>
            <span class="meta-sep">/</span>
            <span>コメント {total_comments}件</span>
          </div>
          <h3 class="index-thread-title">
            <a href="articles/{art_id}.html">{html.escape(art.get('title_ja', ''))}</a>
          </h3>
          <p class="index-thread-hook">{html.escape(art.get('hook_ja', ''))}</p>
          {preview_box_html}
          <div class="thread-footer-bar">
            <div class="gear-inline-list">{dev_chips}</div>
            <a class="read-log-link" href="articles/{art_id}.html">続きを読む（{total_comments}件） →</a>
          </div>
        </article>
        """

    index_html = f"""<!DOCTYPE html>
<html lang="ja">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>エイム沼の海外ログ | 海外Redditの競技エイム理論・マウス・マウスパッド議論が読める翻訳アーカイブ</title>
  {font_links}
  <style>{css}</style>
</head>
<body id="top">
  <header class="masthead">
    <div class="masthead-Core">
      <div>
        <h1 class="site-title"><a href="index.html">エイム沼の海外ログ</a></h1>
        <p class="site-tagline">海外Redditの競技エイム理論・マウス・マウスパッド議論が読める翻訳アーカイブ</p>
      </div>
      <div class="share-group">
        <button type="button" class="share-btn" onclick="shareToX()">Xでシェア ↗</button>
        <button type="button" class="share-btn" onclick="copyPageUrl(this)">URLコピー</button>
      </div>
    </div>
    <div class="filter-strip-wrap">
      <nav class="filter-strip" aria-label="カテゴリ絞り込み">
        <button class="filter-tab active" data-sub="all" onclick="filterSub('all', this)">すべて ({len(published)})</button>
        <button class="filter-tab" data-sub="FPSAimTrainer" onclick="filterSub('FPSAimTrainer', this)">AIM練習・理論</button>
        <button class="filter-tab" data-sub="MouseReview" onclick="filterSub('MouseReview', this)">マウス</button>
        <button class="filter-tab" data-sub="MousepadReview" onclick="filterSub('MousepadReview', this)">マウスパッド・ソール</button>
      </nav>
    </div>
  </header>

  <main class="page-wrap">
    <div class="index-grid">
      <section id="thread-list-section">
        <div class="section-header">
          <h2 class="section-title">スレッド一覧</h2>
        </div>
        <div id="article-list">
          {articles_list_html or '<p class="analysis-para">まだスレッドログがありません。</p>'}
        </div>
        <nav id="pagination-bar" class="pagination-bar" aria-label="ページネーション"></nav>
      </section>

      <aside class="ledger-aside">
        <div class="section-header">
          <h2 class="section-title">スレッド・機材検索</h2>
        </div>
        <div class="search-box-wrap">
          <input type="search" id="thread-search" class="search-input" placeholder="マウス名・用語・悩みで検索..." aria-label="スレッド検索" oninput="onSearchInput()">
          <div id="search-status" class="search-status"></div>
        </div>

        <div class="section-header">
          <h2 class="section-title">高評価ギア番付</h2>
        </div>
        <p class="ledger-lead">スレッド内で好評だったマウス・マウスパッド・ソールの集計</p>
        {ranking_html or '<p class="ledger-lead">高評価デバイスが集計されるとここに表示されます。</p>'}

        {x_sidebar_html}
      </aside>
    </div>

    <div class="back-to-top-wrap">
      <div class="share-group">
        <button type="button" class="share-btn" onclick="shareToX()">Xでシェア ↗</button>
        <button type="button" class="share-btn" onclick="copyPageUrl(this)">URLコピー</button>
      </div>
      <button type="button" class="back-to-top-btn" onclick="window.scrollTo({{top: 0, behavior: 'smooth'}})">↑ 一番上へ戻る</button>
    </div>
  </main>

  <footer class="colophon">
    <div class="colophon-inner">
      <div>
        <p class="colophon-title">エイム沼の海外ログ</p>
        <p>海外Reddit（r/FPSAimTrainer・r/MouseReview・r/MousepadReview）の議論スレッドを翻訳・編纂しているアーカイブサイトです。Amazonのアソシエイトおよび楽天アフィリエイトプログラムに参加しています。</p>
      </div>
      <div class="colophon-mono">
        <div>SOURCES: r/FPSAimTrainer / r/MouseReview / r/MousepadReview</div>
        <div>UPDATED: {updated_date} · {len(published)} THREADS</div>
        {x_footer_html}
      </div>
    </div>
  </footer>

  <script>
    const PER_PAGE = 10;
    let currentSub = 'all';
    let currentPage = 1;

    function shareToX() {{
      const u = window.location.href;
      const t = document.title;
      window.open('https://twitter.com/intent/tweet?text=' + encodeURIComponent(t) + '&url=' + encodeURIComponent(u), '_blank', 'noopener');
    }}

    function copyPageUrl(btn) {{
      const u = window.location.href;
      if (navigator.clipboard && navigator.clipboard.writeText) {{
        navigator.clipboard.writeText(u);
      }}
      const orig = btn.textContent;
      btn.textContent = 'コピー完了';
      setTimeout(() => {{ btn.textContent = orig; }}, 1600);
    }}

    function syncTabButtons() {{
      document.querySelectorAll('.filter-tab').forEach(b => {{
        b.classList.toggle('active', b.dataset.sub === currentSub);
      }});
    }}

    function updateUrlParams() {{
      try {{
        const url = new URL(window.location.href);
        const qVal = (document.getElementById('thread-search')?.value || '').trim();
        if (currentSub && currentSub !== 'all') {{
          url.searchParams.set('sub', currentSub);
        }} else {{
          url.searchParams.delete('sub');
        }}
        if (qVal) {{
          url.searchParams.set('q', qVal);
        }} else {{
          url.searchParams.delete('q');
        }}
        if (currentPage > 1) {{
          url.searchParams.set('page', String(currentPage));
        }} else {{
          url.searchParams.delete('page');
        }}
        window.history.replaceState({{}}, '', url.toString());
      }} catch (e) {{}}
    }}

    function filterSub(sub, btn) {{
      currentSub = sub || 'all';
      currentPage = 1;
      syncTabButtons();
      updateUrlParams();
      applyFilters();
    }}

    function filterByDevice(devName) {{
      const q = (devName || '').trim();
      currentSub = 'all';
      currentPage = 1;
      const searchInput = document.getElementById('thread-search');
      if (searchInput) {{
        searchInput.value = q;
      }}
      syncTabButtons();
      updateUrlParams();
      applyFilters();
      const sec = document.getElementById('thread-list-section');
      if (sec) {{
        sec.scrollIntoView({{ behavior: 'smooth', block: 'start' }});
      }}
    }}

    function onSearchInput() {{
      currentPage = 1;
      updateUrlParams();
      applyFilters();
    }}

    function goToPage(page) {{
      currentPage = page;
      updateUrlParams();
      applyFilters();
      const sec = document.getElementById('thread-list-section');
      if (sec) {{
        sec.scrollIntoView({{ behavior: 'smooth', block: 'start' }});
      }}
    }}

    function applyFilters() {{
      const rawQ = (document.getElementById('thread-search')?.value || '').trim();
      const keywords = rawQ.toLowerCase().split(/\\s+/).filter(Boolean);
      const allArticles = Array.from(document.querySelectorAll('#article-list article'));
      const matched = allArticles.filter(el => {{
        const matchSub = (currentSub === 'all' || el.dataset.sub === currentSub);
        if (!matchSub) return false;
        if (keywords.length === 0) return true;
        const haystack = (el.dataset.search || el.textContent || '').toLowerCase();
        return keywords.every(kw => haystack.includes(kw));
      }});

      const total = matched.length;
      const totalPages = Math.max(1, Math.ceil(total / PER_PAGE));
      if (currentPage > totalPages) currentPage = totalPages;
      if (currentPage < 1) currentPage = 1;

      const startIdx = (currentPage - 1) * PER_PAGE;
      const endIdx = startIdx + PER_PAGE;
      const visibleSet = new Set(matched.slice(startIdx, endIdx));

      allArticles.forEach(el => {{
        el.style.display = visibleSet.has(el) ? '' : 'none';
      }});

      const statusEl = document.getElementById('search-status');
      if (statusEl) {{
        if (!rawQ) {{
          statusEl.textContent = '';
        }} else if (total === 0) {{
          statusEl.textContent = `「${{rawQ}}」に一致するスレッドはありません`;
        }} else {{
          const fromNum = startIdx + 1;
          const toNum = Math.min(endIdx, total);
          statusEl.textContent = `「${{rawQ}}」の検索結果: 全${{total}}件（${{fromNum}}–${{toNum}}件目を表示 / ${{currentPage}}/${{totalPages}}ページ）`;
        }}
      }}

      renderPagination(total, totalPages, startIdx);
    }}

    function renderPagination(total, totalPages, startIdx) {{
      const nav = document.getElementById('pagination-bar');
      if (!nav) return;
      if (total === 0) {{
        nav.innerHTML = '<span class="page-info">該当するスレッドがありません。</span>';
        return;
      }}
      const fromNum = startIdx + 1;
      const toNum = Math.min(startIdx + PER_PAGE, total);
      let btnsHtml = '';
      btnsHtml += `<button type="button" class="page-btn" ${{currentPage <= 1 ? 'disabled' : ''}} onclick="goToPage(${{currentPage - 1}})">« 前へ</button>`;
      for (let p = 1; p <= totalPages; p++) {{
        const activeCls = (p === currentPage) ? ' active' : '';
        btnsHtml += `<button type="button" class="page-btn${{activeCls}}" onclick="goToPage(${{p}})">${{p}}</button>`;
      }}
      btnsHtml += `<button type="button" class="page-btn" ${{currentPage >= totalPages ? 'disabled' : ''}} onclick="goToPage(${{currentPage + 1}})">次へ »</button>`;
      nav.innerHTML = `
        <span class="page-info">全${{total}}件中 ${{fromNum}}–${{toNum}}件を表示（${{currentPage}} / ${{totalPages}}ページ）</span>
        <div class="page-btn-group">${{btnsHtml}}</div>
      `;
    }}

    (function initFromUrl() {{
      try {{
        const params = new URLSearchParams(window.location.search);
        const subParam = params.get('sub');
        if (subParam && ['FPSAimTrainer', 'MouseReview', 'MousepadReview'].includes(subParam)) {{
          currentSub = subParam;
        }}
        const qParam = params.get('q');
        const searchInput = document.getElementById('thread-search');
        if (qParam && searchInput) {{
          searchInput.value = qParam;
        }}
        const pageParam = parseInt(params.get('page') || '1', 10);
        if (!isNaN(pageParam) && pageParam >= 1) {{
          currentPage = pageParam;
        }}
      }} catch (e) {{}}
      syncTabButtons();
      applyFilters();
    }})();
  </script>
</body>
</html>"""
    (out_dir / "index.html").write_text(index_html, encoding="utf-8")


# ============================================================================
# 7. メイン実行フロー ＆ セルフチェック (--self-test)
# ============================================================================

def ensure_initial_files() -> None:
    """初回実行時に商品マスターCSVの雛形を作成する。"""
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    if not PRODUCTS_FILE.exists():
        with PRODUCTS_FILE.open("w", encoding="utf-8-sig", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(["name", "category", "amazon_url", "rakuten_url"])
            writer.writerow(["Razer Viper V3 Pro", "mouse", "", ""])
            writer.writerow(["Logicool G PRO X SUPERLIGHT 2", "mouse", "", ""])
            writer.writerow(["Artisan 零 Soft", "mousepad", "", ""])
            writer.writerow(["Wallhack SP-004", "mousepad", "", ""])


def upgrade_legacy_articles(articles: list[dict[str, Any]], site_base_url: str) -> int:
    """
    実コメントツリー (`comment_tree`) が未取得・未翻訳の記事を、
    Arctic Shift / Reddit API から実コメント階層ツリーを取得した上で
    水増し・創作ゼロの1対1翻訳にアップグレードする。
    ※既に8行以上の `short_script`（ショート動画台本）がある場合は既存の台本をそのまま保持する。
    """
    legacy_articles = [
        a for a in articles
        if (not a.get("comment_tree") or not a.get("op_post_ja"))
        and a.get("title_en")
    ]
    if not legacy_articles:
        return 0

    print(f"[INFO] 記事 {len(legacy_articles)} 件をReddit実コメントツリー仕様（水増しゼロ・1対1翻訳）にアップグレードします...")
    upgraded_count = 0
    for art in legacy_articles:
        try:
            pid = str(art.get("id") or "")
            sub = str(art.get("subreddit") or "")
            print(f"[INFO] 実コメントツリー取得＆翻訳中: [{pid}] {art.get('title_ja') or art['title_en'][:40]}...")

            # OPのユーザー名・フレアが未取得ならArctic Shiftから補完
            if not art.get("op_author") and pid:
                try:
                    p_url = f"https://arctic-shift.photon-reddit.com/api/posts/ids?ids={urllib.parse.quote(pid)}"
                    p_payload = http_get_json(p_url, headers={"User-Agent": REDDIT_USER_AGENT, "Accept": "application/json"})
                    p_rows = p_payload.get("data") if isinstance(p_payload, dict) else []
                    if isinstance(p_rows, list) and p_rows and isinstance(p_rows[0], dict):
                        p0 = p_rows[0]
                        art["op_author"] = str(p0.get("author") or "OriginalPoster").strip()
                        fl = str(p0.get("author_flair_text") or "").strip()
                        if not fl and isinstance(p0.get("author_flair_richtext"), list):
                            fl = "".join(
                                str(x.get("t") or "") for x in p0["author_flair_richtext"] if isinstance(x, dict)
                            ).strip()
                        art["op_flair"] = fl
                except Exception:
                    pass

            # 実コメントツリーを取得
            art["comment_tree"] = fetch_thread_comment_tree(sub, pid, max_comments=30)

            existing_short_script = art.get("short_script")
            summary = summarize_with_gemini(art)
            # 既に8行以上のショート動画台本が存在する場合は上書きせず保持する
            if isinstance(existing_short_script, list) and len(existing_short_script) >= 8:
                summary["short_script"] = existing_short_script
            art.update(summary)
            art_url = art.get("article_url") or f"{site_base_url}/articles/{art['id']}.html"
            art["article_url"] = art_url
            art["x_intent_url"] = build_x_intent_url(summary["x_main_post"], art_url)
            print(
                f"[OK] ツリー翻訳完了: {art['title_ja']} "
                f"(実コメント {len(art.get('comment_tree') or [])}件 / 解説 {len(art.get('detailed_analysis_ja', ''))}字)"
            )
            upgraded_count += 1
            save_articles(articles)
        except Exception as e:
            print(f"[WARN] 記事アップグレード失敗 ({art['id']}): {e}", file=sys.stderr)
    return upgraded_count


def refresh_article_urls(articles: list[dict[str, Any]], site_base_url: str) -> None:
    """SITE_BASE_URL に合わせて全記事の article_url と x_intent_url を最新化する。"""
    base = site_base_url.rstrip("/")
    for art in articles:
        aid = str(art.get("id") or "").strip()
        if not aid:
            continue
        new_url = f"{base}/articles/{aid}.html"
        art["article_url"] = new_url
        if art.get("x_main_post"):
            art["x_intent_url"] = build_x_intent_url(str(art["x_main_post"]), new_url)


def run_pipeline() -> None:
    """日次パイプライン: .env読込 → シート同期 → Reddit収集 → Gemini要約 → シート保存 → サイト生成 → X投稿"""
    load_dotenv()
    ensure_initial_files()
    master = load_product_master()
    articles = load_articles()
    site_base_url = (os.environ.get("SITE_BASE_URL") or "https://example.com").rstrip("/")
    refresh_article_urls(articles, site_base_url)
    articles = sync_with_google_sheets(articles)
    existing_ids = {str(a.get("id")) for a in articles}

    # 旧仕様ドラフトのアップグレードおよび新規スレッドの収集・要約（GEMINI_API_KEY がある時のみ実行）
    if os.environ.get("GEMINI_API_KEY"):
        upgrade_legacy_articles(articles, site_base_url)
        threads = fetch_reddit_threads(existing_ids, max_total=MAX_DRAFTS_PER_RUN)
        print(f"[INFO] 条件に合致した新規スレッド {len(threads)} 件をGeminiで要約します...")
        for th in threads:
            try:
                print(f"[INFO] 要約中: [r/{th['subreddit']}] {th['title_en'][:60]}...")
                summary = summarize_with_gemini(th)
                article_url = f"{site_base_url}/articles/{th['id']}.html"
                record = {
                    **th,
                    **summary,
                    "status": "draft",  # スプレッドシート上で人間が 'published' に変更すると公開される
                    "x_posted": False,
                    "article_url": article_url,
                    "x_intent_url": build_x_intent_url(summary["x_main_post"], article_url),
                    "created_at": dt.datetime.now(dt.timezone.utc).isoformat(),
                }
                articles.append(record)
                print(f"[OK] 生成完了: {summary['title_ja']}")
            except Exception as e:
                print(f"[WARN] スレッド要約失敗 ({th['id']}): {e}", file=sys.stderr)
    else:
        print("[WARN] GEMINI_API_KEY が未設定のため、新規スレッドの要約をスキップしました（.env を確認してください）。")

    # 再同期して保存
    articles = sync_with_google_sheets(articles)
    save_articles(articles)

    # 静的サイト生成
    build_site(articles, out_dir=DIST_DIR, master=master)
    print(f"[DONE] 記事データ ({ARTICLES_FILE}) と Webサイト ({DIST_DIR / 'index.html'}) を出力しました！")

    # 公開済み かつ X未投稿の記事があれば、X API設定時にツリー投稿を実行
    if publish_pending_to_x(articles):
        save_articles(articles)


def self_test() -> None:
    """APIキー無しで全ロジック（フィルタ・アフィリエイトURL生成・ランキング集計・HTML生成）を検証する。"""
    import tempfile

    # 1. スレッドフィルタのテスト
    assert not is_meaningful_thread({"stickied": True, "num_comments": 50, "is_self": True})
    assert not is_meaningful_thread({"num_comments": 5, "is_self": True, "selftext": "short"})
    assert not is_meaningful_thread({"num_comments": 20, "is_self": False, "selftext": ""})
    assert is_meaningful_thread({"num_comments": 25, "is_self": True, "selftext": "Detailed aim training discussion..."})

    # 2. アフィリエイトURL生成のテスト（Amazon直 / 楽天 / もしも）
    urls_direct = build_affiliate_urls(
        "Razer Viper V3 Pro",
        master={},
        env={"AMAZON_ASSOC_TAG": "mytag-22", "RAKUTEN_AFFILIATE_ID": "rk123"},
    )
    assert "tag=mytag-22" in urls_direct["amazon_url"]
    assert "Razer+Viper+V3+Pro" in urls_direct["amazon_url"]
    assert "hb.afl.rakuten.co.jp/hgc/rk123/" in urls_direct["rakuten_url"]

    urls_moshimo = build_affiliate_urls(
        "Artisan 零 Soft",
        master={},
        env={"MOSHIMO_AMAZON_AID": "999111", "MOSHIMO_RAKUTEN_AID": "888222"},
    )
    assert "a_id=999111" in urls_moshimo["amazon_url"]
    assert "a_id=888222" in urls_moshimo["rakuten_url"]

    # 3. ランキング集計＆静的サイト出力のテスト
    sample_articles = [
        {
            "id": "demo1",
            "subreddit": "FPSAimTrainer",
            "title_en": "Tension management changed my tracking forever",
            "title_ja": "【海外エイム理論】「脱力（テンション管理）」を意識したらトラッキング精度が劇的に上がった話",
            "hook_ja": "マウスを強く握りしめるのをやめるだけで、マイクロフリックと滑らかな追いエイムが別次元になります。",
            "consensus_points": [
                "指先と手首の力みを30%以下に抑えるのがVoltaic上位勢の共通認識",
                "力みやすい人は軽量マウス＋コントロール系またはガラスパッド＋汎用丸型ソールで初動摩擦を減らすと改善しやすい",
            ],
            "detailed_analysis_ja": "r/FPSAimTrainerで50件以上のコメントが集まった議論。多くのプレイヤーがターゲット切り返し時に無意識にマウスを強く握り込んでしまい、初動の引っかかりを生んでいると指摘されています。",
            "dialogue": [
                {"speaker": "スレ主", "text": "KovaaK'sで手首の力を抜くようにしたらスコアが一気に伸びたんだが"},
                {"speaker": "海外エイム猛者A", "text": "テンション管理こそエイム練習の本質。あとマウスソールをJadeに変えると初動の力みが消えるぞ"},
            ],
            "devices": [
                {
                    "name": "Razer Viper V3 Pro",
                    "category": "mouse",
                    "sentiment": "positive",
                    "comment_ja": "54gの軽量バランスで脱力したつまみ・つかみ持ちに最適と絶賛",
                },
                {
                    "name": "X-raypad Jade Skates",
                    "category": "skates",
                    "sentiment": "positive",
                    "comment_ja": "初動の引っかかり（静摩擦）が激減する定番の汎用丸型PTFEソール",
                },
            ],
            "x_main_post": "海外r/FPSAimTrainerで話題の「脱力（テンション管理）」まとめ🎯\n・指先の力みを抜くだけで追いエイムが激変\n・初動で力む人は軽量マウス＋丸型ソールで静摩擦を減らすのが正解",
            "x_reply_post": "スレッド内の50人の議論まとめ＆絶賛されていたマウス・ソール一覧はこちら👇\n{{ARTICLE_URL}}",
            "short_script": [
                {"speaker": "zundamon", "text": "エイムがガクつく人は、マウスを強く握りすぎなのだ！", "caption": "エイム悪化の真犯人＝力み"},
                {"speaker": "aoyama", "text": "海外のエイム猛者50人の結論を見てみよう。", "caption": "海外Reddit 50人の結論"},
            ],
            "status": "published",
            "permalink": "https://www.reddit.com/r/FPSAimTrainer/comments/demo1/",
            "created_at": "2026-10-20T00:00:00Z",
        }
    ]

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        build_site(sample_articles, out_dir=tmp_path, env={"AMAZON_ASSOC_TAG": "test-22"})
        index_content = (tmp_path / "index.html").read_text(encoding="utf-8")
        article_content = (tmp_path / "articles" / "demo1.html").read_text(encoding="utf-8")
        assert "Razer Viper V3 Pro" in index_content
        assert "tag=test-22" in article_content

    print("SELF_TEST_OK")


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        self_test()
    elif "--sync-only" in sys.argv:
        load_dotenv()
        ensure_initial_files()
        master = load_product_master()
        articles = load_articles()
        site_base_url = (os.environ.get("SITE_BASE_URL") or "https://example.com").rstrip("/")
        refresh_article_urls(articles, site_base_url)
        articles = sync_with_google_sheets(articles)
        save_articles(articles)
        build_site(articles, out_dir=DIST_DIR, master=master)
        if publish_pending_to_x(articles):
            save_articles(articles)
        print(f"[DONE] スプレッドシート同期＆サイト再生成が完了しました！ ({DIST_DIR / 'index.html'})")
    elif "--upgrade-drafts" in sys.argv:
        load_dotenv()
        master = load_product_master()
        articles = load_articles()
        site_base_url = (os.environ.get("SITE_BASE_URL") or "https://example.com").rstrip("/")
        if upgrade_legacy_articles(articles, site_base_url) > 0:
            articles = sync_with_google_sheets(articles)
            save_articles(articles)
            build_site(articles, out_dir=DIST_DIR, master=master)
            print("[DONE] 旧記事のアップグレードとサイト再生成が完了しました！")
        else:
            print("[INFO] アップグレード対象の旧記事はありませんでした。")
    else:
        run_pipeline()
