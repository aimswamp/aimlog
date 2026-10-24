/**
 * Googleスプレッドシート側 連携用スクリプト (Google Apps Script)
 *
 * 【使い方】
 * 1. 新しいGoogleスプレッドシートを作成
 * 2. 「拡張機能」＞「Apps Script」を開き、このコードを貼り付けて保存
 * 3. 「デプロイ」＞「新しいデプロイ」＞ 種類「ウェブアプリ」
 *    - 次のユーザーとして実行: 「自分」
 *    - アクセスできるユーザー: 「全員」
 * 4. 発行されたウェブアプリURLを `.env`（およびGitHub Secrets）の `GAS_WEBHOOK_URL` に設定するだけ！
 *
 * シートの B列 (`status`) をプルダウンで `draft` から `published` に変えると、
 * 次回パイプライン実行時に自動でWebサイト公開＆X投稿が行われます。
 */

const SHEET_NAME = 'Articles';
const HEADERS = [
  'id',
  'status',          // 👈 ここをプルダウンで 'draft' から 'published' に変えるだけ！
  'subreddit',
  'title_ja',        // 👈 シート上でタイトルを微修正するとサイト側にも反映されます
  'hook_ja',         // 👈 シート上で要約フックを微修正するとサイト側にも反映されます
  'x_intent_url',    // 👈 スマホ/PCからワンクリックでX投稿画面を開くリンク
  'article_url',
  'devices_summary',
  'created_at',
  'meta_json'        // 軽量メタデータ保持列（50,000文字制限を回避）
];

function getOrCreateSheet() {
  const ss = SpreadsheetApp.getActiveSpreadsheet();
  let sheet = ss.getSheetByName(SHEET_NAME);
  if (!sheet) {
    sheet = ss.insertSheet(SHEET_NAME);
    sheet.appendRow(HEADERS);
    sheet.setFrozenRows(1);
    sheet.getRange(1, 1, 1, HEADERS.length).setFontWeight('bold');
  }
  return sheet;
}

function applyStatusDropdown(sheet, rowCount) {
  if (rowCount < 2) return;
  const rule = SpreadsheetApp.newDataValidation()
    .requireValueInList(['draft', 'published', 'rejected'], true)
    .setAllowInvalid(true)
    .build();
  sheet.getRange(2, 2, rowCount - 1, 1).setDataValidation(rule);
}

// ブラウザでURLを開いたときの疎通確認用
function doGet() {
  const sheet = getOrCreateSheet();
  const rowCount = Math.max(0, sheet.getLastRow() - 1);
  return ContentService
    .createTextOutput(JSON.stringify({
      status: 'ok',
      message: 'エイム沼の海外ログ GAS Webhook is active!',
      article_count: rowCount
    }))
    .setMimeType(ContentService.MimeType.JSON);
}

function doPost(e) {
  const sheet = getOrCreateSheet();
  const payload = JSON.parse(e.postData.contents || '{}');
  const incoming = payload.articles || [];

  const rows = sheet.getDataRange().getValues();
  const existingMap = {};

  // シート上の現在のステータス・編集済みタイトル等を読み取る（人間の編集を優先）
  for (let i = 1; i < rows.length; i++) {
    const id = String(rows[i][0] || '').trim();
    if (!id) continue;
    const status = String(rows[i][1] || 'draft').trim();
    const subreddit = String(rows[i][2] || '').trim();
    const titleJa = String(rows[i][3] || '').trim();
    const hookJa = String(rows[i][4] || '').trim();
    const xIntentUrl = String(rows[i][5] || '').trim();
    const articleUrl = String(rows[i][6] || '').trim();
    const createdAt = String(rows[i][8] || '').trim();
    const rawMeta = String(rows[i][9] || '');

    let obj = {};
    if (rawMeta) {
      try {
        obj = JSON.parse(rawMeta);
      } catch (_) {}
    }
    obj.id = id;
    obj.status = status || obj.status || 'draft';
    if (subreddit) obj.subreddit = subreddit;
    if (titleJa) obj.title_ja = titleJa;
    if (hookJa) obj.hook_ja = hookJa;
    if (xIntentUrl) obj.x_intent_url = xIntentUrl;
    if (articleUrl) obj.article_url = articleUrl;
    if (createdAt) obj.created_at = createdAt;

    existingMap[id] = { rowIndex: i + 1, data: obj };
  }

  // パイプラインから送られてきた記事をマージ
  incoming.forEach(art => {
    const id = String(art.id || '').trim();
    if (!id) return;
    const devicesSummary = Array.isArray(art.devices)
      ? art.devices.map(d => d.name).filter(Boolean).join(', ')
      : String(art.devices_summary || '');

    // セル文字数上限(50,000字)を超えないよう、長文ツリー等を除いた軽量メタデータのみJSON保持
    const lightMeta = {
      id: id,
      status: art.status || 'draft',
      subreddit: art.subreddit || '',
      title_ja: art.title_ja || '',
      hook_ja: art.hook_ja || '',
      x_intent_url: art.x_intent_url || '',
      article_url: art.article_url || '',
      devices_summary: devicesSummary,
      created_at: art.created_at || ''
    };

    if (existingMap[id]) {
      const prev = existingMap[id].data;
      // シート側で人間が変更した status / title_ja / hook_ja を優先維持
      lightMeta.status = prev.status || lightMeta.status;
      if (prev.title_ja) lightMeta.title_ja = prev.title_ja;
      if (prev.hook_ja) lightMeta.hook_ja = prev.hook_ja;

      const r = existingMap[id].rowIndex;
      sheet.getRange(r, 1, 1, HEADERS.length).setValues([[
        id,
        lightMeta.status,
        lightMeta.subreddit,
        lightMeta.title_ja,
        lightMeta.hook_ja,
        lightMeta.x_intent_url,
        lightMeta.article_url,
        devicesSummary,
        lightMeta.created_at,
        JSON.stringify(lightMeta)
      ]]);
      existingMap[id].data = lightMeta;
    } else {
      sheet.appendRow([
        id,
        lightMeta.status,
        lightMeta.subreddit,
        lightMeta.title_ja,
        lightMeta.hook_ja,
        lightMeta.x_intent_url,
        lightMeta.article_url,
        devicesSummary,
        lightMeta.created_at,
        JSON.stringify(lightMeta)
      ]);
      existingMap[id] = { data: lightMeta };
    }
  });

  applyStatusDropdown(sheet, sheet.getLastRow());

  const mergedArticles = Object.keys(existingMap).map(k => existingMap[k].data);
  return ContentService
    .createTextOutput(JSON.stringify({ status: 'ok', articles: mergedArticles }))
    .setMimeType(ContentService.MimeType.JSON);
}
