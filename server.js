/**
 * ハブのリモートブラウザ（プロキシの「直接」）
 *  サーバーで本物の Chrome を動かし、ページ全体を「縦長の絵（タイル）」にしてハブへ送る。
 *  ハブは絵を並べるだけなので、スクロールは手元でなめらか。押す・入力するときだけ、ここに送る。
 *
 *  POST /api/open  { url, w }            → 新しく開く（sid を返す）
 *  POST /api/act   { sid, a, ... }        → a: click(x,y) / fill(text,enter,tab) / type(text) / key(key) / pick(x,y,value) / back / fwd / reload / nav(url)
 *  POST /api/tiles { sid, from, to }      → まだ持っていない部分の絵
 *  POST /api/close { sid }
 *  GET  /ping                             → ok（起こしておく用）
 *
 *  本人確認: ハブ（Apps Script）が RB_SECRET で署名したチケット（Authorization: Bearer <payload>.<sig>）
 *  環境変数: RB_SECRET（必須・ハブのスクリプト プロパティと同じ値）／ CHROME_PATH ／ RB_MAX（同時に開ける数・既定 2）／ PORT
 */
'use strict';
const http = require('http'), crypto = require('crypto'), dns = require('dns').promises, net = require('net');
const puppeteer = require('puppeteer-core');

const PORT = Number(process.env.PORT) || 10000;
const SECRET = process.env.RB_SECRET || '';
const CHROME = process.env.CHROME_PATH || '/usr/bin/chromium';
const MAX_SESS = Math.max(1, Number(process.env.RB_MAX) || 2);
const ALLOW_LOCAL = process.env.RB_ALLOW_LOCAL === '1'; // 試すときだけ
const IDLE_MS = 5 * 60 * 1000;        // 5分さわらなければ閉じる
const VH = 900;                       // 画面の高さ = タイル1枚の高さ
const MAXH = 24000;                   // ページはここまで（長すぎるページの下は切る）
const QUALITY = 55;
const MAX_TILES = 6;                  // 1回に返すタイルの数
const sleep = ms => new Promise(r => setTimeout(r, ms));
const short = m => String(m || '').replace(/\s+/g, ' ').slice(0, 140);
class HttpErr extends Error { constructor(code, msg) { super(msg); this.code = code; } }

/* ===== 本人確認（チケット） ===== */
function verify(h) {
  const m = /^Bearer\s+([\w-]+)\.([\w-]+)$/.exec(h || ''); if (!m || !SECRET) return null;
  const sig = crypto.createHmac('sha256', SECRET).update(m[1]).digest('base64url');
  const a = Buffer.from(sig), b = Buffer.from(m[2]); if (a.length !== b.length || !crypto.timingSafeEqual(a, b)) return null;
  let o; try { o = JSON.parse(Buffer.from(m[1], 'base64url').toString('utf8')); } catch (e) { return null; }
  return o && typeof o.u === 'string' && o.u && Number(o.e) > Date.now() ? o : null;
}

/* ===== 学校や家の中のネットワーク（ローカル）には行かせない ===== */
function privIp(ip) {
  if (net.isIPv6(ip)) {
    const l = ip.toLowerCase(), m = /::ffff:(\d+\.\d+\.\d+\.\d+)$/.exec(l); if (m) return privIp(m[1]);
    return l === '::1' || l === '::' || /^(fc|fd|fe[89ab])/.test(l);
  }
  const [a, b] = ip.split('.').map(Number);
  return a === 0 || a === 10 || a === 127 || a >= 224 || (a === 100 && b >= 64 && b <= 127) || (a === 169 && b === 254) || (a === 172 && b >= 16 && b <= 31) || (a === 192 && b === 168);
}
const hostCache = new Map();
async function safeHost(h) {
  h = String(h || '').toLowerCase().replace(/^\[|\]$/g, '').replace(/\.$/, '');
  if (ALLOW_LOCAL) return true;
  if (!h || h === 'localhost' || /\.(localhost|local|internal)$/.test(h)) return false;
  if (net.isIP(h)) return !privIp(h);
  const c = hostCache.get(h); if (c && c.t > Date.now()) return c.ok;
  let ok = false; try { const r = await dns.lookup(h, { all: true }); ok = r.length > 0 && r.every(x => !privIp(x.address)); } catch (e) {}
  if (hostCache.size > 5000) hostCache.clear(); hostCache.set(h, { ok, t: Date.now() + 10 * 60 * 1000 });
  return ok;
}
async function checkUrl(u) {
  let x; try { x = new URL(String(u)); } catch (e) { throw new HttpErr(400, 'URL の形が正しくありません'); }
  if (!/^https?:$/.test(x.protocol)) throw new HttpErr(400, 'http・https のページだけ開けます');
  if (!(await safeHost(x.hostname))) throw new HttpErr(400, 'このアドレスには行けません（ローカルのネットワーク）');
  return x.href;
}

/* ===== Chrome ===== */
let browser = null, launching = null, lastUse = Date.now();
async function getBrowser() {
  if (browser && browser.connected) return browser;
  if (!launching) launching = puppeteer.launch({
    executablePath: CHROME, headless: true, defaultViewport: null,
    args: ['--no-sandbox', '--disable-setuid-sandbox', '--disable-dev-shm-usage', '--disable-gpu', '--no-first-run', '--no-zygote', '--disable-extensions',
      '--mute-audio', '--renderer-process-limit=' + (MAX_SESS + 1), '--js-flags=--max-old-space-size=192', '--lang=ja-JP', '--disable-background-networking',
      '--disable-features=Translate,MediaRouter,OptimizationHints', '--hide-scrollbars', '--font-render-hinting=none']
  }).then(b => { browser = b; launching = null; b.on('disconnected', () => { browser = null; sessions.clear(); }); return b; }, e => { launching = null; throw e; });
  return launching;
}

/* ===== 開いているページ（1人1つ〜。sid で呼ぶ） ===== */
const sessions = new Map();
async function closeS(s) { sessions.delete(s.sid); try { await s.ctx.close(); } catch (e) {} }
async function makeRoom(owner) {
  while (sessions.size >= MAX_SESS) {
    const all = [...sessions.values()].sort((a, b) => a.last - b.last);
    const mine = all.find(s => s.owner === owner), idle = all.find(s => Date.now() - s.last > 60 * 1000);
    const victim = mine || idle; if (!victim) throw new HttpErr(503, 'いま、ほかの人が使っていて満員です。少し待ってからやり直してください');
    await closeS(victim);
  }
}
async function newSession(owner, w) {
  await makeRoom(owner);
  const b = await getBrowser(), ctx = await b.createBrowserContext(), page = await ctx.newPage();
  const s = { sid: crypto.randomBytes(12).toString('base64url'), owner, ctx, page, w, v: 0, H: VH, last: Date.now(), q: Promise.resolve(), nav: false, cdp: null, note: '' };
  sessions.set(s.sid, s);
  await page.setViewport({ width: w, height: VH });
  const ua = (await b.userAgent()).replace(/HeadlessChrome/g, 'Chrome');
  await page.setUserAgent(ua);
  await page.setExtraHTTPHeaders({ 'Accept-Language': 'ja,en;q=0.8' });
  // 新しいタブ・窓で開くリンクは、同じ画面で開く
  await page.evaluateOnNewDocument(() => {
    document.addEventListener('click', e => { const a = e.target && e.target.closest && e.target.closest('a[target]'); if (a) a.target = '_self'; }, true);
    window.open = function (u) { if (u) location.href = new URL(u, location.href).href; return null; };
  });
  page.on('dialog', d => { s.note = (d.type() === 'beforeunload' ? '' : d.message() || '').slice(0, 300); d.type() === 'beforeunload' || d.type() === 'alert' ? d.accept().catch(() => {}) : d.dismiss().catch(() => {}); });
  ctx.on('targetcreated', async t => { try { if (t.type() !== 'page') return; const p = await t.page(); if (p && p !== page) await p.close(); } catch (e) {} });
  s.cdp = await page.createCDPSession();
  try { await s.cdp.send('Page.setDownloadBehavior', { behavior: 'deny' }); } catch (e) {}
  await page.setRequestInterception(true);
  page.on('request', async req => {
    if (req.isInterceptResolutionHandled()) return;
    try {
      const u = new URL(req.url());
      if (u.protocol === 'data:' || u.protocol === 'blob:') return req.continue();
      if (!/^https?:$/.test(u.protocol) || req.resourceType() === 'media') return req.abort('blockedbyclient');
      if (!(await safeHost(u.hostname))) return req.abort('accessdenied');
      if (req.isNavigationRequest() && req.frame() === page.mainFrame()) s.nav = true;
      return req.continue();
    } catch (e) { try { req.abort(); } catch (x) {} }
  });
  return s;
}

/* ===== 読み込みを待つ ===== */
async function waitDoc(p, ms) {
  const end = Date.now() + ms;
  while (Date.now() < end) { try { if ((await p.evaluate(() => document.readyState)) !== 'loading') return; } catch (e) {} await sleep(200); }
}
async function settle(p, ms) { try { await p.waitForNetworkIdle({ idleTime: 400, timeout: ms }); } catch (e) {} }
async function goto(s, url) {
  url = await checkUrl(url);
  try { await s.page.goto(url, { waitUntil: 'domcontentloaded', timeout: 25000 }); }
  catch (e) { if (!/timeout/i.test(e.message)) throw new HttpErr(502, 'ページを開けませんでした（' + short(e.message) + '）'); }
  await settle(s.page, 6000);
}

/* ===== 絵にする =====
 * 上に固定されたメニューなど（fixed・sticky）は、いまの場所に置いたままにする（絵の何枚にも写らないように） */
function freeze() {
  for (const el of document.querySelectorAll('body *')) {
    const cs = getComputedStyle(el);
    if (cs.position === 'fixed') { const r = el.getBoundingClientRect(); el.style.setProperty('position', 'absolute', 'important'); el.style.setProperty('top', (r.top + scrollY) + 'px', 'important'); el.style.setProperty('bottom', 'auto', 'important'); }
    else if (cs.position === 'sticky') el.style.setProperty('position', 'relative', 'important');
  }
}
async function capture(s, from, to) {
  const out = [], p = s.page; from = Math.max(0, Math.floor(Math.max(0, from) / VH) * VH); to = Math.min(s.H, Math.max(from + 1, to));
  for (let y = from; y < to && out.length < MAX_TILES; y += VH) {
    const sy = await p.evaluate(y => { scrollTo(0, y); return Math.round(scrollY); }, y);
    await sleep(80); try { await p.waitForNetworkIdle({ idleTime: 200, timeout: 1200 }); } catch (e) {} // あとから読み込まれる画像を少し待つ
    out.push({ y: sy, h: VH, img: await p.screenshot({ type: 'jpeg', quality: QUALITY, encoding: 'base64' }) });
    if (sy + VH >= s.H) break;
  }
  return out;
}
async function history(s) { try { const h = await s.cdp.send('Page.getNavigationHistory'); return { back: h.currentIndex > 0, fwd: h.currentIndex < h.entries.length - 1 }; } catch (e) { return { back: false, fwd: false }; } }
async function snap(s, o) {
  const p = s.page; s.v++;
  await p.evaluate(freeze).catch(() => {});
  const info = await p.evaluate(() => ({ H: Math.max(document.documentElement.scrollHeight, document.body ? document.body.scrollHeight : 0), title: document.title, url: location.href })).catch(() => ({ H: VH, title: '', url: p.url() }));
  s.H = Math.max(VH, Math.min(MAXH, info.H));
  const around = o && o.around != null ? o.around : 0;
  const tiles = await capture(s, around - VH * 1.5, around + VH * 2.5);
  const note = s.note; s.note = '';
  return Object.assign({ sid: s.sid, v: s.v, url: info.url, title: info.title, H: s.H, w: s.w, tile: VH, tiles, keep: !!(o && o.keep), note }, await history(s), o && o.focus ? { focus: o.focus } : {});
}

/* ===== 操作 ===== */
const KEYS = new Set(['Enter', 'Backspace', 'Delete', 'Tab', 'Escape', 'ArrowUp', 'ArrowDown', 'ArrowLeft', 'ArrowRight', 'Home', 'End', 'PageUp', 'PageDown', 'Space']);
async function focusInfo(p) {
  return p.evaluate(() => {
    const a = document.activeElement; if (!a || a === document.body) return null;
    const t = a.tagName, ed = a.isContentEditable || t === 'TEXTAREA' || (t === 'INPUT' && !/^(button|submit|checkbox|radio|range|color|file|image|reset|hidden)$/i.test(a.type));
    if (!ed) return null; const r = a.getBoundingClientRect();
    return { x: Math.round(r.left), y: Math.round(r.top + scrollY), w: Math.round(r.width), h: Math.round(r.height), pw: a.type === 'password', val: String(a.value != null ? a.value : a.textContent || '').slice(0, 2000), ph: String(a.placeholder || '').slice(0, 100), multi: t === 'TEXTAREA' || a.isContentEditable };
  }).catch(() => null);
}
async function place(p, y) { const sy = await p.evaluate(y => { scrollTo(0, Math.max(0, y - innerHeight / 2)); return scrollY; }, y); return y - sy; }
/* 何かしたあと: ページが移ったら上から、移らなければ、その場所のまわりを撮り直す */
async function after(s, fn, y) {
  const p = s.page, before = p.url(); s.nav = false;
  await fn(); await sleep(450);
  if (s.nav) { await waitDoc(p, 15000); await settle(p, 6000); return snap(s, { around: 0 }); }
  try { await p.waitForNetworkIdle({ idleTime: 300, timeout: 2500 }); } catch (e) {}
  const same = p.url().split('#')[0] === before.split('#')[0];
  return snap(s, same ? { around: y, keep: true, focus: await focusInfo(p) } : { around: 0 });
}
async function act(s, b) {
  const p = s.page, x = Math.max(0, Math.min(s.w, Number(b.x) || 0)), y = Math.max(0, Math.min(s.H, Number(b.y) || 0));
  switch (b.a) {
    case 'click': {
      const vy = await place(p, y);
      const sel = await p.evaluate((x, y) => { const e = document.elementFromPoint(x, y), s = e && e.closest && e.closest('select'); return s && !s.disabled ? { opts: [...s.options].slice(0, 400).map(o => [o.value, o.text.trim()]), val: s.value } : null; }, x, vy).catch(() => null);
      if (sel) return { sid: s.sid, v: s.v, select: sel, x, y }; // 選ぶ欄: ハブで選んでもらう
      return after(s, () => p.mouse.click(x, vy), y);
    }
    case 'pick': {
      const vy = await place(p, y);
      return after(s, () => p.evaluate((x, y, v) => { const e = document.elementFromPoint(x, y), s = e && e.closest && e.closest('select'); if (!s) return; s.focus(); s.value = v; s.dispatchEvent(new Event('input', { bubbles: true })); s.dispatchEvent(new Event('change', { bubbles: true })); }, x, vy, String(b.value || '')), y);
    }
    case 'fill': { // 入力欄の中身を入れかえる（ハブの手元の入力欄で書いたもの）。enter / tab で、そのあとキーも押す
      const f = await focusInfo(p); if (!f) throw new HttpErr(409, '入力する場所が見つかりませんでした。もう一度、入力欄を押してください');
      const t = String(b.text || '').slice(0, 5000);
      return after(s, async () => {
        await p.evaluate(() => { const a = document.activeElement; if (a.select) a.select(); else { const r = document.createRange(); r.selectNodeContents(a); const g = getSelection(); g.removeAllRanges(); g.addRange(r); } });
        if (t) await p.keyboard.sendCharacter(t); else await p.keyboard.press('Backspace');
        if (b.enter) await p.keyboard.press('Enter'); else if (b.tab) await p.keyboard.press('Tab');
      }, f.y);
    }
    case 'type': { const t = String(b.text || '').slice(0, 2000); const f = await focusInfo(p); return after(s, () => p.keyboard.type(t), f ? f.y : y); }
    case 'key': {
      const k = String(b.key || ''); if (!KEYS.has(k)) throw new HttpErr(400, 'そのキーは送れません');
      const f = await focusInfo(p); return after(s, () => p.keyboard.press(k === 'Space' ? ' ' : k), f ? f.y : y);
    }
    case 'back': case 'fwd': { s.nav = false; try { await (b.a === 'back' ? p.goBack({ waitUntil: 'domcontentloaded', timeout: 15000 }) : p.goForward({ waitUntil: 'domcontentloaded', timeout: 15000 })); } catch (e) {} await settle(p, 5000); return snap(s, { around: 0 }); }
    case 'reload': { try { await p.reload({ waitUntil: 'domcontentloaded', timeout: 20000 }); } catch (e) {} await settle(p, 5000); return snap(s, { around: 0 }); }
    case 'nav': await goto(s, b.url); return snap(s, { around: 0 });
    default: throw new HttpErr(400, '知らない操作です');
  }
}

/* ===== 受け付け ===== */
function readBody(req) {
  return new Promise((ok, ng) => { let n = 0; const c = []; req.on('data', d => { n += d.length; if (n > 65536) { ng(new HttpErr(413, '大きすぎます')); req.destroy(); } else c.push(d); }); req.on('end', () => ok(Buffer.concat(c).toString('utf8'))); req.on('error', ng); });
}
function own(b, who) { const s = sessions.get(String(b.sid || '')); if (!s || s.owner !== who.u) throw new HttpErr(410, 'ページが閉じられました。もう一度開いてください'); s.last = lastUse = Date.now(); return s; }
const queue = (s, fn) => (s.q = s.q.then(fn, fn)); // 1つのページへの操作は、順番に
async function route(path, b, who) {
  if (path === '/api/open') {
    const w = Math.max(360, Math.min(1400, Math.round(Number(b.w) || 1100)));
    const url = await checkUrl(b.url);
    if (b.sid && sessions.has(String(b.sid))) { const s = own(b, who); if (s.w !== w) { s.w = w; await s.page.setViewport({ width: w, height: VH }); } return queue(s, async () => { await goto(s, url); return snap(s, { around: 0 }); }); }
    const s = await newSession(who.u, w); lastUse = Date.now();
    return queue(s, async () => { await goto(s, url); return snap(s, { around: 0 }); });
  }
  if (path === '/api/act') { const s = own(b, who); return queue(s, () => act(s, b)); }
  if (path === '/api/tiles') { const s = own(b, who); return queue(s, async () => ({ sid: s.sid, v: s.v, H: s.H, tiles: await capture(s, Number(b.from) || 0, Number(b.to) || 0) })); }
  if (path === '/api/close') { const s = sessions.get(String(b.sid || '')); if (s && s.owner === who.u) await closeS(s); return { ok: true }; }
  throw new HttpErr(404, 'ありません');
}
http.createServer(async (req, res) => {
  res.setHeader('Access-Control-Allow-Origin', '*');
  res.setHeader('Access-Control-Allow-Headers', 'Authorization, Content-Type');
  res.setHeader('Access-Control-Allow-Methods', 'GET, POST, OPTIONS');
  res.setHeader('Access-Control-Max-Age', '86400');
  const path = (req.url || '/').split('?')[0];
  if (req.method === 'OPTIONS') { res.writeHead(204); res.end(); return; }
  if (req.method === 'GET' && (path === '/ping' || path === '/')) { res.writeHead(200, { 'Content-Type': 'text/plain' }); res.end('ok'); return; }
  const send = (code, o) => { res.writeHead(code, { 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store' }); res.end(JSON.stringify(o)); };
  if (req.method !== 'POST') { send(405, { error: 'POST だけです' }); return; }
  const who = verify(req.headers.authorization); if (!who) { send(401, { error: '本人確認ができませんでした（チケットが古いか、違います）' }); return; }
  try { const b = JSON.parse((await readBody(req)) || '{}'); send(200, await route(path, b, who)); }
  catch (e) { send(e.code || 500, { error: e.code ? e.message : 'サーバーでエラーが起きました（' + short(e.message) + '）' }); if (!e.code) console.error(e); }
}).listen(PORT, () => console.log('rbrowser on ' + PORT + (SECRET ? '' : '  ※ RB_SECRET がありません（だれも使えません）')));

/* 使っていないページを閉じる。だれも使っていなければ、Chrome も閉じてメモリをあける */
setInterval(async () => {
  for (const s of [...sessions.values()]) if (Date.now() - s.last > IDLE_MS) await closeS(s);
  if (browser && !sessions.size && Date.now() - lastUse > 10 * 60 * 1000) { const b = browser; browser = null; try { await b.close(); } catch (e) {} }
}, 30 * 1000);
