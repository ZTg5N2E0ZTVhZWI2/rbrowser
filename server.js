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
const http = require('http'), https = require('https'), crypto = require('crypto'), dns = require('dns').promises, net = require('net'), zlib = require('zlib');
const puppeteer = require('puppeteer-core');

const PORT = Number(process.env.PORT) || 10000;
const SECRET = process.env.RB_SECRET || '';
const CHROME = process.env.CHROME_PATH || '/usr/bin/chromium';
const MAX_SESS = Math.max(1, Number(process.env.RB_MAX) || 2);
const ALLOW_LOCAL = process.env.RB_ALLOW_LOCAL === '1'; // 試すときだけ
const IDLE_MS = 5 * 60 * 1000;        // 5分さわらなければ閉じる
const VH = 900;                       // 画面の高さ = タイル1枚の高さ
const MAXH = 24000;                   // ページはここまで（長すぎるページの下は切る）
const QUALITY = 50;
const SLOW = Number(process.env.RB_SLOW) || 0; // 試すときだけ: CPU を遅くする（無料のサーバーのまね）
// 広告・計測（重いだけで、見るものではない）は読み込まない
const ADS = /(^|\.)(doubleclick\.net|googlesyndication\.com|googleadservices\.com|google-analytics\.com|googletagmanager\.com|googletagservices\.com|adservice\.google\.[a-z.]+|amazon-adsystem\.com|facebook\.net|scorecardresearch\.com|criteo\.(com|net)|taboola\.com|outbrain\.com|adnxs\.com|rubiconproject\.com|pubmatic\.com|openx\.net|casalemedia\.com|hotjar\.com|clarity\.ms|yads\.yahoo\.co\.jp|i-mobile\.co\.jp|microad\.jp|adingo\.jp|fout\.jp|logly\.co\.jp|popin\.cc|ad-stir\.com|socdm\.com|teads\.tv|moatads\.com|quantserve\.com|adsrvr\.org|bidswitch\.net|smartadserver\.com)$/i;
const UA_RES = 'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130.0.0.0 Safari/537.36';
const MAX_TILES = 6;                 // 1回に返すタイルの数
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
let browser = null, launching = null, lastUse = Date.now(), busy = 0;
function chromeEnv() { const e = Object.assign({}, process.env); for (const k of Object.keys(e)) if (/SECRET|TOKEN|KEY|PASS/i.test(k)) delete e[k]; return e; }
async function getBrowser() {
  if (browser && browser.connected) return browser;
  if (!launching) launching = puppeteer.launch({
    executablePath: CHROME, headless: true, defaultViewport: null,
    env: chromeEnv(), // Chrome には合言葉（RB_SECRET）を渡さない（もし悪いページに Chrome が乗っ取られても、読めないように）
    args: ['--no-sandbox', '--disable-setuid-sandbox', '--disable-dev-shm-usage', '--disable-gpu', '--no-first-run', '--no-zygote', '--disable-extensions',
      '--mute-audio', '--renderer-process-limit=' + (MAX_SESS + 1), '--js-flags=--max-old-space-size=192', '--lang=ja-JP', '--disable-background-networking',
      '--disable-features=Translate,MediaRouter,OptimizationHints', '--hide-scrollbars', '--font-render-hinting=none']
  }).then(b => { browser = b; launching = null; b.on('disconnected', () => { browser = null; sessions.clear(); spare = null; }); return b; }, e => { launching = null; throw e; });
  return launching;
}

/* ===== 開いているページ（1人1つ〜。sid で呼ぶ） ===== */
const sessions = new Map(), byRk = new Map(); // byRk: 画像などを取る合言葉 → ページ
async function closeS(s) { sessions.delete(s.sid); byRk.delete(s.rk); try { await s.ctx.close(); } catch (e) {} }
async function makeRoom(owner) {
  while (sessions.size >= MAX_SESS) {
    const all = [...sessions.values()].sort((a, b) => a.last - b.last);
    const mine = all.find(s => s.owner === owner), idle = all.find(s => Date.now() - s.last > 60 * 1000);
    const victim = mine || idle; if (!victim) throw new HttpErr(503, 'いま、ほかの人が使っていて満員です。少し待ってからやり直してください');
    await closeS(victim);
  }
}
/* 次の人のために、空のページを1つ用意しておく（開くときの「準備」の数秒をなくす） */
let spare = null, spareMaking = null;
function makeSpare() {
  if (spare || spareMaking) return;
  spareMaking = prepare(1100).then(s => { spare = s; spareMaking = null; }, e => { spareMaking = null; console.error('spare', e.message); });
}
async function takeSpare() {
  if (!spare && spareMaking) await spareMaking;
  const s = spare; spare = null;
  if (s && s.page && !s.page.isClosed() && browser && browser.connected) return s;
  if (s) try { await s.ctx.close(); } catch (e) {}
  return null;
}
async function newSession(owner, w) {
  await makeRoom(owner);
  let s = await takeSpare();
  if (s) { if (s.w !== w) { s.w = w; await s.page.setViewport({ width: w, height: VH }); } } else s = await prepare(w);
  s.owner = owner; s.last = Date.now(); sessions.set(s.sid, s); byRk.set(s.rk, s);
  return s;
}
async function prepare(w) {
  const b = await getBrowser(), ctx = await b.createBrowserContext(), page = await ctx.newPage();
  const s = { sid: crypto.randomBytes(12).toString('base64url'), rk: crypto.randomBytes(16).toString('base64url'), owner: null, ctx, page, w, v: 0, H: VH, last: Date.now(), q: Promise.resolve(), nav: false, cdp: null, note: '', ms: {}, mode: 'tiles', res: '' };
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
  if (SLOW) try { await s.cdp.send('Emulation.setCPUThrottlingRate', { rate: SLOW }); } catch (e) {}
  await page.setRequestInterception(true);
  page.on('request', async req => {
    if (req.isInterceptResolutionHandled()) return;
    try {
      const u = new URL(req.url());
      if (u.protocol === 'data:' || u.protocol === 'blob:') return req.continue();
      if (!/^https?:$/.test(u.protocol) || req.resourceType() === 'media' || ADS.test(u.hostname)) return req.abort('blockedbyclient');
      // 中身のまま送るとき: 画像・フォントは、ハブの側が（このサーバーの /r/ を通して）読み込むので、ここの Chrome では読み込まない（見た目は同じ・速くなる）
      if (s.mode === 'dom' && (req.resourceType() === 'image' || req.resourceType() === 'font')) return req.abort('blockedbyclient');
      // Apps Script が取ってきたページ・CSS は、それを返す（サイトへは取りにいかない）
      const g = s.given, ru = req.url().split('#')[0];
      if (g) {
        if (!g.used && req.method() === 'GET' && req.isNavigationRequest() && req.frame() === page.mainFrame() && ru === g.url) { g.used = true; s.nav = true; return req.respond({ status: 200, contentType: 'text/html; charset=utf-8', body: g.html }); }
      }
      if (s.css && req.method() === 'GET' && req.resourceType() === 'stylesheet' && s.css.has(ru)) return req.respond({ status: 200, contentType: 'text/css; charset=utf-8', headers: { 'Access-Control-Allow-Origin': '*' }, body: s.css.get(ru) });
      if (!(await safeHost(u.hostname))) return req.abort('accessdenied');
      if (req.isNavigationRequest() && req.frame() === page.mainFrame()) s.nav = true;
      return req.continue();
    } catch (e) { try { req.abort(); } catch (x) {} }
  });
  // DNS のすりかえ（確かめたときは外のアドレス、Chrome がつなぐときは中のアドレス）への備え:
  // 実際につないだ先が中のアドレスだったら、そのページはすぐ閉じる
  page.on('response', r => {
    if (ALLOW_LOCAL) return;
    const a = r.remoteAddress && r.remoteAddress(); if (!a || !a.ip || !privIp(String(a.ip).replace(/^\[|\]$/g, ''))) return;
    console.error('blocked private address', a.ip); s.bad = true; closeS(s).catch(() => {});
  });
  return s;
}

/* ===== 読み込みを待つ ===== */
async function waitDoc(p, ms) {
  const end = Date.now() + ms;
  while (Date.now() < end) { try { if ((await p.evaluate(() => document.readyState)) !== 'loading') return; } catch (e) {} await sleep(200); }
}
async function settle(p, ms) { try { await p.waitForNetworkIdle({ idleTime: 300, timeout: ms }); } catch (e) {} }
/* 1画面目が見られるようになったか（新しいページで、最初の絵がかかれていて、見た目の CSS がそろっている）
 * ※ 大きさ（scrollHeight・innerText）を聞くと、ページ全体の並べ直しが走って遅くなるので、聞かない */
function early() {
  if (window.__rbOld || !document.body || document.body.childElementCount < 1) return false;
  if (!performance.getEntriesByName('first-contentful-paint').length) return false;
  return [...document.querySelectorAll('link[rel~="stylesheet"]')].every(l => l.sheet || l.disabled || (l.media && !matchMedia(l.media).matches));
}
/* ページ全部の読み込み（大きなページは、とても時間がかかる）を待たず、1画面目が見られたら先に返す。残りは、スクロールしたときに撮る */
async function goto(s, url) {
  const tc = Date.now(); url = await checkUrl(url); const p = s.page;
  await p.evaluate(() => { window.__rbOld = 1; }).catch(() => {}); s.ms.pre = Date.now() - tc; const t0 = Date.now();
  let done = false, err = null;
  const nav = p.goto(url, { waitUntil: 'domcontentloaded', timeout: 25000 }).then(() => { done = true; }, e => { done = true; if (!/timeout/i.test(e.message)) err = e; });
  while (!done) {
    await Promise.race([nav, sleep(400)]);
    if (!done && s.mode !== 'dom' && Date.now() - t0 > 1200 && await p.evaluate(early).catch(() => false)) break;
  }
  if (err) throw new HttpErr(502, 'ページを開けませんでした（' + short(err.message) + '）');
  s.ms.load = Date.now() - t0; s.ms.early = !done;
  await settle(p, done ? (s.given ? 2000 : 3000) : 1200); s.ms.settle = Date.now() - t0 - s.ms.load;
}
async function pageH(s) {
  const h = await s.page.evaluate(() => Math.max(document.documentElement.scrollHeight, document.body ? document.body.scrollHeight : 0)).catch(() => 0);
  if (h) s.H = Math.max(VH, Math.min(MAXH, h));
  return s.H;
}

/* ===== 絵にする =====
 * 上に固定されたメニューなど（fixed・sticky）は、いまの場所に置いたままにする（絵の何枚にも写らないように） */
function freeze(force) {
  if (window.__rbFrozen && !force) return; window.__rbFrozen = 1;
  for (const el of document.querySelectorAll('body *')) {
    const cs = getComputedStyle(el);
    if (cs.position === 'fixed') { const r = el.getBoundingClientRect(); el.style.setProperty('position', 'absolute', 'important'); el.style.setProperty('top', (r.top + scrollY) + 'px', 'important'); el.style.setProperty('bottom', 'auto', 'important'); }
    else if (cs.position === 'sticky') el.style.setProperty('position', 'relative', 'important');
  }
}
async function capture(s, from, to) {
  const out = [], p = s.page; from = Math.max(0, Math.floor(Math.max(0, from) / VH) * VH); to = Math.min(s.H, Math.max(from + 1, to));
  for (let y = from; y < to && out.length < MAX_TILES; y += VH) {
    if (y > 0) await p.evaluate(freeze, false).catch(() => {}); // 一番上のときは、固定のものも、もとの場所にあるので、そのままでよい
    const sy = await p.evaluate(y => { scrollTo(0, y); return Math.round(scrollY); }, y);
    await p.evaluate(() => new Promise(done => { // 画面に見えている画像が読み込み中なら、少し（1秒まで）待つ
      const vis = [...document.images].filter(i => { if (i.complete) return false; const r = i.getBoundingClientRect(); return r.bottom > 0 && r.top < innerHeight && r.width > 0; });
      if (!vis.length) return requestAnimationFrame(() => done());
      let n = vis.length; const one = () => { if (--n <= 0) done(); }; vis.forEach(i => { i.addEventListener('load', one, { once: true }); i.addEventListener('error', one, { once: true }); }); setTimeout(done, 1000);
    })).catch(() => {});
    out.push({ y: sy, h: VH, img: await p.screenshot({ type: 'jpeg', quality: QUALITY, encoding: 'base64', optimizeForSpeed: true }) });
    if (sy + VH >= s.H) break;
  }
  return out;
}
/* ===== 中身のまま送る（mode: 'dom'） =====
 * サーバーの Chrome で動かしたあとのページ（JavaScript で作られた部分も入る）を HTML にして送る。
 * ハブは、スクリプトを動かさない箱の中に、それをそのまま出す（文字が選べる・コピーできる・手元でスクロール・入力できる）。
 * 押せるもの（リンク・ボタンなど）には番号（data-rbi）を付け、押されたら、サーバーの本物のページの、その番号のものを押す。
 * 画像・CSS・フォントは、このサーバーの /r/ を通して取る（学校などでサイトに直接つながらなくても出るように） */
function domSer(pfx) {
  const abs = u => { try { return new URL(u, document.baseURI).href; } catch (e) { return ''; } };
  const R = u => { // 画像など: このサーバーを通す
    u = String(u || '').trim(); if (!u) return '';
    if (/^data:/i.test(u)) return u; if (/^(blob|about|javascript|file):/i.test(u)) return '';
    const a = abs(u); return pfx && /^https?:/i.test(a) ? pfx + encodeURIComponent(a) : a;
  };
  const cssFix = t => String(t || '')
    .replace(/url\(\s*(['"]?)(.*?)\1\s*\)/gi, (m, q, u) => /^(data:|#)/i.test(u) ? m : 'url("' + R(u).replace(/"/g, '%22') + '")')
    .replace(/@import\s+(['"])(.*?)\1/gi, (m, q, u) => '@import url("' + R(u).replace(/"/g, '%22') + '")');
  const srcset = v => String(v || '').split(/,\s+/).map(p => { const t = p.trim().split(/\s+/); t[0] = R(t[0]); return t.join(' '); }).join(', ');
  const LINKS = { A: 'href', AREA: 'href', FORM: 'action' }, ROLE = /^(button|link|tab|menuitem|menuitemcheckbox|menuitemradio|option|checkbox|radio|switch|treeitem)$/;
  const root = document.documentElement, live = [root, ...root.querySelectorAll('*')];
  const clone = root.cloneNode(true), cl = [clone, ...clone.querySelectorAll('*')];
  const els = []; window.__rbEls = els; const kill = [], swap = [];
  const cur = new Map(), pointer = el => { // 指の形のカーソル = 押せるもの（JavaScript で押せるようにした div など）
    if (cur.has(el)) return cur.get(el); let v = false; try { v = getComputedStyle(el).cursor === 'pointer'; } catch (e) {} cur.set(el, v); return v;
  };
  const MAYBE = /^(DIV|SPAN|LI|IMG|I|P|TD|TR|TH|SECTION|ARTICLE|SVG|H[1-6]|FIGURE|PICTURE|STRONG|B|EM|UL|NAV|HEADER|FOOTER|ASIDE|MAIN|DT|DD)$/;
  const INSIDE = 'a,button,label,summary,select,[onclick],[role="button"],[role="link"]';
  for (let i = 0; i < live.length && i < cl.length; i++) {
    const L = live[i], C = cl[i], tag = L.tagName.toUpperCase();
    if (/^(SCRIPT|NOSCRIPT|OBJECT|EMBED|BASE|TEMPLATE|APPLET|PORTAL)$/.test(tag) || (tag === 'META' && L.httpEquiv) || (tag === 'LINK' && !/(^|\s)(stylesheet|icon)(\s|$)/i.test(L.rel || ''))) { kill.push(C); continue; }
    for (const at of [...C.attributes]) { // 動くもの（on〜・javascript:）は外す
      const n = at.name.toLowerCase();
      if (n.startsWith('on') || n === 'integrity' || n === 'nonce' || n === 'crossorigin' || /^\s*javascript:/i.test(at.value)) C.removeAttribute(at.name);
    }
    if (C.hasAttribute('style')) C.setAttribute('style', cssFix(C.getAttribute('style')));
    if (LINKS[tag] && C.hasAttribute(LINKS[tag])) C.setAttribute(LINKS[tag], abs(C.getAttribute(LINKS[tag])));
    if (C.hasAttribute('formaction')) C.setAttribute('formaction', abs(C.getAttribute('formaction')));
    if (C.hasAttribute('background')) C.setAttribute('background', R(C.getAttribute('background')));
    if (tag === 'IMG') {
      let src = L.currentSrc || L.getAttribute('src') || '';
      const lazy = L.getAttribute('data-src') || L.getAttribute('data-lazy-src') || L.getAttribute('data-original');
      if (lazy && (!L.currentSrc || /^data:/i.test(src))) src = lazy;
      C.setAttribute('src', R(src)); C.removeAttribute('srcset'); C.removeAttribute('sizes');
      if (!L.currentSrc && L.getAttribute('data-srcset')) C.setAttribute('srcset', srcset(L.getAttribute('data-srcset')));
      else if (!L.currentSrc && L.getAttribute('srcset')) C.setAttribute('srcset', srcset(L.getAttribute('srcset')));
    } else if (tag === 'SOURCE') { if (C.hasAttribute('srcset')) C.setAttribute('srcset', srcset(C.getAttribute('srcset'))); if (C.hasAttribute('src')) C.setAttribute('src', R(C.getAttribute('src'))); }
    else if (tag === 'LINK') C.setAttribute('href', R(L.href));
    else if (tag === 'STYLE') { let t = ''; try { t = [...L.sheet.cssRules].map(r => r.cssText).join('\n'); } catch (e) { t = L.textContent; } C.textContent = cssFix(t); }
    else if (tag === 'VIDEO' || tag === 'AUDIO') { C.removeAttribute('src'); C.removeAttribute('autoplay'); C.querySelectorAll('source').forEach(x => x.remove()); if (C.hasAttribute('poster')) C.setAttribute('poster', R(C.getAttribute('poster'))); }
    else if (tag === 'IMAGE' || tag === 'USE' || tag === 'FEIMAGE') { for (const n of ['href', 'xlink:href']) { const v = C.getAttribute(n); if (v && v[0] !== '#') C.setAttribute(n, R(v)); } }
    else if (tag === 'IFRAME' || tag === 'FRAME') { const r = L.getBoundingClientRect(); swap.push([C, 'f', Math.round(r.width), Math.round(r.height), abs(L.getAttribute('src') || '')]); }
    else if (tag === 'CANVAS') { try { swap.push([C, 'c', L.width, L.height, L.toDataURL()]); } catch (e) {} }
    else if (tag === 'INPUT') {
      if (L.type === 'checkbox' || L.type === 'radio') L.checked ? C.setAttribute('checked', '') : C.removeAttribute('checked');
      else if (L.type === 'image') C.setAttribute('src', R(L.getAttribute('src')));
      else if (L.type !== 'file') C.setAttribute('value', L.type === 'password' ? '' : L.value);
    }
    else if (tag === 'TEXTAREA') C.textContent = L.value;
    else if (tag === 'OPTION') L.selected ? C.setAttribute('selected', '') : C.removeAttribute('selected');
    else if (tag === 'DETAILS') L.open ? C.setAttribute('open', '') : C.removeAttribute('open');
    // 押せるもの: 番号を付ける
    const role = (L.getAttribute('role') || '').toLowerCase(), ti = L.getAttribute('tabindex');
    if (/^(A|BUTTON|INPUT|SELECT|TEXTAREA|SUMMARY|LABEL)$/.test(tag) || L.onclick || L.hasAttribute('onclick') || ROLE.test(role) || (ti !== null && Number(ti) >= 0) ||
      (MAYBE.test(tag) && L !== document.body && !(L.parentElement && L.parentElement.closest(INSIDE)) && pointer(L) && !(L.parentElement && pointer(L.parentElement)))) { C.setAttribute('data-rbi', els.length); els.push(L); }
  }
  kill.forEach(c => c.remove());
  for (const [C, k, w, h, v] of swap) {
    const n = document.createElement(k === 'c' ? 'img' : 'div');
    if (k === 'c') { n.src = v; n.width = w; n.height = h; n.setAttribute('style', C.getAttribute('style') || ''); n.className = C.className; }
    else { n.setAttribute('style', 'display:flex;align-items:center;justify-content:center;flex-direction:column;gap:6px;box-sizing:border-box;border:1px dashed #94a3b8;background:#f1f5f9;color:#475569;font:13px sans-serif;padding:8px;text-align:center;width:' + Math.max(w, 120) + 'px;max-width:100%;height:' + Math.max(h, 60) + 'px'); n.textContent = '（ここには埋め込みがあります。このモードでは出せません）'; if (/^https?:/i.test(v)) { const a = document.createElement('a'); a.href = v; a.textContent = 'それだけを開く'; a.setAttribute('data-rbnav', '1'); n.appendChild(a); } }
    C.replaceWith(n);
  }
  const head = clone.querySelector('head') || clone.insertBefore(document.createElement('head'), clone.firstChild);
  const base = document.createElement('base'); base.href = location.href; head.insertBefore(base, head.firstChild);
  const mc = document.createElement('meta'); mc.setAttribute('charset', 'utf-8'); head.insertBefore(mc, head.firstChild);
  try { for (const sh of document.adoptedStyleSheets || []) { const st = document.createElement('style'); st.textContent = cssFix([...sh.cssRules].map(r => r.cssText).join('\n')); head.appendChild(st); } } catch (e) {}
  return (document.doctype ? '<!DOCTYPE html>' : '') + clone.outerHTML;
}
async function domSnap(s, o) {
  const p = s.page; s.v++; const t0 = Date.now();
  const pfx = s.res ? s.res + '/r/' + s.rk + '/' : '';
  let html = '';
  for (let k = 0; k < 2 && !html; k++) {
    try { html = await p.evaluate(domSer, pfx); }
    catch (e) { if (k) throw new HttpErr(502, 'ページを読み取れませんでした（' + short(e.message) + '）'); await waitDoc(p, 10000); }
  }
  s.ms.ser = Date.now() - t0;
  if (html.length > 15e6) throw new HttpErr(413, 'ページが大きすぎて送れません。プロキシで開いてください');
  const info = await p.evaluate(() => ({ title: document.title, url: location.href })).catch(() => ({ title: '', url: p.url() }));
  const note = s.note; s.note = ''; const ms = s.ms; s.ms = {};
  return Object.assign({ sid: s.sid, v: s.v, mode: 'dom', url: info.url, title: info.title, html, keep: !!(o && o.keep), note, ms }, await history(s));
}
/* ハブで書きかえた入力欄の中身を、本物のページへ（React などでも効くように、本来の書き方で） */
async function applyVals(p, vals) {
  if (!vals || typeof vals !== 'object') return;
  const v = {}; let n = 0;
  for (const k of Object.keys(vals)) { if (++n > 500) break; const o = vals[k] || {}; if (!/^\d+$/.test(k)) continue; v[k] = 'c' in o ? { c: !!o.c } : { v: String(o.v == null ? '' : o.v).slice(0, 20000) }; }
  await p.evaluate(v => {
    for (const k in v) {
      const el = (window.__rbEls || [])[k], o = v[k]; if (!el || !el.isConnected) continue;
      if ('c' in o) { if (el.checked !== o.c) el.click(); continue; }
      if (el.value === o.v) continue;
      const proto = el.tagName === 'TEXTAREA' ? HTMLTextAreaElement.prototype : el.tagName === 'SELECT' ? HTMLSelectElement.prototype : HTMLInputElement.prototype;
      const d = Object.getOwnPropertyDescriptor(proto, 'value'); try { d.set.call(el, o.v); } catch (e) { el.value = o.v; }
      el.dispatchEvent(new Event('input', { bubbles: true })); el.dispatchEvent(new Event('change', { bubbles: true }));
    }
  }, v).catch(() => {});
}
/* 番号 i のものを押す（見えていれば本物のマウスで。隠れていれば click()） */
async function clickEl(p, i) {
  const pt = await p.evaluate(i => {
    const el = (window.__rbEls || [])[i]; if (!el || !el.isConnected) return 'gone';
    el.scrollIntoView({ block: 'center', inline: 'center' }); const r = el.getBoundingClientRect(), x = r.left + r.width / 2, y = r.top + r.height / 2;
    const at = r.width > 0 && r.height > 0 && document.elementFromPoint(x, y);
    if (at && (at === el || el.contains(at))) return { x, y };
    el.click(); return 'done';
  }, Number(i)).catch(() => 'gone');
  if (pt === 'gone') throw new HttpErr(409, 'ページが変わっていました。もう一度押してください');
  if (pt !== 'done') await p.mouse.click(pt.x, pt.y);
}
async function history(s) { try { const h = await s.cdp.send('Page.getNavigationHistory'); return { back: h.currentIndex > 0, fwd: h.currentIndex < h.entries.length - 1 }; } catch (e) { return { back: false, fwd: false }; } }
async function snap(s, o) {
  if (s.mode === 'dom') return domSnap(s, o);
  const p = s.page; s.v++; const t0 = Date.now();
  const around = o && o.around != null ? o.around : 0;
  if (around > 0) await p.evaluate(freeze, true).catch(() => {}); s.ms.freeze = Date.now() - t0; // 押したあとなど: 新しく出てきた固定のものも止める
  const info = await p.evaluate(() => ({ H: Math.max(document.documentElement.scrollHeight, document.body ? document.body.scrollHeight : 0), title: document.title, url: location.href })).catch(() => ({ H: VH, title: '', url: p.url() }));
  s.H = Math.max(VH, Math.min(MAXH, info.H)); s.ms.info = Date.now() - t0;
  // 新しいページは1画面目だけ（すぐ見せる）。続きは、ハブがすぐに取りにくる
  const t1 = Date.now(), tiles = around > 0 ? await capture(s, around - VH, around + VH * 1.2) : await capture(s, 0, 1); s.ms.cap = Date.now() - t1;
  const note = s.note; s.note = '';
  const ms = s.ms; s.ms = {}; const t2 = Date.now(), hi = await history(s); ms.hist = Date.now() - t2;
  return Object.assign({ sid: s.sid, v: s.v, url: info.url, title: info.title, H: s.H, w: s.w, tile: VH, tiles, keep: !!(o && o.keep), note, ms }, hi, o && o.focus ? { focus: o.focus } : {});
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
  return snap(s, same ? { around: y, keep: true, focus: s.mode === 'dom' ? null : await focusInfo(p) } : { around: 0 });
}
async function act(s, b) {
  const p = s.page, x = Math.max(0, Math.min(s.w, Number(b.x) || 0)), y = Math.max(0, Math.min(s.H, Number(b.y) || 0));
  if (s.mode === 'dom') {
    await applyVals(p, b.vals);
    const i = Number(b.i);
    if (b.a === 'click' && i >= 0) return after(s, () => clickEl(p, i), 0);
    if (b.a === 'enter' && i >= 0) return after(s, async () => { await p.evaluate(i => { const el = (window.__rbEls || [])[i]; if (el) el.focus(); }, i).catch(() => {}); await p.keyboard.press('Enter'); }, 0);
    if (b.a === 'set') return after(s, async () => {}, 0);
  }
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

/* ===== 画像・CSS・フォントの中継（GET /r/<合言葉>/<URL>） =====
 * 合言葉は、開いているページごとのもの（HTML の中にだけ書いてある）。ページを閉じると使えなくなる。
 * 行き先は毎回確かめ、つなぐときの DNS の答えも確かめる（中のアドレスへは行かない）。ページ（HTML）やスクリプトは返さない */
const RES_MAX = 12 * 1024 * 1024;
const RES_OK = /^(image\/|font\/|text\/css|application\/(font|x-font|vnd\.ms-fontobject|octet-stream))/i;
function safeLookup(host, opts, cb) {
  if (typeof opts === 'function') { cb = opts; opts = {}; }
  dns.lookup(host, { all: true }).then(r => {
    if (!r.length || (!ALLOW_LOCAL && r.some(x => privIp(x.address)))) return cb(Object.assign(new Error('blocked address'), { code: 'EBLOCKED' }));
    if (opts && opts.all) cb(null, r); else cb(null, r[0].address, r[0].family);
  }, cb);
}
function getRes(u, ref, hop) {
  return new Promise((ok, ng) => {
    const x = new URL(u), mod = x.protocol === 'https:' ? https : http;
    const rq = mod.get(x, { lookup: safeLookup, timeout: 15000, headers: { 'User-Agent': UA_RES, Accept: 'image/avif,image/webp,image/*,text/css,*/*;q=0.8', 'Accept-Language': 'ja,en;q=0.8', Referer: ref || '' } }, r => {
      const code = r.statusCode || 0, loc = r.headers.location;
      if (code >= 300 && code < 400 && loc) {
        r.resume(); if (hop >= 5) return ng(new HttpErr(502, 'too many redirects'));
        let nx; try { nx = new URL(loc, u).href; } catch (e) { return ng(new HttpErr(502, 'bad redirect')); }
        return checkUrl(nx).then(v => getRes(v, ref, hop + 1)).then(ok, ng);
      }
      const type = String(r.headers['content-type'] || ''), c = []; let n = 0;
      r.on('data', d => { n += d.length; if (n > RES_MAX) { r.destroy(); ng(new HttpErr(413, 'too large')); } else c.push(d); });
      r.on('end', () => ok({ code, type, url: u, body: Buffer.concat(c) })); r.on('error', ng);
    });
    rq.on('timeout', () => rq.destroy(new HttpErr(504, 'timeout'))); rq.on('error', ng);
  });
}
/* かんたん表示（Apps Script が取ったページ）で、サイトから直接は出なかった画像だけを、ここで取る（GET /i?t=<チケット>&u=<URL>） */
async function serveImg(req, res) {
  const fail = (code, msg) => { res.writeHead(code, { 'Content-Type': 'text/plain; charset=utf-8', 'Cache-Control': 'no-store' }); res.end(msg); };
  let q; try { q = new URL(req.url, 'http://x').searchParams; } catch (e) { return fail(400, 'bad'); }
  if (!verify('Bearer ' + (q.get('t') || ''))) return fail(401, 'ticket');
  let u; try { u = await checkUrl(q.get('u') || ''); } catch (e) { return fail(400, 'bad url'); }
  lastUse = Date.now();
  try {
    const r = await getRes(u, q.get('r') || '', 0), type = r.type.split(';')[0].trim().toLowerCase();
    if (!/^image\//.test(type)) return fail(415, 'not an image');
    res.writeHead(r.code >= 200 && r.code < 300 ? 200 : r.code, { 'Content-Type': type, 'Content-Length': r.body.length, 'Cache-Control': 'private, max-age=3600', 'X-Content-Type-Options': 'nosniff', 'Content-Security-Policy': "default-src 'none'; style-src 'unsafe-inline'; sandbox", 'Cross-Origin-Resource-Policy': 'cross-origin' });
    res.end(r.body);
  } catch (e) { fail(e.code && Number.isInteger(e.code) ? e.code : 502, 'fetch failed'); }
}
async function serveRes(req, res, path) {
  const m = /^\/r\/([\w-]{20,})\/(.+)$/.exec(path), s = m && byRk.get(m[1]);
  const fail = (code, msg) => { res.writeHead(code, { 'Content-Type': 'text/plain; charset=utf-8', 'Cache-Control': 'no-store' }); res.end(msg); };
  if (!s) return fail(404, 'no page');
  let u; try { u = await checkUrl(decodeURIComponent(m[2])); } catch (e) { return fail(400, 'bad url'); }
  s.last = lastUse = Date.now();
  try {
    const r = await getRes(u, s.page.url(), 0);
    let type = r.type.split(';')[0].trim().toLowerCase(), body = r.body;
    if (!type || type === 'application/octet-stream') { // 種類がわからないときは、拡張子で
      const ext = (/\.(\w+)(?:$|\?)/.exec(new URL(r.url).pathname) || [])[1] || '';
      type = { woff: 'font/woff', woff2: 'font/woff2', ttf: 'font/ttf', otf: 'font/otf', eot: 'application/vnd.ms-fontobject', css: 'text/css', svg: 'image/svg+xml', png: 'image/png', jpg: 'image/jpeg', jpeg: 'image/jpeg', gif: 'image/gif', webp: 'image/webp', avif: 'image/avif', ico: 'image/x-icon' }[ext.toLowerCase()] || '';
    }
    if (!RES_OK.test(type) || type === 'application/octet-stream') return fail(415, 'not allowed');
    if (type === 'text/css') { // CSS の中の url() も、このサーバーを通す（CSS のある場所から見たアドレスで）
      const pfx = (s.res || '') + '/r/' + s.rk + '/';
      const R = v => { v = String(v || '').trim(); if (!v || /^(data:|#)/i.test(v)) return v; try { const a = new URL(v, r.url).href; return /^https?:/i.test(a) ? (s.res ? pfx + encodeURIComponent(a) : a) : ''; } catch (e) { return ''; } };
      body = Buffer.from(body.toString('utf8')
        .replace(/url\(\s*(['"]?)(.*?)\1\s*\)/gi, (x, q, v) => /^(data:|#)/i.test(v) ? x : 'url("' + R(v).replace(/"/g, '%22') + '")')
        .replace(/@import\s+(['"])(.*?)\1/gi, (x, q, v) => '@import url("' + R(v).replace(/"/g, '%22') + '")'));
      type = 'text/css; charset=utf-8';
    }
    res.writeHead(r.code >= 200 && r.code < 300 ? 200 : r.code, { 'Content-Type': type, 'Content-Length': body.length, 'Cache-Control': 'private, max-age=3600', 'X-Content-Type-Options': 'nosniff', 'Content-Security-Policy': "default-src 'none'; img-src data:; style-src 'unsafe-inline'; sandbox", 'Cross-Origin-Resource-Policy': 'cross-origin' });
    res.end(body);
  } catch (e) { fail(e.code && Number.isInteger(e.code) ? e.code : 502, 'fetch failed'); }
}

/* ===== 受け付け ===== */
function readBody(req, max) {
  return new Promise((ok, ng) => { let n = 0; const c = []; req.on('data', d => { n += d.length; if (n > (max || 65536)) { ng(new HttpErr(413, '大きすぎます')); req.destroy(); } else c.push(d); }); req.on('end', () => {
    let buf = Buffer.concat(c);
    if (/gzip/i.test(req.headers['content-encoding'] || '')) { try { buf = zlib.gunzipSync(buf, { maxOutputLength: Math.max(max || 65536, 65536) * 2 }); } catch (e) { ng(new HttpErr(400, '送られたものを読めませんでした')); return; } }
    ok(buf.toString('utf8'));
  }); req.on('error', ng); });
}
function own(b, who) { const s = sessions.get(String(b.sid || '')); if (!s || s.owner !== who.u) throw new HttpErr(410, 'ページが閉じられました。もう一度開いてください'); s.last = lastUse = Date.now(); return s; }
const queue = (s, fn) => (s.q = s.q.then(fn, fn)); // 1つのページへの操作は、順番に
async function route(path, b, who) {
  if (path === '/api/open') {
    const w = Math.max(360, Math.min(1400, Math.round(Number(b.w) || 1100)));
    const url = await checkUrl(b.url);
    const mode = b.mode === 'dom' ? 'dom' : 'tiles', res = typeof b.res === 'string' && /^https?:\/\/[\w.:-]+$/.test(b.res.replace(/\/+$/, '')) ? b.res.replace(/\/+$/, '') : '';
    const setMode = s => { s.mode = mode; s.res = res; };
    /* Apps Script がもう取ってきたページ（HTML と CSS）: ここの Chrome は、それを使う（サイトから取り直さない）。JavaScript などだけを取りにいく */
    const given = typeof b.html === 'string' && b.html ? { url: url.split('#')[0], html: b.html, used: false,
      css: new Map((Array.isArray(b.css) ? b.css : []).slice(0, 400).filter(c => c && typeof c.href === 'string' && typeof c.text === 'string').map(c => [c.href.split('#')[0], c.text])) } : null;
    const run = s => queue(s, async () => {
      s.given = given; s.ms.given = given ? 1 : 0;
      if (given) { // CSS は、このページ（セッション）が閉じるまで覚えておく（次のページで、ハブがもう一度送らなくてよい）
        if (!s.css) { s.css = new Map(); s.cssN = 0; }
        for (const [k, t] of given.css) { if (!s.css.has(k)) { s.css.set(k, t); s.cssN += t.length; } }
        while (s.cssN > 12e6 && s.css.size) { const k = s.css.keys().next().value; s.cssN -= s.css.get(k).length; s.css.delete(k); }
      }
      await goto(s, url); return Object.assign(await snap(s, { around: 0 }), given ? { cssHave: s.css.size } : {});
    });
    if (b.sid && sessions.has(String(b.sid))) { const s = own(b, who); setMode(s); if (s.w !== w) { s.w = w; await s.page.setViewport({ width: w, height: VH }); } return run(s); }
    const t0 = Date.now(), s = await newSession(who.u, w); lastUse = Date.now(); s.ms.start = Date.now() - t0; setMode(s);
    return run(s);
  }
  if (path === '/api/act') { const s = own(b, who); return queue(s, () => act(s, b)); }
  if (path === '/api/tiles') { const s = own(b, who); return queue(s, async () => { await pageH(s); return { sid: s.sid, v: s.v, H: s.H, tiles: await capture(s, Number(b.from) || 0, Number(b.to) || 0) }; }); }
  if (path === '/api/close') { const s = sessions.get(String(b.sid || '')); if (s && s.owner === who.u) await closeS(s); return { ok: true }; }
  throw new HttpErr(404, 'ありません');
}
http.createServer(async (req, res) => {
  res.setHeader('Access-Control-Allow-Origin', '*');
  res.setHeader('Access-Control-Allow-Headers', 'Authorization, Content-Type, Content-Encoding');
  res.setHeader('Access-Control-Expose-Headers', 'X-Rb-Z');
  res.setHeader('X-Rb-Z', '1'); // 送るもの（HTML など）を gzip で小さくして受け取れる
  res.setHeader('Access-Control-Allow-Methods', 'GET, POST, OPTIONS');
  res.setHeader('Access-Control-Max-Age', '86400');
  const path = (req.url || '/').split('?')[0];
  if (req.method === 'OPTIONS') { res.writeHead(204); res.end(); return; }
  if (req.method === 'GET' && (path === '/ping' || path === '/')) { res.writeHead(200, { 'Content-Type': 'text/plain' }); res.end('ok'); return; }
  if (req.method === 'GET' && path.startsWith('/r/')) { serveRes(req, res, path); return; }
  if (req.method === 'GET' && path === '/i') { serveImg(req, res); return; }
  // 絵（base64）は gzip で 2〜3 割小さくなる
  const gz = /\bgzip\b/.test(req.headers['accept-encoding'] || '') && !/Google-Apps-Script/i.test(req.headers['user-agent'] || ''); // Apps Script の中継には、そのまま
  const send = (code, o) => {
    let body = Buffer.from(JSON.stringify(o)); const h = { 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store', Vary: 'Accept-Encoding' };
    if (gz && body.length > 2048) { body = zlib.gzipSync(body, { level: 1 }); h['Content-Encoding'] = 'gzip'; }
    res.writeHead(code, h); res.end(body);
  };
  if (req.method !== 'POST') { send(405, { error: 'POST だけです' }); return; }
  const who = verify(req.headers.authorization); if (!who) { send(401, { error: '本人確認ができませんでした（チケットが古いか、違います）' }); return; }
  busy++; lastUse = Date.now();
  try { const b = JSON.parse((await readBody(req, path === '/api/open' ? 24 * 1024 * 1024 : 0)) || '{}'); /* open は、Apps Script が取ったページ（HTML・CSS）を持ってくるので大きい */ send(200, await route(path, b, who)); }
  catch (e) { send(e.code || 500, { error: e.code ? e.message : 'サーバーでエラーが起きました（' + short(e.message) + '）' }); if (!e.code) console.error(e); }
  finally { busy--; lastUse = Date.now(); }
}).listen(PORT, () => { console.log('rbrowser on ' + PORT + (SECRET ? '' : '  ※ RB_SECRET がありません（だれも使えません）')); getBrowser().catch(e => console.error('Chrome を起こせませんでした', e.message)); });

/* 使っていないページを閉じる（Chrome 自体は起こしたままにして、次に開くときを速くする） */
setInterval(async () => {
  for (const s of [...sessions.values()]) if (Date.now() - s.last > IDLE_MS) await closeS(s);
}, 30 * 1000);
/* 空のページの用意は、だれも使っていない（5秒さわられていない）ときに（遅いサーバーで、見ている人のじゃまをしない） */
setInterval(() => { if (!spare && !spareMaking && !busy && Date.now() - lastUse > 5000 && browser && browser.connected) makeSpare(); }, 2000);
