/* 딜레이 카메라 — 체육 수업 / 운동 자세 교정용
 *
 * 구조 요약
 *  1) 카메라 → (숨겨진 <video>) → 캡처 캔버스에서 "기기 기준 방향"으로 정규화 → JPEG Blob 링버퍼
 *  2) 재생 헤드(playT)가 버퍼에서 프레임을 골라 디코드 → 표시 캔버스에 그림
 *  3) 화면 방향: 시스템 회전 각도(A)를 읽어 루트(#app)를 반대로 회전시켜
 *     "앱 회전 버튼으로 고른 방향(T)"에 항상 고정. 카메라/버퍼는 방향 전환과 무관하게 유지됨.
 *
 *  각도 규칙: 모든 각도는 "기기의 위쪽 모서리 기준 시계방향" 도(degree).
 *   A = 시스템이 콘텐츠를 돌려놓은 각도 (뷰포트의 위쪽 = 기기의 A 모서리)
 *   T = 앱이 원하는 콘텐츠 위쪽 (0 = 세로, 90/270 = 가로)
 *   R = T - A  → #app 에 적용하는 CSS 회전
 */
(() => {
'use strict';

const $ = (id) => document.getElementById(id);
const app = $('app'), video = $('src'), view = $('view'), stage = $('stage');
const vctx = view.getContext('2d', { alpha: false });

/* ---------------- 설정 (localStorage 저장) ---------------- */
const STORE_KEY = 'delaycam.settings.v1';
const DEFAULTS = {
  delay: 5, bufferSec: 60, quality: 'mid', fps: 30, fit: 'cover',
  mirror: true, landDir: 90, orient: 'portrait', facing: 'environment',
};
const S = Object.assign({}, DEFAULTS, loadSettings());
function loadSettings() { try { return JSON.parse(localStorage.getItem(STORE_KEY)) || {}; } catch (e) { return {}; } }
function saveSettings() { try { localStorage.setItem(STORE_KEY, JSON.stringify(S)); } catch (e) {} }

const LONG_SIDE = { low: 640, mid: 960, high: 1280 };
const JPEG_Q = 0.72;
const MAX_BYTES = 180 * 1024 * 1024;       // 메모리 상한 (모바일 브라우저 보호)
const SPEEDS = [0.25, 0.5, 1, 2];

/* ---------------- 상태 ---------------- */
let started = false;
let stream = null, track = null, isFront = false, camStarting = false;
const frames = [];                 // {t, blob, size, front}
let bytes = 0, evictedAny = false;
let recording = true;              // false = 기록 정지(버퍼 고정, 분석용)
let playing = true, speed = 1;
let playT = 0;                     // 재생 위치 (performance.now() 시간축, ms)
let lastEdge = 0;
let loopA = null, loopB = null, loopOn = false;
let scrubbing = false, wasPlaying = false;

/* ======================================================================
 * 1. 화면 방향 고정 (시스템 자동회전 무시)
 * ==================================================================== */
const lay = { A: -1, vw: 0, vh: 0, T: -1, R: 0, W: 0, H: 0, safe: [0, 0, 0, 0] };

function deviceAngle() {
  let a = 0;
  if (typeof window.orientation === 'number') a = window.orientation;            // iOS / Android: 90 = 반시계로 눕힘
  else if (screen.orientation && typeof screen.orientation.angle === 'number') a = screen.orientation.angle;
  a = Math.round(a / 90) * 90;
  return ((a % 360) + 360) % 360;
}
function targetAngle() { return S.orient === 'portrait' ? 0 : S.landDir; }

// safe-area 값 측정용 (회전에 맞춰 변의 대응을 바꿔 적용)
const probe = document.createElement('div');
probe.style.cssText = 'position:fixed;left:0;top:0;width:0;height:0;visibility:hidden;pointer-events:none;' +
  'padding:env(safe-area-inset-top) env(safe-area-inset-right) env(safe-area-inset-bottom) env(safe-area-inset-left)';
document.body.appendChild(probe);

function applyLayout(force) {
  const A = deviceAngle(), T = targetAngle();
  const vw = window.innerWidth, vh = window.innerHeight;
  if (!force && A === lay.A && vw === lay.vw && vh === lay.vh && T === lay.T) return false;

  const R = ((T - A) % 360 + 360) % 360;
  const swap = R % 180 !== 0;
  const W = swap ? vh : vw, H = swap ? vw : vh;
  Object.assign(lay, { A, vw, vh, T, R, W, H });

  app.style.width = W + 'px';
  app.style.height = H + 'px';
  app.style.transform = `translate(-50%, -50%) rotate(${R}deg)`;

  // safe-area: 루트의 i번째 변(위,오,아,왼)은 뷰포트의 (i + R/90)번째 변에 놓임
  const cs = getComputedStyle(probe);
  const v = [cs.paddingTop, cs.paddingRight, cs.paddingBottom, cs.paddingLeft].map((x) => parseFloat(x) || 0);
  const k = R / 90;
  ['top', 'right', 'bottom', 'left'].forEach((n, i) => {
    lay.safe[i] = v[(i + k) % 4];
    app.style.setProperty('--safe-' + n, lay.safe[i] + 'px');
  });

  const land = W > H;
  app.classList.toggle('landscape', land);
  app.classList.toggle('portrait', !land);
  layoutControls(land);
  resizeView();
  return true;
}

// 버튼 수와 화면 크기로 열 수를 계산 → 어떤 기기에서도 겹치지 않음
function layoutControls(land) {
  const ctr = $('controls');
  const n = ctr.children.length;
  let cols;
  if (land) {
    const availH = lay.H - lay.safe[0] - lay.safe[2] - 16;
    const rows = Math.max(1, Math.floor((availH + 6) / (50 + 6)));
    cols = Math.ceil(n / rows);
  } else {
    const availW = lay.W - lay.safe[1] - lay.safe[3] - 16;
    cols = Math.max(3, Math.min(n, Math.floor((availW + 6) / (44 + 6))));
    const rows = Math.ceil(n / cols);
    cols = Math.ceil(n / rows);                       // 줄마다 개수 균등화
  }
  ctr.style.setProperty('--cols', cols);
}

function resizeView() {
  const dpr = Math.min(window.devicePixelRatio || 1, 2);
  const w = Math.max(1, Math.round(stage.clientWidth * dpr));   // clientWidth = 회전 전 레이아웃 크기
  const h = Math.max(1, Math.round(stage.clientHeight * dpr));
  if (view.width !== w || view.height !== h) { view.width = w; view.height = h; }
  draw();
}

async function lockOrientation() {
  // Android Chrome: 전체화면 또는 설치된 앱에서만 동작. 실패해도 CSS 보정이 처리함.
  try {
    if (!screen.orientation || !screen.orientation.lock) return;
    const T = targetAngle();
    await screen.orientation.lock(T === 0 ? 'portrait-primary' : T === 90 ? 'landscape-primary' : 'landscape-secondary');
  } catch (e) {}
}

['resize', 'orientationchange'].forEach((ev) => window.addEventListener(ev, () => applyLayout(false)));
if (screen.orientation && screen.orientation.addEventListener) screen.orientation.addEventListener('change', () => applyLayout(false));
if (window.visualViewport) window.visualViewport.addEventListener('resize', () => applyLayout(false));
new ResizeObserver(() => resizeView()).observe(stage);

/* ======================================================================
 * 2. 카메라
 * ==================================================================== */
async function startCamera() {
  if (camStarting) return false;
  camStarting = true;
  try {
    if (!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia) {
      throw new Error(location.protocol === 'https:' ? '이 브라우저는 카메라를 지원하지 않습니다.' : 'HTTPS 주소에서만 카메라를 사용할 수 있습니다.');
    }
    if (stream) stream.getTracks().forEach((t) => t.stop());
    stream = null;
    let s;
    try {
      s = await navigator.mediaDevices.getUserMedia({
        audio: false,
        video: { facingMode: { ideal: S.facing }, width: { ideal: 1280 }, height: { ideal: 720 }, frameRate: { ideal: 30 } },
      });
    } catch (e) {
      if (e && (e.name === 'NotAllowedError' || e.name === 'SecurityError')) throw e;
      s = await navigator.mediaDevices.getUserMedia({ video: true, audio: false });
    }
    stream = s;
    track = s.getVideoTracks()[0];
    const st = track.getSettings ? track.getSettings() : {};
    isFront = st.facingMode ? st.facingMode === 'user' : S.facing === 'user';
    track.addEventListener('ended', () => {
      if (!document.hidden && started) { toast('카메라 연결이 끊어져 다시 연결합니다'); setTimeout(startCamera, 600); }
    });
    video.srcObject = s;
    natural = null; mismatchSince = 0;
    await video.play().catch(() => {});
    return true;
  } catch (e) {
    const msg = e && e.name === 'NotAllowedError' ? '카메라 권한이 거부되었습니다. 브라우저 설정에서 허용해 주세요.'
      : (e && e.message) || '카메라를 열 수 없습니다.';
    toast(msg, 4000);
    $('startHint').textContent = msg;
    return false;
  } finally {
    camStarting = false;
  }
}

/* ======================================================================
 * 3. 캡처 → 기기 기준 방향으로 정규화 → JPEG 버퍼
 *    (시스템이 카메라 프레임을 돌려도 버퍼의 프레임 방향/크기는 일정 → 회전해도 버퍼 유지)
 * ==================================================================== */
const cap = document.createElement('canvas');
const cctx = cap.getContext('2d', { alpha: false });
let natural = null;            // 기기 세로(자연) 방향 기준 원본 크기
let mismatchSince = 0, pendingEnc = 0, lastCapT = 0;

function setCapSize() {
  if (!natural) return;
  const L = Math.min(LONG_SIDE[S.quality] || 960, Math.max(natural.w, natural.h));
  const sc = L / Math.max(natural.w, natural.h);
  cap.width = Math.round(natural.w * sc / 2) * 2;
  cap.height = Math.round(natural.h * sc / 2) * 2;
}

function capture(now) {
  if (!recording || !stream || video.readyState < 2) return;
  const vw = video.videoWidth, vh = video.videoHeight;
  if (!vw || !vh) return;
  if (now - lastCapT < 1000 / S.fps - 4) return;
  if (pendingEnc >= 3) return;                    // 인코딩이 밀리면 프레임 건너뜀

  const A = deviceAngle();
  const turned = A % 180 !== 0;
  if (!natural) { natural = turned ? { w: vh, h: vw } : { w: vw, h: vh }; setCapSize(); }

  // 회전 전환 중(각도와 프레임 크기가 아직 안 맞는 순간)은 프레임을 버림
  if (vw !== vh && natural.w !== natural.h) {
    const expectPortrait = turned ? natural.w > natural.h : natural.h > natural.w;
    if ((vh > vw) !== expectPortrait) {
      if (!mismatchSince) mismatchSince = now;
      if (now - mismatchSince < 700) return;
      natural = turned ? { w: vh, h: vw } : { w: vw, h: vh };   // 지속되면 기준 재설정
      setCapSize();
    }
  }
  mismatchSince = 0;
  lastCapT = now;

  const W = cap.width, H = cap.height;
  const ew = turned ? vh : vw, eh = turned ? vw : vh;
  const sc = Math.max(W / ew, H / eh);
  cctx.save();
  cctx.translate(W / 2, H / 2);
  cctx.rotate(A * Math.PI / 180);                 // 원본의 위쪽 = 기기 A 모서리 → 기기 기준으로 되돌림
  cctx.drawImage(video, -vw * sc / 2, -vh * sc / 2, vw * sc, vh * sc);
  cctx.restore();

  pendingEnc++;
  const t = now, front = isFront;
  cap.toBlob((b) => {
    pendingEnc--;
    if (b) addFrame({ t, blob: b, size: b.size, front });
  }, 'image/jpeg', JPEG_Q);
}

function keepMs() { return Math.max(S.bufferSec, S.delay + 5) * 1000; }

function addFrame(f) {
  let i = frames.length;
  while (i > 0 && frames[i - 1].t > f.t) i--;
  frames.splice(i, 0, f);
  bytes += f.size;
  evict();
}
function evict() {
  if (!frames.length) return;
  const newest = frames[frames.length - 1].t, keep = keepMs();
  while (frames.length > 1 && (frames[0].t < newest - keep || bytes > MAX_BYTES)) {
    bytes -= frames.shift().size;
    evictedAny = true;
  }
}
function clearBuffer() {
  frames.length = 0; bytes = 0; evictedAny = false;
  loopA = loopB = null; loopOn = false;
  if (curImg && curImg.close) curImg.close();
  curImg = null; curFrame = null; wantFrame = null;
  goLive(); draw();
}

function findIdx(t) {
  let lo = 0, hi = frames.length - 1, ans = -1;
  while (lo <= hi) { const m = (lo + hi) >> 1; if (frames[m].t <= t) { ans = m; lo = m + 1; } else hi = m - 1; }
  return ans;
}

/* ======================================================================
 * 4. 재생 (지연 / 속도 / 구간 반복)
 * ==================================================================== */
function edgeTime(now) {           // 정상 재생의 상한: 기록 중이면 (지금 - 지연), 정지 중이면 마지막 프레임
  return recording ? now - S.delay * 1000 : (frames.length ? frames[frames.length - 1].t : now);
}
function goLive() {
  playT = performance.now() - S.delay * 1000;
  speed = 1; playing = true; loopOn = false;
  if (!recording) recording = true;
  refreshButtons();
}

function updatePlayhead(now, dt) {
  const n = frames.length;
  const oldest = n ? frames[0].t : now, newest = n ? frames[n - 1].t : now;
  const edge = edgeTime(now);

  if (playing && !scrubbing) {
    const atEdge = playT >= lastEdge - 5;             // 직전 프레임에 지연 지점에 붙어 있었는지
    const ahead = playT > lastEdge + 30;              // 사용자가 지연 지점보다 앞으로 옮긴 경우
    playT += dt * speed;

    if (loopOn) {
      const ls = loopA != null ? loopA : oldest;
      const le = loopB != null ? loopB : edge;
      if (le - ls > 100 && playT >= le) playT = ls;
    }
    if (!loopOn && atEdge && speed >= 1) playT = edge;          // 프레임 지연/백그라운드 후에도 지연 시간 정확히 유지
    if (ahead) { if (playT > newest) playT = newest; }
    else if (playT > edge) {
      playT = edge;
      if (!recording && !loopOn) playing = false, refreshButtons();   // 고정 버퍼 끝에 도달
    }
  }
  if (n && playT < oldest && (evictedAny || !recording)) playT = oldest;
  lastEdge = edge;
}

/* ---------------- 프레임 디코드 & 그리기 ---------------- */
let curImg = null, curFrame = null, wantFrame = null, decoding = false;

function decodeBlob(blob) {
  if (window.createImageBitmap) return createImageBitmap(blob);
  return new Promise((res, rej) => {                                    // 구형 Safari 대비
    const url = URL.createObjectURL(blob), img = new Image();
    img.onload = () => { URL.revokeObjectURL(url); res(img); };
    img.onerror = (e) => { URL.revokeObjectURL(url); rej(e); };
    img.src = url;
  });
}
function showFrame() {
  const i = findIdx(playT);
  if (i < 0) return;
  const f = frames[i];
  if (f === curFrame) return;
  wantFrame = f;
  if (!decoding) decodeNext();
}
async function decodeNext() {
  const f = wantFrame;
  if (!f || f === curFrame) return;
  decoding = true;
  try {
    const img = await decodeBlob(f.blob);
    if (curImg && curImg.close) curImg.close();
    curImg = img; curFrame = f;
    draw();
  } catch (e) {}
  decoding = false;
  if (wantFrame && wantFrame !== curFrame) decodeNext();
}

function draw() {
  const w = view.width, h = view.height;
  vctx.fillStyle = '#000';
  vctx.fillRect(0, 0, w, h);
  if (!curImg) return;
  const bw = curImg.width || curImg.naturalWidth, bh = curImg.height || curImg.naturalHeight;
  const T = lay.T < 0 ? 0 : lay.T;
  const sw = T % 180 ? bh : bw, sh = T % 180 ? bw : bh;      // 회전 후 보이는 크기
  const sc = S.fit === 'cover' ? Math.max(w / sw, h / sh) : Math.min(w / sw, h / sh);
  vctx.save();
  vctx.translate(w / 2, h / 2);
  if (curFrame && curFrame.front && S.mirror) vctx.scale(-1, 1);   // 화면 기준 좌우 반전(거울)
  vctx.rotate(-T * Math.PI / 180);                                   // 기기 기준 프레임 → 현재 앱 방향
  vctx.drawImage(curImg, -bw * sc / 2, -bh * sc / 2, bw * sc, bh * sc);
  vctx.restore();
}

/* ======================================================================
 * 5. UI
 * ==================================================================== */
const el = {
  bPlay: $('bPlay'), bSpeed: $('bSpeed'), bLoop: $('bLoop'), bRec: $('bRec'), bA: $('bA'), bB: $('bB'), bLive: $('bLive'),
  speedTxt: $('speedTxt'), recTxt: $('recTxt'), delayTxt: $('delayTxt'), rotTxt: $('rotTxt'),
  recPill: $('recPill'), modePill: $('modePill'), lagPill: $('lagPill'),
  wait: $('wait'), waitNum: $('waitNum'), waitTxt: $('waitTxt'),
  track: $('track'), tlFill: $('tlFill'), tlLoop: $('tlLoop'), tlLive: $('tlLive'), tlA: $('tlA'), tlB: $('tlB'), tlHead: $('tlHead'),
  tlLeft: $('tlLeft'), tlRight: $('tlRight'),
};

function fmtDelay(d) { return d === 0 ? '실시간' : `지연 ${d}초`; }

function refreshButtons() {
  el.bPlay.classList.toggle('paused', !playing);
  el.bPlay.querySelector('.l').textContent = playing ? '멈춤' : '재생';
  el.speedTxt.textContent = (speed === 0.25 ? '¼' : speed === 0.5 ? '½' : speed) + 'x';
  el.bSpeed.classList.toggle('on', speed !== 1);
  el.bLoop.classList.toggle('on', loopOn);
  el.bA.classList.toggle('set', loopA != null);
  el.bB.classList.toggle('set', loopB != null);
  el.bRec.classList.toggle('frozen', !recording);
  el.recTxt.textContent = recording ? '기록중' : '정지됨';
  el.delayTxt.textContent = S.delay + 's';
  el.rotTxt.textContent = S.orient === 'portrait' ? '가로로' : '세로로';
  el.recPill.classList.toggle('off', !recording);
  el.recPill.querySelector('b').textContent = recording ? 'REC' : '정지';
}

let lastTextT = 0;
function updateUI(now) {
  const n = frames.length;
  const end = recording ? now : (n ? frames[n - 1].t : now);
  const span = keepMs(), start = end - span;
  const pct = (t) => (Math.min(1, Math.max(0, (t - start) / span)) * 100).toFixed(2) + '%';

  if (n) { el.tlFill.style.left = pct(frames[0].t); el.tlFill.style.width = `calc(${pct(frames[n - 1].t)} - ${pct(frames[0].t)})`; }
  else el.tlFill.style.width = '0';
  el.tlHead.style.left = pct(playT);
  el.tlLive.style.left = pct(edgeTime(now));
  el.tlLive.style.display = recording ? '' : 'none';
  el.tlA.hidden = loopA == null; if (loopA != null) el.tlA.style.left = pct(loopA);
  el.tlB.hidden = loopB == null; if (loopB != null) el.tlB.style.left = pct(loopB);
  if (loopOn) {
    const ls = loopA != null ? loopA : (n ? frames[0].t : start);
    const le = loopB != null ? loopB : edgeTime(now);
    el.tlLoop.style.display = 'block';
    el.tlLoop.style.left = pct(ls);
    el.tlLoop.style.width = `calc(${pct(le)} - ${pct(ls)})`;
  } else el.tlLoop.style.display = 'none';

  // 대기 화면 (지연 버퍼 채우는 중)
  const idx = findIdx(playT);
  const waiting = started && idx < 0;
  el.wait.hidden = !waiting;

  if (now - lastTextT < 100) return;              // 텍스트는 10Hz
  lastTextT = now;
  if (waiting) {
    if (!n) { el.waitNum.textContent = '…'; el.waitTxt.textContent = '카메라 준비 중'; }
    else {
      const sec = Math.max(0, (frames[0].t - playT) / 1000 / Math.max(speed, 0.25));
      el.waitNum.textContent = Math.ceil(sec);
      el.waitTxt.textContent = '초 후 지연 영상 재생';
    }
  }
  const lag = Math.max(0, (end - playT) / 1000);
  el.lagPill.textContent = (recording ? '-' : '') + (recording ? lag.toFixed(1) + 's' : ((playT - (n ? frames[0].t : 0)) / 1000).toFixed(1) + 's');
  const live = recording && playing && !loopOn && speed === 1 && Math.abs(lag - S.delay) < 0.25;
  let mode = live ? (S.delay ? `LIVE · ${S.delay}초 지연` : 'LIVE') : (playing ? '리플레이' : '일시정지');
  if (speed !== 1) mode += ` · ${speed}x`;
  if (loopOn) mode += ' · 구간반복';
  el.modePill.textContent = mode;
  el.modePill.classList.toggle('warn', !live);
  el.tlLeft.textContent = `-${Math.round(span / 1000)}s`;
  el.tlRight.textContent = recording ? '지금' : '끝';
}

/* ---------------- 토스트 ---------------- */
let toastTimer = 0;
function toast(msg, ms = 1600) {
  const t = $('toast');
  t.textContent = msg; t.classList.add('show');
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => t.classList.remove('show'), ms);
}

/* ---------------- 타임라인 스크럽 (회전된 좌표계 보정) ---------------- */
function localFrac(node, cx, cy) {
  const r = node.getBoundingClientRect();
  const dx = cx - (r.left + r.width / 2), dy = cy - (r.top + r.height / 2);
  const a = lay.R * Math.PI / 180;
  const lx = dx * Math.cos(a) + dy * Math.sin(a);           // 화면 좌표 → 요소 내부 x
  return Math.min(1, Math.max(0, (lx + node.offsetWidth / 2) / node.offsetWidth));
}
function scrubTo(e) {
  const now = performance.now(), n = frames.length;
  if (!n) return;
  const end = recording ? now : frames[n - 1].t, span = keepMs();
  playT = Math.min(frames[n - 1].t, Math.max(frames[0].t, end - span + localFrac(el.track, e.clientX, e.clientY) * span));
  showFrame();
}
el.track.addEventListener('pointerdown', (e) => {
  if (!frames.length) return;
  el.track.setPointerCapture(e.pointerId);
  scrubbing = true; wasPlaying = playing; playing = false;
  scrubTo(e);
});
el.track.addEventListener('pointermove', (e) => { if (scrubbing) scrubTo(e); });
const endScrub = () => { if (!scrubbing) return; scrubbing = false; playing = wasPlaying; lastEdge = Infinity; refreshButtons(); };
el.track.addEventListener('pointerup', endScrub);
el.track.addEventListener('pointercancel', endScrub);

/* ---------------- 버튼 ---------------- */
function on(id, fn) { $(id).addEventListener('click', fn); }

function togglePlay() {
  if (!playing && frames.length) {
    const lastT = frames[frames.length - 1].t;
    if (!recording && playT >= lastT - 1) playT = loopA != null ? loopA : frames[0].t;   // 끝이면 처음부터
  }
  playing = !playing;
  lastEdge = Infinity;
  refreshButtons();
}
function step(d) {
  if (!frames.length) return;
  playing = false;
  let i = findIdx(playT);
  i = i < 0 ? 0 : Math.min(frames.length - 1, Math.max(0, i + d));
  playT = frames[i].t;
  refreshButtons();
}
on('bPlay', togglePlay);
on('bBack', () => step(-1));
on('bFwd', () => step(1));
on('bSpeed', () => {
  speed = SPEEDS[(SPEEDS.indexOf(speed) + 1) % SPEEDS.length];
  if (speed < 1 && recording) toast(`${speed}x 슬로모션 · LIVE 버튼으로 지연 화면 복귀`);
  refreshButtons();
});
on('bLive', () => { goLive(); toast(S.delay ? `${S.delay}초 지연 화면으로 복귀` : '실시간 화면'); });

// A/B: 탭 = 지점 지정, 길게 누르기 = 구간 해제
let lpTimer = 0, lpFired = false;
['bA', 'bB', 'bLoop'].forEach((id) => {
  const b = $(id);
  b.addEventListener('pointerdown', () => {
    lpFired = false;
    lpTimer = setTimeout(() => { lpFired = true; loopA = loopB = null; loopOn = false; refreshButtons(); toast('구간 해제'); }, 600);
  });
  ['pointerup', 'pointerleave', 'pointercancel'].forEach((ev) => b.addEventListener(ev, () => clearTimeout(lpTimer)));
});
on('bA', () => {
  if (lpFired) return;
  loopA = playT;
  if (loopB != null && loopB <= loopA + 100) loopB = null;
  toast('A(시작점) 지정 · 길게 누르면 구간 해제');
  refreshButtons();
});
on('bB', () => {
  if (lpFired) return;
  if (loopA != null && playT <= loopA + 100) { toast('B는 A보다 뒤에 지정해 주세요'); return; }
  loopB = playT;
  if (loopA != null) { loopOn = true; playT = loopA; playing = true; lastEdge = Infinity; toast('A–B 구간 반복 재생'); }
  else toast('B(끝점) 지정');
  refreshButtons();
});
on('bLoop', () => {
  if (lpFired) return;
  loopOn = !loopOn;
  if (loopOn) {
    if (loopA != null) playT = loopA;
    else if (frames.length) playT = frames[0].t;
    playing = true; lastEdge = Infinity;
    toast(loopA != null || loopB != null ? '구간 반복 켜짐' : '기록된 전체 구간 반복');
  } else toast('구간 반복 꺼짐');
  refreshButtons();
});
on('bRec', () => {
  recording = !recording;
  if (recording) { goLive(); toast('기록 재개 · 지연 화면으로 복귀'); }
  else { toast('기록 정지 · 버퍼가 고정되어 자세히 분석할 수 있어요', 2200); }
  refreshButtons();
});
on('bDelay', () => openSheet());
on('bSet', () => openSheet());
on('bCam', async () => {
  S.facing = S.facing === 'user' ? 'environment' : 'user';
  saveSettings();
  if (started) { toast(S.facing === 'user' ? '전면 카메라' : '후면 카메라'); await startCamera(); }
});
on('bRotate', () => {
  S.orient = S.orient === 'portrait' ? 'landscape' : 'portrait';
  saveSettings();
  applyLayout(true);
  if (document.fullscreenElement || isStandalone()) lockOrientation();
  refreshButtons();
  toast(S.orient === 'portrait' ? '세로 화면' : '가로 화면 · 기기를 옆으로 눕혀 주세요');
});

/* ---------------- 설정 시트 ---------------- */
const OPTIONS = [
  { key: 'delay', label: '지연 시간', opts: [[0, '실시간'], [1, '1초'], [2, '2초'], [3, '3초'], [5, '5초'], [7, '7초'], [10, '10초'], [15, '15초'], [20, '20초'], [30, '30초']] },
  { key: 'bufferSec', label: '기록 길이 (되감기 가능 범위)', opts: [[30, '30초'], [60, '60초'], [90, '90초'], [120, '120초']] },
  { key: 'quality', label: '화질', opts: [['low', '저 (빠름)'], ['mid', '중'], ['high', '고']] },
  { key: 'fps', label: '초당 프레임', opts: [[15, '15'], [24, '24'], [30, '30']] },
  { key: 'fit', label: '화면 맞춤', opts: [['cover', '꽉 채우기'], ['contain', '전체 보기']] },
  { key: 'mirror', label: '전면 카메라 좌우 반전(거울)', opts: [[true, '켜기'], [false, '끄기']] },
  { key: 'landDir', label: '가로 모드 방향', opts: [[90, '왼쪽으로 눕힘'], [270, '오른쪽으로 눕힘']] },
];
function buildSheet() {
  const body = $('sheetBody');
  body.innerHTML = '';
  OPTIONS.forEach((o) => {
    const wrap = document.createElement('div'); wrap.className = 'opt';
    wrap.innerHTML = `<h3>${o.label}</h3>`;
    const chips = document.createElement('div'); chips.className = 'chips';
    o.opts.forEach(([val, txt]) => {
      const c = document.createElement('button');
      c.className = 'chip' + (S[o.key] === val ? ' on' : '');
      c.textContent = txt;
      c.addEventListener('click', () => { setOption(o.key, val); buildSheet(); });
      chips.appendChild(c);
    });
    wrap.appendChild(chips); body.appendChild(wrap);
  });
  const act = document.createElement('div'); act.className = 'opt';
  act.innerHTML = '<h3>기타</h3>';
  const chips = document.createElement('div'); chips.className = 'chips';
  const fsOK = document.fullscreenEnabled || document.webkitFullscreenEnabled;
  if (fsOK) {
    const fs = document.createElement('button'); fs.className = 'chip';
    fs.textContent = document.fullscreenElement ? '전체화면 종료' : '전체화면 (방향 잠금)';
    fs.addEventListener('click', toggleFullscreen); chips.appendChild(fs);
  }
  const clr = document.createElement('button'); clr.className = 'chip danger'; clr.textContent = '기록 비우기';
  clr.addEventListener('click', () => { clearBuffer(); buildSheet(); toast('기록을 비웠습니다'); });
  chips.appendChild(clr);
  act.appendChild(chips); body.appendChild(act);

  const info = document.createElement('div'); info.className = 'info';
  const dur = frames.length ? (frames[frames.length - 1].t - frames[0].t) / 1000 : 0;
  info.innerHTML = `기록: ${dur.toFixed(1)}초 · ${(bytes / 1048576).toFixed(1)}MB · ${cap.width}×${cap.height}<br>` +
    '팁: 기기 자동회전과 상관없이 화면은 <b>회전 버튼</b>으로만 바뀝니다. ' +
    'Android는 전체화면 또는 홈 화면에 추가하면 방향이 시스템 수준에서 잠깁니다.';
  body.appendChild(info);
}
function setOption(key, val) {
  S[key] = val; saveSettings();
  if (key === 'delay') { goLive(); evict(); }
  if (key === 'bufferSec') evict();
  if (key === 'quality') setCapSize();
  if (key === 'fit' || key === 'mirror') draw();
  if (key === 'landDir') { applyLayout(true); if (document.fullscreenElement || isStandalone()) lockOrientation(); }
  refreshButtons();
}
function openSheet() { buildSheet(); $('sheet').hidden = false; }
function closeSheet() { $('sheet').hidden = true; }
on('sheetClose', closeSheet);
$('sheet').addEventListener('click', (e) => { if (e.target.id === 'sheet') closeSheet(); });

function isStandalone() {
  return (window.matchMedia && matchMedia('(display-mode: fullscreen), (display-mode: standalone)').matches) || navigator.standalone === true;
}
async function toggleFullscreen() {
  try {
    if (!document.fullscreenElement && !document.webkitFullscreenElement) {
      const d = document.documentElement;
      await (d.requestFullscreen ? d.requestFullscreen({ navigationUI: 'hide' }) : d.webkitRequestFullscreen());
      await lockOrientation();
    } else {
      await (document.exitFullscreen ? document.exitFullscreen() : document.webkitExitFullscreen());
    }
  } catch (e) { toast('전체화면을 사용할 수 없습니다'); }
  setTimeout(() => { applyLayout(true); if (!$('sheet').hidden) buildSheet(); }, 300);
}

/* ---------------- 화면 꺼짐 방지 ---------------- */
let wakeLock = null;
async function keepAwake() {
  try { if ('wakeLock' in navigator && !document.hidden) { wakeLock = await navigator.wakeLock.request('screen'); } } catch (e) {}
}
document.addEventListener('visibilitychange', () => {
  if (document.hidden || !started) return;
  keepAwake();
  if (!track || track.readyState === 'ended') startCamera();
  applyLayout(true);
});

/* ---------------- 제스처 차단 (확대/스크롤/당겨서 새로고침) ---------------- */
document.addEventListener('touchmove', (e) => { if (!e.target.closest('.scroll')) e.preventDefault(); }, { passive: false });
document.addEventListener('gesturestart', (e) => e.preventDefault());
document.addEventListener('dblclick', (e) => e.preventDefault());
document.addEventListener('contextmenu', (e) => e.preventDefault());

/* ---------------- 키보드 (PC 테스트용) ---------------- */
document.addEventListener('keydown', (e) => {
  if (!started) return;
  if (e.code === 'Space') { e.preventDefault(); togglePlay(); }
  else if (e.key === 'ArrowLeft') step(-1);
  else if (e.key === 'ArrowRight') step(1);
  else if (e.key === 'l' || e.key === 'L') goLive();
  else if (e.key === 'r' || e.key === 'R') $('bRotate').click();
});

/* ---------------- 시작 ---------------- */
$('startBtn').addEventListener('click', async () => {
  $('startHint').textContent = '카메라 연결 중…';
  const ok = await startCamera();
  if (!ok) return;
  started = true;
  $('start').hidden = true;
  goLive();
  keepAwake();
  if (isStandalone()) lockOrientation();
});

let lastTick = performance.now();
function tick(now) {
  const dt = Math.min(now - lastTick, 250);
  lastTick = now;
  applyLayout(false);              // 매 프레임 확인 → 시스템 회전을 즉시 상쇄
  if (started) {
    capture(now);
    updatePlayhead(now, dt);
    showFrame();
  }
  updateUI(now);
  requestAnimationFrame(tick);
}

applyLayout(true);
refreshButtons();
requestAnimationFrame(tick);

if ('serviceWorker' in navigator && (location.protocol === 'https:' || location.hostname === 'localhost')) {
  window.addEventListener('load', () => navigator.serviceWorker.register('sw.js').catch(() => {}));
}

// 테스트/디버그용 핸들
window.__delaycam = { S, frames, lay, get playT() { return playT; }, get state() { return { playing, speed, recording, loopA, loopB, loopOn }; } };
})();
