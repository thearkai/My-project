/* =========================================================================
   ACTIN CALC — script.js
   A fully functional clone of the Casio fx-991EX CLASSWIZ.
   Plain vanilla JavaScript. No libraries, no modules, no build step.

   HOW THE CODE IS ORGANISED
     0. Tiny helpers + global state
     1. Complex number engine (every value is complex-aware)
     2. Matrix / vector engine
     3. BASE-N helpers (BigInt, 64-bit two's complement)
     4. Number formatting (Fix/Sci/Norm, ENG, DMS, S<->D exact forms)
     5. Tokenizer helpers + expression building (what keys insert)
     6. Parser (tokens -> AST)
     7. Evaluator (AST -> value) + scientific function library
     8. Calculus / solver meta functions (Sigma, Pi, integral, d/dx, SOLVE, CALC)
     9. LCD rendering (lines, indicators, auto-shrink, scrolling)
    10. On-screen menus, prompts and data editors
    11. Key table (the fx-991EX keypad) + key handling
    12. Modes: EQN, STAT, MATRIX, VECTOR, TABLE, RATIO, DIST, INEQ, VERIF, BASE-N
    13. Keyboard support, history, startup
   ========================================================================= */

'use strict';

/* ------------------------------------------------------------------ *
 * 0. TINY HELPERS + GLOBAL STATE
 * ------------------------------------------------------------------ */

function $(id) { return document.getElementById(id); }
function el(tag, cls, txt) {
  var e = document.createElement(tag);
  if (cls) e.className = cls;
  if (txt != null) e.textContent = txt;
  return e;
}
function clamp(v, a, b) { return v < a ? a : (v > b ? b : v); }

/** Any maths problem (Math ERROR) is reported by throwing one of these. */
function CalcError(msg) { this.name = 'CalcError'; this.message = msg; }
CalcError.prototype = Object.create(Error.prototype);
CalcError.prototype.constructor = CalcError;
function mathError() { throw new CalcError('Math ERROR'); }
function syntaxError() { throw new CalcError('Syntax ERROR'); }

/** The whole calculator lives in this one object. */
var state = {
  mode: 'COMP',          // COMP CMPLX STAT BASE-N EQN MATRIX VECTOR TABLE RATIO DIST INEQ VERIF
  angle: 'DEG',          // DEG | RAD | GRAD
  display: 'Norm',       // Fix | Sci | Norm
  dispDigits: 10,        // digits used by Fix/Sci (and Norm = 10 significant)
  mathIO: true,          // Math (exact forms) vs Line (decimals)
  eng: false,            // engineering notation toggle for the current result

  shift: false,          // SHIFT armed
  alpha: false,          // ALPHA armed
  sto: false,            // STO pending (waiting for a variable key)
  rcl: false,            // RCL pending
  hyp: false,            // hyp pressed (next sin/cos/tan is hyperbolic)

  tokens: [],            // the expression, as an array of token objects
  justEquals: false,     // true right after "=" was pressed
  error: false,          // true when the display shows an error message

  result: null,          // last computed value
  resultForms: [],       // alternative strings for S<->D
  resultForm: 0,
  resultIsDMS: false,

  ans: null,             // last answer (C)
  preAns: null,          // answer before that
  hasAns: false,

  vars: null,            // A B C D E F X Y M
  memory: null,          // independent memory M+
  memUsed: false,

  menu: null,            // {title,items,page,sel}
  editor: null,          // {kind,...} active data editor
  prompt: null,          // {label,value,onDone}

  stats: { two: false, x: [], y: [], reg: null },
  mats: { MatA: null, MatB: null, MatC: null },
  vcts: { VctA: null, VctB: null, VctC: null },
  matAns: null,

  base: 'DEC',           // DEC HEX BIN OCT
  eqn: { type: 'quad', deg: 0, n: 2, coef: null },
  tbl: { f: 'X²', start: 1, end: 5, step: 1, g: '' },

  history: [],
  histIndex: -1
};

/* ------------------------------------------------------------------ *
 * 1. COMPLEX NUMBER ENGINE
 *    Every numeric value in this calculator is a complex number
 *    {re, im}. Real values simply have im === 0, which is why one
 *    single evaluator can serve both COMP and COMPLEX (CMPLX) mode.
 * ------------------------------------------------------------------ */

function C(re, im) { return { re: (re || 0), im: (im || 0) }; }
function cclone(z) { return { re: z.re, im: z.im }; }
function cisReal(z) { return Math.abs(z.im) < 1e-12 * Math.max(1, Math.abs(z.re)); }
function cadd(a, b) { return C(a.re + b.re, a.im + b.im); }
function csub(a, b) { return C(a.re - b.re, a.im - b.im); }
function cmul(a, b) { return C(a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re); }
function cdiv(a, b) {
  var d = b.re * b.re + b.im * b.im;
  if (d === 0) mathError();
  return C((a.re * b.re + a.im * b.im) / d, (a.im * b.re - a.re * b.im) / d);
}
function cneg(a) { return C(-a.re, -a.im); }
function cabs(a) { return Math.hypot(a.re, a.im); }
function carg(a) { return Math.atan2(a.im, a.re); }
function cscale(a, k) { return C(a.re * k, a.im * k); }
function cconj(a) { return C(a.re, -a.im); }
function cexp(a) { var e = Math.exp(a.re); return C(e * Math.cos(a.im), e * Math.sin(a.im)); }
function cln(a) {
  var m = cabs(a);
  if (m === 0) mathError();
  return C(Math.log(m), carg(a));
}
function csqrt(a) {
  var r = Math.sqrt(cabs(a)), t = carg(a) / 2;
  return C(r * Math.cos(t), r * Math.sin(t));
}
function cpowInt(a, n) {
  var r = C(1, 0), base = a, neg = n < 0, k = Math.abs(n);
  while (k > 0) {
    if (k & 1) r = cmul(r, base);
    base = cmul(base, base);
    k = Math.floor(k / 2);
  }
  return neg ? cdiv(C(1, 0), r) : r;
}
function cpow(a, b) {
  if (a.re === 0 && a.im === 0) {
    if (b.re > 0 && Math.abs(b.im) < 1e-12) return C(0, 0);
    mathError();
  }
  // fast, exact path for integer exponents
  if (Math.abs(b.im) < 1e-12 && Math.abs(b.re) < 1e9 && Math.abs(b.re - Math.round(b.re)) < 1e-12) {
    return cpowInt(a, Math.round(b.re));
  }
  // negative real base to a fractional power is undefined in COMP mode
  if (state.mode !== 'CMPLX' && Math.abs(a.im) < 1e-12 && a.re < 0) mathError();
  return cexp(cmul(b, cln(a)));
}
function csin(z) { return C(Math.sin(z.re) * Math.cosh(z.im), Math.cos(z.re) * Math.sinh(z.im)); }
function ccos(z) { return C(Math.cos(z.re) * Math.cosh(z.im), -Math.sin(z.re) * Math.sinh(z.im)); }
function ctan(z) { return cdiv(csin(z), ccos(z)); }
function ccot(z) { return cdiv(ccos(z), csin(z)); }
function csinh(z) { return C(Math.sinh(z.re) * Math.cos(z.im), Math.cosh(z.re) * Math.sin(z.im)); }
function ccosh(z) { return C(Math.cosh(z.re) * Math.cos(z.im), Math.sinh(z.re) * Math.sin(z.im)); }
function ctanh(z) { return cdiv(csinh(z), ccosh(z)); }
function casin(z) { return cmul(C(0, -1), cln(cadd(cmul(C(0, 1), z), csqrt(csub(C(1, 0), cmul(z, z)))))); }
function cacos(z) { return csub(C(Math.PI / 2, 0), casin(z)); }
function catan(z) {
  var i = C(0, 1);
  return cdiv(cln(cdiv(cadd(C(1, 0), cmul(i, z)), csub(C(1, 0), cmul(i, z)))), C(0, 2));
}
function casinh(z) { return cln(cadd(z, csqrt(cadd(cmul(z, z), C(1, 0))))); }
function cacosh(z) { return cln(cadd(z, csqrt(csub(cmul(z, z), C(1, 0))))); }
function catanh(z) { return cdiv(cln(cdiv(cadd(C(1, 0), z), csub(C(1, 0), z))), C(2, 0)); }

/* --- angle units --------------------------------------------------- */
var ANG = {
  DEG:  { to: Math.PI / 180,  from: 180 / Math.PI,  sym: 'D' },
  RAD:  { to: 1,              from: 1,              sym: 'R' },
  GRAD: { to: Math.PI / 200,  from: 200 / Math.PI,  sym: 'G' }
};
/** value -> radians (used before sin/cos/tan) */
function toRad(z) { return cscale(z, ANG[state.angle].to); }
/** radians -> value (used after asin/acos/atan) */
function fromRad(z) { return cscale(z, ANG[state.angle].from); }

/** In COMP mode (not CMPLX) a complex result is an error, like a real Casio. */
function needReal(z) {
  if (state.mode === 'CMPLX') return z;
  if (Math.abs(z.im) > 1e-9 * Math.max(1, Math.abs(z.re))) mathError();
  return C(z.re, 0);
}

/* --- factorial / gamma ---------------------------------------------- */
function factorial(n) {
  if (!isFinite(n) || n < 0 || Math.abs(n - Math.round(n)) > 1e-12) mathError();
  var r = 1;
  for (var i = 2; i <= n; i++) r *= i;
  return C(r, 0);
}
/** Lanczos gamma — used by the distribution mode. */
function gammaFn(x) {
  if (x < 0.5) return Math.PI / (Math.sin(Math.PI * x) * gammaFn(1 - x));
  x -= 1;
  var g = [676.5203681218851, -1259.1392167224028, 771.32342877765313,
           -176.61502916214059, 12.507343278686905, -0.13857109526572012,
           9.9843695780195716e-6, 1.5056327351493116e-7];
  var a = 0.99999999999980993, t = x + 7.5;
  for (var i = 0; i < g.length; i++) a += g[i] / (x + i + 1);
  return Math.sqrt(2 * Math.PI) * Math.pow(t, x + 0.5) * Math.exp(-t) * a;
}

/* ------------------------------------------------------------------ *
 * 2. MATRIX + VECTOR ENGINE
 * ------------------------------------------------------------------ */

function Mat(rows, cols, data) {
  var d = data || [];
  while (d.length < rows * cols) d.push(C(0, 0));
  return { kind: 'mat', rows: rows, cols: cols, data: d };
}
function Vct(n, data) {
  var d = data || [];
  while (d.length < n) d.push(C(0, 0));
  return { kind: 'vct', n: n, data: d };
}
function isMat(v) { return !!v && v.kind === 'mat'; }
function isVct(v) { return !!v && v.kind === 'vct'; }
function isNum(v) { return !!v && v.re !== undefined && v.kind === undefined; }

function matClone(m) { return Mat(m.rows, m.cols, m.data.map(cclone)); }
function vctClone(v) { return Vct(v.n, v.data.map(cclone)); }

function matAdd(a, b) {
  if (a.rows !== b.rows || a.cols !== b.cols) mathError();
  var d = [];
  for (var i = 0; i < a.data.length; i++) d.push(cadd(a.data[i], b.data[i]));
  return Mat(a.rows, a.cols, d);
}
function matSub(a, b) {
  if (a.rows !== b.rows || a.cols !== b.cols) mathError();
  var d = [];
  for (var i = 0; i < a.data.length; i++) d.push(csub(a.data[i], b.data[i]));
  return Mat(a.rows, a.cols, d);
}
function matMul(a, b) {
  if (a.cols !== b.rows) mathError();
  var d = [], r, c, k, s;
  for (r = 0; r < a.rows; r++) {
    for (c = 0; c < b.cols; c++) {
      s = C(0, 0);
      for (k = 0; k < a.cols; k++) s = cadd(s, cmul(a.data[r * a.cols + k], b.data[k * b.cols + c]));
      d.push(s);
    }
  }
  return Mat(a.rows, b.cols, d);
}
function matScale(m, z) {
  return Mat(m.rows, m.cols, m.data.map(function (x) { return cmul(x, z); }));
}
function matTrn(m) {
  var d = [], r, c;
  for (r = 0; r < m.cols; r++) for (c = 0; c < m.rows; c++) d.push(m.data[c * m.cols + r]);
  return Mat(m.cols, m.rows, d);
}
/** Determinant by Gaussian elimination with partial pivoting (complex safe). */
function matDet(m) {
  if (m.rows !== m.cols) mathError();
  var n = m.rows, a = m.data.map(cclone), det = C(1, 0), i, j, k, piv, tmp;
  for (i = 0; i < n; i++) {
    piv = i;
    for (j = i + 1; j < n; j++) if (cabs(a[j * n + i]) > cabs(a[piv * n + i])) piv = j;
    if (cabs(a[piv * n + i]) < 1e-14) return C(0, 0);
    if (piv !== i) {
      for (j = 0; j < n; j++) { tmp = a[i * n + j]; a[i * n + j] = a[piv * n + j]; a[piv * n + j] = tmp; }
      det = cneg(det);
    }
    det = cmul(det, a[i * n + i]);
    for (j = i + 1; j < n; j++) {
      var f = cdiv(a[j * n + i], a[i * n + i]);
      for (k = i; k < n; k++) a[j * n + k] = csub(a[j * n + k], cmul(f, a[i * n + k]));
    }
  }
  return det;
}
/** Inverse by Gauss-Jordan. Throws Math ERROR for singular matrices. */
function matInv(m) {
  if (m.rows !== m.cols) mathError();
  var n = m.rows, i, j, k;
  var a = m.data.map(cclone);
  var b = [];
  for (i = 0; i < n; i++) for (j = 0; j < n; j++) b.push(i === j ? C(1, 0) : C(0, 0));
  for (i = 0; i < n; i++) {
    var piv = i;
    for (j = i + 1; j < n; j++) if (cabs(a[j * n + i]) > cabs(a[piv * n + i])) piv = j;
    if (cabs(a[piv * n + i]) < 1e-14) mathError();
    if (piv !== i) {
      for (j = 0; j < n; j++) {
        var t1 = a[i * n + j]; a[i * n + j] = a[piv * n + j]; a[piv * n + j] = t1;
        var t2 = b[i * n + j]; b[i * n + j] = b[piv * n + j]; b[piv * n + j] = t2;
      }
    }
    var d = a[i * n + i];
    for (j = 0; j < n; j++) { a[i * n + j] = cdiv(a[i * n + j], d); b[i * n + j] = cdiv(b[i * n + j], d); }
    for (j = 0; j < n; j++) {
      if (j === i) continue;
      var f = a[j * n + i];
      for (k = 0; k < n; k++) {
        a[j * n + k] = csub(a[j * n + k], cmul(f, a[i * n + k]));
        b[j * n + k] = csub(b[j * n + k], cmul(f, b[i * n + k]));
      }
    }
  }
  return Mat(n, n, b);
}
/** solves A x = b  (A square, b vector) */
function matSolve(A, bvec) {
  var n = A.rows;
  if (bvec.n !== n) mathError();
  var a = A.data.map(cclone), rhs = bvec.data.map(cclone), i, j, k;
  for (i = 0; i < n; i++) {
    var piv = i;
    for (j = i + 1; j < n; j++) if (cabs(a[j * n + i]) > cabs(a[piv * n + i])) piv = j;
    if (cabs(a[piv * n + i]) < 1e-14) return null;   // singular
    if (piv !== i) {
      for (j = 0; j < n; j++) { var t = a[i * n + j]; a[i * n + j] = a[piv * n + j]; a[piv * n + j] = t; }
      var tr = rhs[i]; rhs[i] = rhs[piv]; rhs[piv] = tr;
    }
    var d = a[i * n + i];
    for (j = i; j < n; j++) a[i * n + j] = cdiv(a[i * n + j], d);
    rhs[i] = cdiv(rhs[i], d);
    for (j = 0; j < n; j++) {
      if (j === i) continue;
      var f = a[j * n + i];
      for (k = i; k < n; k++) a[j * n + k] = csub(a[j * n + k], cmul(f, a[i * n + k]));
      rhs[j] = csub(rhs[j], cmul(f, rhs[i]));
    }
  }
  return Vct(n, rhs);
}
/** Solve a real linear system given as nested arrays (used by regressions). */
function solveLinear(A, b) {
  var n = b.length, i, j, k;
  var M = A.map(function (row, r) { return row.slice().concat([b[r]]); });
  for (i = 0; i < n; i++) {
    var piv = i;
    for (j = i + 1; j < n; j++) if (Math.abs(M[j][i]) > Math.abs(M[piv][i])) piv = j;
    if (Math.abs(M[piv][i]) < 1e-14) return null;
    var tmp = M[i]; M[i] = M[piv]; M[piv] = tmp;
    var d = M[i][i];
    for (j = i; j <= n; j++) M[i][j] /= d;
    for (j = 0; j < n; j++) {
      if (j === i) continue;
      var f = M[j][i];
      for (k = i; k <= n; k++) M[j][k] -= f * M[i][k];
    }
  }
  return M.map(function (row) { return row[n]; });
}

function vctAdd(a, b) { chkDim(a, b); return Vct(a.n, a.data.map(function (x, i) { return cadd(x, b.data[i]); })); }
function vctSub(a, b) { chkDim(a, b); return Vct(a.n, a.data.map(function (x, i) { return csub(x, b.data[i]); })); }
function chkDim(a, b) { if (a.n !== b.n) mathError(); }
function vctDot(a, b) {
  chkDim(a, b);
  var s = C(0, 0);
  for (var i = 0; i < a.n; i++) s = cadd(s, cmul(a.data[i], b.data[i]));
  return s;
}
function vctCross(a, b) {
  if (a.n !== 3 || b.n !== 3) mathError();
  return Vct(3, [
    csub(cmul(a.data[1], b.data[2]), cmul(a.data[2], b.data[1])),
    csub(cmul(a.data[2], b.data[0]), cmul(a.data[0], b.data[2])),
    csub(cmul(a.data[0], b.data[1]), cmul(a.data[1], b.data[0]))
  ]);
}
function vctMag(v) {
  var s = 0;
  for (var i = 0; i < v.n; i++) s += Math.pow(cabs(v.data[i]), 2);
  return C(Math.sqrt(s), 0);
}
function vctScale(v, z) { return Vct(v.n, v.data.map(function (x) { return cmul(x, z); })); }

/* ------------------------------------------------------------------ *
 * 3. BASE-N HELPERS  (64-bit signed, two's complement)
 * ------------------------------------------------------------------ */
var BASE_INFO = { DEC: { r: 10, p: '' }, HEX: { r: 16, p: 'H' }, BIN: { r: 2, p: 'b' }, OCT: { r: 8, p: 'o' } };
var BITS = 64n, MOD = 1n << 64n, HALF = 1n << 63n;

function wrapSigned(v) {
  v = ((v % MOD) + MOD) % MOD;
  if (v >= HALF) v -= MOD;
  return v;
}
function toUnsigned(v) { return ((v % MOD) + MOD) % MOD; }
function bigFromText(txt, radix) {
  var s = txt.toUpperCase(), v = 0n, r = BigInt(radix);
  for (var i = 0; i < s.length; i++) {
    var d = parseInt(s[i], radix);
    if (isNaN(d)) syntaxError();
    v = v * r + BigInt(d);
  }
  return v;
}
function bigToText(v, radix) {
  var neg = v < 0n;
  // DEC shows a minus sign; HEX/BIN/OCT show the two's complement (like a real Casio)
  var u = (neg && radix === 10) ? (-v) : toUnsigned(v);
  var r = BigInt(radix), out = '';
  var digits = '0123456789ABCDEF';
  if (u === 0n) return '0';
  while (u > 0n) { out = digits[Number(u % r)] + out; u = u / r; }
  return (neg && radix === 10 ? '-' : '') + out;
}
function baseLabel(v) {
  var t = bigToText(v, BASE_INFO[state.base].r);
  return t + BASE_INFO[state.base].p;
}

/* ------------------------------------------------------------------ *
 * 4. NUMBER FORMATTING
 * ------------------------------------------------------------------ */

function isBad(x) { return !isFinite(x); }

/** Keep the display tidy: values that are 0 to within rounding become 0. */
function clean(x) { return Math.abs(x) < 1e-13 ? 0 : x; }

/** Trim an exponential string: "1.2300000e+15" -> mantissa + "e+15". */
function trimExp(s) {
  var p = s.split('e');
  var m = p[0].indexOf('.') >= 0 ? p[0].replace(/0+$/, '').replace(/\.$/, '') : p[0];
  var e = parseInt(p[1], 10);
  if (m === '0') return '0';
  if (state.mathIO) return m + '×10^' + e;
  return m + 'E' + (e < 0 ? '-' : '+') + Math.abs(e);
}
/** Trim a plain decimal string ("0.3000" -> "0.3"). */
function trimFixed(s) {
  if (s.indexOf('e') >= 0) return trimExp(s);
  if (s.indexOf('.') >= 0) s = s.replace(/0+$/, '').replace(/\.$/, '');
  return s;
}

/**
 * Format one real number according to the current display setting.
 * This is the single place that decides how many digits you see.
 */
function fmtNum(x) {
  if (isBad(x)) mathError();
  x = clean(x);
  if (x === 0) return '0';
  var d = clamp(Math.round(state.dispDigits), 0, 9);
  var s;
  if (state.display === 'Fix') {
    s = x.toFixed(d);
    if (Math.abs(x) >= 1e14) s = x.toExponential(9);
    if (s.indexOf('e') >= 0) return trimExp(s);
    return s;
  }
  if (state.display === 'Sci') {
    return trimExp(x.toExponential(clamp(d, 0, 9)));
  }
  // Norm: 10 significant digits, switching to exponential outside range
  var a = Math.abs(x);
  if (a >= 1e10 || a < 1e-4) return trimExp(x.toExponential(9));
  return trimFixed(String(Number(x.toPrecision(10))));
}

/** Engineering notation: exponent always a multiple of 3. */
function fmtEng(x) {
  if (isBad(x)) mathError();
  x = clean(x);
  if (x === 0) return '0';
  var e = Math.floor(Math.log10(Math.abs(x)));
  var e3 = e - ((e % 3) + 3) % 3;
  var m = x / Math.pow(10, e3);
  // rounding can push the mantissa to 1000
  var ms = String(Number(m.toPrecision(10)));
  if (Math.abs(Number(ms)) >= 1000) { m /= 1000; e3 += 3; ms = String(Number(m.toPrecision(10))); }
  return trimFixed(ms) + '×10^' + e3;
}

/** Complex number -> string ("3+4i", "-2i", "5"). */
function fmtComplex(z) {
  if (isBad(z.re) || isBad(z.im)) mathError();
  var re = clean(z.re), im = clean(z.im);
  var tol = 1e-11 * Math.max(1, Math.abs(re), Math.abs(im));
  if (Math.abs(im) <= tol) return fmtNum(re);
  if (Math.abs(re) <= tol) {
    if (Math.abs(im - 1) < 1e-12) return 'i';
    if (Math.abs(im + 1) < 1e-12) return '-i';
    return fmtNum(im) + 'i';
  }
  return fmtNum(re) + (im < 0 ? '-' : '+') + fmtNum(Math.abs(im)) + 'i';
}

/** Degrees -> D°M'S.SS" */
function fmtDMS(x) {
  if (isBad(x)) mathError();
  var neg = x < 0; x = Math.abs(x);
  var d = Math.floor(x + 1e-12);
  var mm = (x - d) * 60;
  var m = Math.floor(mm + 1e-10);
  var s = (mm - m) * 60;
  if (Math.abs(s - 60) < 1e-9) { s = 0; m += 1; }
  if (m === 60) { m = 0; d += 1; }
  var ss = (Math.round(s * 100) / 100).toFixed(2);
  return (neg ? '-' : '') + d + '°' + m + "'" + ss + '"';
}

/** DMS string (dd.mmss) -> degrees. Used when the user types 30°30' . */
function dmsToDeg(d, m, s) { return (d + m / 60 + (s || 0) / 3600) * (d < 0 ? -1 : 1); }

/* ---- S<->D: exact (fraction / pi / root) forms ---------------------- */
/** Best rational approximation of x with denominator <= maxDen. */
function toFraction(x, maxDen, tol) {
  if (!isFinite(x)) return null;
  var neg = x < 0; x = Math.abs(x);
  if (x === 0) return { n: 0, d: 1 };
  var n1 = 1, d1 = 0, n2 = 0, d2 = 1;      // the two previous convergents
  var b = x, i, a, n, d;
  for (i = 0; i < 40; i++) {
    a = Math.floor(b);
    n = a * n1 + n2;
    d = a * d1 + d2;
    if (d > maxDen) break;
    n2 = n1; d2 = d1; n1 = n; d1 = d;
    if (Math.abs(x - n / d) <= tol * Math.max(1, x)) return { n: neg ? -n : n, d: d };
    var frac = b - a;
    if (frac < 1e-12) break;
    b = 1 / frac;
  }
  return null;
}
function fracStr(f) {
  if (!f) return null;
  if (f.d === 1) return String(f.n);
  return f.n + '/' + f.d;
}
function mixedStr(f) {
  if (!f) return null;
  if (f.d === 1) return String(f.n);
  var neg = f.n < 0, n = Math.abs(f.n), w = Math.floor(n / f.d), r = n % f.d;
  if (w === 0) return (neg ? '-' : '') + r + '/' + f.d;
  return (neg ? '-' : '') + w + ' ' + r + '/' + f.d;
}
/**
 * All the alternative display strings for a value (used by S<->D).
 *   forms[0] = plain decimal, then fraction / mixed / pi / root forms.
 */
function exactForms(z) {
  var forms = [];
  if (!z || z.re === undefined) return forms;
  var x = clean(z.re);
  if (Math.abs(z.im) > 1e-11 || !isFinite(x)) return forms;
  if (Math.abs(x) >= 1e10) return forms;
  var tol = 1e-9;
  var f = toFraction(x, 1000, tol);
  if (f && f.d !== 1) {
    forms.push(mixedStr(f));
    var improper = fracStr(f);
    if (improper !== mixedStr(f)) forms.push(improper);
  }
  // pi multiples:  x = (p/q) * pi
  var fp = toFraction(x / Math.PI, 100, 1e-8);
  if (fp && fp.d !== 0 && Math.abs(fp.n / fp.d * Math.PI - x) < 1e-8) {
    var s = (fp.d === 1 ? '' : '/' + fp.d);
    if (fp.n === 1) forms.push('π' + s);
    else if (fp.n === -1) forms.push('-π' + s);
    else forms.push(fp.n + 'π' + s);
  }
  // simple square roots: x = (p/q) * sqrt(k)
  var sqrtK;
  for (var k = 2; k <= 220 && forms.length < 6; k++) {
    sqrtK = Math.sqrt(k);
    if (Math.abs(sqrtK - Math.round(sqrtK)) < 1e-12) continue;      // skip 4, 9, 16 ...
    var r = x / sqrtK;
    var fr = toFraction(r, 60, 1e-8);
    if (fr && fr.d !== 0 && Math.abs(fr.n / fr.d * Math.sqrt(k) - x) < 1e-8 && Math.abs(fr.n) <= 200) {
      var head = (fr.d === 1 ? '' : fr.n + '/') ;
      var body = (fr.d === 1 ? (Math.abs(fr.n) === 1 ? '' : String(Math.abs(fr.n))) : String(Math.abs(fr.n)));
      var sgn = (fr.n < 0 ? '-' : '');
      var txt = sgn + (fr.d === 1 ? body : body + '/' + fr.d) + '√' + k;
      forms.push(txt);
      break;
    }
  }
  return forms;
}

/** Turn any value into the string shown on the result line. */
function valueToString(v) {
  if (v === null || v === undefined) return '';
  if (v.kind === 'mat' || v.kind === 'vct') return 'Mat/Vct';   // drawn in the editor instead
  if (v.kind === 'pair') {
    return v.labels.map(function (L, i) {
      return L + '=' + (state.mathIO ? fmtComplex(v.values[i]) : fmtNum(clean(v.values[i].re)));
    }).join(',  ');
  }
  if (state.eng) return fmtEng(clean(v.re));
  return fmtComplex(v);
}
/* =========================================================================
   5. TOKENS — the expression is stored as an array of token objects
   ========================================================================= */

function tok(t, v, extra) {
  var o = { t: t, v: v };
  if (extra) for (var k in extra) o[k] = extra[k];
  return o;
}
function numTok(m, e) { return tok('num', null, { m: m, e: (e === undefined ? null : e) }); }
function opTok(v) { return tok('op', v); }
function fnTok(v, disp, noargs) { return tok('fn', v, { s: disp, noargs: !!noargs }); }
function lpTok() { return tok('lp'); }
function rpTok() { return tok('rp'); }
function postTok(v) { return tok('post', v); }

var OP_TEXT = { '+': '+', '-': '−', '*': '×', '/': '÷', '^': '^', 'mod': 'mod',
                'and': 'and', 'or': 'or', 'xor': 'xor', 'xnor': 'xnor' };

/** How one token is drawn on the display. */
function tokText(t) {
  switch (t.t) {
    case 'num':   return t.m + (t.e !== null && t.e !== undefined ? '×10^' + t.e : '');
    case 'op':    return OP_TEXT[t.v] || t.v;
    case 'post':  return t.v;
    case 'lp':    return '(';
    case 'rp':    return ')';
    case 'fn':    return t.s !== undefined ? t.s : (t.v + '(');
    case 'var':   return t.v;
    case 'const': return t.v;
    case 'ans':   return 'Ans';
    case 'preans':return 'PreAns';
    case 'i':     return 'i';
    case 'mat':   return t.v;
    case 'vct':   return t.v;
    case 'dms':   return '°';
  }
  return '';
}
function exprText(toks) {
  var s = '';
  for (var i = 0; i < (toks || state.tokens).length; i++) s += tokText(toks[i]);
  return s;
}
/** numeric value of a number token (mantissa + optional ×10^ exponent) */
function numValue(t) {
  var s = t.m;
  if (t.e !== null && t.e !== undefined && t.e !== '') s += 'e' + t.e;
  var v = parseFloat(s);
  if (isNaN(v)) return 0;
  return v;
}
/** A token that can begin a value (used for implicit multiplication). */
function startsPrimary(t) {
  return !!t && (t.t === 'num' || t.t === 'lp' || t.t === 'fn' || t.t === 'var' ||
                 t.t === 'const' || t.t === 'ans' || t.t === 'preans' ||
                 t.t === 'i' || t.t === 'mat' || t.t === 'vct');
}

/* =========================================================================
   6. PARSER  (token array -> AST)
   Grammar (lowest to highest precedence):
     expr   := logic
     logic  := add (('and'|'or'|'xor'|'xnor') add)*        (BASE-N)
     add    := mul (('+'|'-') mul [%])*
     mul    := unary (('×'|'÷'|'mod'| implicit) unary)*
     unary  := '-' unary | 'not' unary | 'neg' unary | power
     power  := postfix ('^' unary)?                        (right associative)
     postfix:= primary ('!'|'²'|'³'|'⁻¹'|'%')*
     primary:= num | var | const | Ans | i | MatA | VctA | '(' expr ')' | fn '(' args ')'
   ========================================================================= */

/* Functions whose arguments are captured as RAW token slices, because they
   need to be evaluated many times with a variable bound to different values. */
var RAW_FNS = { 'sum': 1, 'prod': 1, 'intg': 1, 'diff': 1, 'solve': 1 };

function Parser(tokens) { this.t = tokens; this.i = 0; }

Parser.prototype = {
  peek: function (o) { return this.t[this.i + (o || 0)]; },
  next: function () { return this.t[this.i++]; },
  atEnd: function () { return this.i >= this.t.length; },

  parseAll: function () {
    if (!this.t.length) syntaxError();
    var n = this.parseExpr();
    if (!this.atEnd()) syntaxError();      // leftovers => Syntax ERROR
    return n;
  },
  parseExpr: function () { return this.parseLogic(); },

  parseLogic: function () {
    var l = this.parseAdd();
    while (!this.atEnd()) {
      var p = this.peek();
      if (p.t === 'op' && (p.v === 'and' || p.v === 'or' || p.v === 'xor' || p.v === 'xnor')) {
        this.next();
        l = { k: 'bin', op: p.v, l: l, r: this.parseAdd() };
      } else break;
    }
    return l;
  },

  parseAdd: function () {
    var l = this.parseMul(false);
    while (!this.atEnd()) {
      var p = this.peek();
      if (p.t === 'op' && (p.v === '+' || p.v === '-')) {
        this.next();
        /* The right hand side is parsed with noPercent = true so that the '+'
           branch below can turn   200 + 10 %   into   200 + 200*10/100,
           exactly like a real Casio. */
        var r = this.parseMul(true);
        var nx = this.peek();
        if (nx && nx.t === 'post' && nx.v === '%') {
          this.next();
          l = { k: 'pct', op: p.v, base: l, x: r };
        } else {
          l = { k: 'bin', op: p.v, l: l, r: r };
        }
      } else break;
    }
    return l;
  },

  parseMul: function (noPercent) {
    var l = this.parseUnary();
    while (!this.atEnd()) {
      var p = this.peek();
      var op = null;
      if (p.t === 'op' && (p.v === '*' || p.v === '/' || p.v === 'mod')) { this.next(); op = p.v; }
      else if (startsPrimary(p)) { op = '*'; }          // implicit multiplication: 2π, 3(4), 5sin(30)
      else break;
      l = { k: 'bin', op: op, l: l, r: this.parseUnary() };
    }
    // a lone % simply means "divide by 100":  20 % -> 0.2,  100×10 % -> 10
    if (!noPercent) {
      var pc = this.peek();
      if (pc && pc.t === 'post' && pc.v === '%') { this.next(); l = { k: 'post', op: '%', x: l }; }
    }
    return l;
  },

  parseUnary: function () {
    var p = this.peek();
    if (p && p.t === 'op' && p.v === '-') { this.next(); return { k: 'neg', x: this.parseUnary() }; }
    if (p && p.t === 'op' && p.v === '+') { this.next(); return this.parseUnary(); }
    if (p && p.t === 'op' && (p.v === 'not' || p.v === 'bneg')) {
      this.next(); return { k: 'unaryfn', name: p.v, x: this.parseUnary() };
    }
    return this.parsePower();
  },

  parsePower: function () {
    var b = this.parsePostfix();
    var p = this.peek();
    if (p && p.t === 'op' && p.v === '^') {
      this.next();
      return { k: 'bin', op: '^', l: b, r: this.parseUnary() };   // right assoc: 2^3^2 = 2^9
    }
    return b;
  },

  parsePostfix: function () {
    var x = this.parsePrimary();
    while (!this.atEnd()) {
      var p = this.peek();
      // '%' is handled one level up (see parseMul / parseAdd)
      if (p && p.t === 'post' && p.v !== '%') { this.next(); x = { k: 'post', op: p.v, x: x }; }
      else break;
    }
    return x;
  },

  parsePrimary: function () {
    var p = this.next();
    if (!p) syntaxError();
    switch (p.t) {
      case 'num': {
        // optional degrees/minutes/seconds:  1°30°45°  ->  1.508...
        var v = numValue(p);
        if (this.peek() && this.peek().t === 'dms') {
          var parts = [v];
          while (this.peek() && this.peek().t === 'dms') {
            this.next();
            var q = this.peek();
            if (q && q.t === 'num') { parts.push(numValue(q)); this.next(); }
            else { parts.push(0); break; }
          }
          var d = Math.abs(parts[0]), m = parts[1] || 0, s = parts[2] || 0;
          v = (d + m / 60 + s / 3600) * (parts[0] < 0 ? -1 : 1);
        }
        return { k: 'num', v: C(v, 0), raw: p };
      }
      case 'var':    return { k: 'var', name: p.v };
      case 'const':  return { k: 'const', name: p.v };
      case 'ans':    return { k: 'ans' };
      case 'preans': return { k: 'preans' };
      case 'i':      return { k: 'i' };
      case 'mat':    return { k: 'mat', name: p.v };
      case 'vct':    return { k: 'vct', name: p.v };
      case 'lp': {
        var inner = this.parseExpr();
        var r = this.next();
        if (!r || r.t !== 'rp') syntaxError();
        return inner;
      }
      case 'fn': {
        if (p.noargs) return { k: 'fn', name: p.v, args: [] };
        var rp = this.peek();
        if (!rp || rp.t !== 'lp') syntaxError();
        if (RAW_FNS[p.v]) {
          return { k: 'raw', name: p.v, args: this.captureArgs() };
        }
        return { k: 'fn', name: p.v, args: this.parseArgs() };
      }
    }
    syntaxError();
  },

  /** Normal argument list: '(' expr (',' expr)* ')'  ->  array of AST nodes */
  parseArgs: function () {
    this.next();                                   // consume '('
    var args = [];
    if (this.peek() && this.peek().t === 'rp') { this.next(); return args; }
    for (;;) {
      args.push(this.parseExpr());
      var p = this.next();
      if (!p) syntaxError();
      if (p.t === 'comma') continue;
      if (p.t === 'rp') break;
      syntaxError();
    }
    return args;
  },

  /** Capture argument lists as RAW token slices (for Σ, Π, ∫, d/dx, SOLVE). */
  captureArgs: function () {
    this.next();                                   // consume the outer '('
    var args = [[]], depth = 0;
    while (!this.atEnd()) {
      var p = this.next();
      if (p.t === 'lp') { depth++; args[args.length - 1].push(p); continue; }
      if (p.t === 'rp') {
        if (depth === 0) return args;              // the closing bracket of the call
        depth--;
        args[args.length - 1].push(p);
        continue;
      }
      if (p.t === 'comma' && depth === 0) { args.push([]); continue; }
      args[args.length - 1].push(p);
    }
    syntaxError();
  }
};

function parseTokens(tokens) { return new Parser(tokens).parseAll(); }

/* =========================================================================
   7. EVALUATOR (AST -> value) + SCIENTIFIC FUNCTION LIBRARY
   ========================================================================= */

var FNS = {
  /* --- trigonometry (angle unit aware) --- */
  'sin':   { n: 1, f: function (a) { return needReal(csin(toRad(a[0]))); } },
  'cos':   { n: 1, f: function (a) { return needReal(ccos(toRad(a[0]))); } },
  'tan':   { n: 1, f: function (a) { return needReal(ctan(toRad(a[0]))); } },
  'asin':  { n: 1, f: function (a) { return needReal(fromRad(casin(a[0]))); } },
  'acos':  { n: 1, f: function (a) { return needReal(fromRad(cacos(a[0]))); } },
  'atan':  { n: 1, f: function (a) { return needReal(fromRad(catan(a[0]))); } },
  /* --- hyperbolic (arguments are plain numbers, not angles) --- */
  'sinh':  { n: 1, f: function (a) { return needReal(csinh(a[0])); } },
  'cosh':  { n: 1, f: function (a) { return needReal(ccosh(a[0])); } },
  'tanh':  { n: 1, f: function (a) { return needReal(ctanh(a[0])); } },
  'asinh': { n: 1, f: function (a) { return needReal(casinh(a[0])); } },
  'acosh': { n: 1, f: function (a) { return needReal(cacosh(a[0])); } },
  'atanh': { n: 1, f: function (a) { return needReal(catanh(a[0])); } },
  /* --- logarithms and exponentials --- */
  'ln':    { n: 1, f: function (a) { return needReal(cln(a[0])); } },
  'log':   { n: -1, f: function (a) {
      if (a.length === 1) return needReal(cdiv(cln(a[0]), C(Math.LN10, 0)));
      if (a.length === 2) return needReal(cdiv(cln(a[1]), cln(a[0])));   // log(a,b) = log base a of b
      syntaxError();
    } },
  'sqrt':  { n: 1, f: function (a) { return needReal(csqrt(a[0])); } },
  'cbrt':  { n: 1, f: function (a) {
      if (Math.abs(a[0].im) < 1e-12) return C(Math.cbrt(a[0].re), 0);
      return cpow(a[0], C(1 / 3, 0));
    } },
  'nroot': { n: 2, f: function (a) { return needReal(cpow(a[0], cdiv(C(1, 0), a[1]))); } },
  'pow10': { n: 1, f: function (a) { return needReal(cpow(C(10, 0), a[0])); } },
  'exp':   { n: 1, f: function (a) { return needReal(cexp(a[0])); } },
  /* --- misc --- */
  'abs':   { n: 1, f: function (a) {
      if (isVct(a[0])) return vctMag(a[0]);
      if (isMat(a[0])) return C(Math.sqrt(cabs(vctMag(Vct(a[0].data.length, a[0].data)))), 0);
      return C(cabs(a[0]), 0);
    } },
  'rnd':   { n: 1, f: function (a) { return C(roundToDisplay(a[0].re), roundToDisplay(a[0].im)); } },
  'ran':   { n: 0, f: function () { return C(Math.floor(Math.random() * 1000) / 1000, 0); } },
  'ranint':{ n: 2, f: function (a) {
      var lo = Math.round(a[0].re), hi = Math.round(a[1].re);
      if (hi < lo) { var t = lo; lo = hi; hi = t; }
      return C(lo + Math.floor(Math.random() * (hi - lo + 1)), 0);
    } },
  /* --- complex --- */
  'arg':   { n: 1, f: function (a) { return C(fromRad(C(carg(a[0]), 0)).re, 0); } },
  'conjg': { n: 1, f: function (a) { return cconj(a[0]); } },
  're':    { n: 1, f: function (a) { return C(a[0].re, 0); } },
  'im':    { n: 1, f: function (a) { return C(a[0].im, 0); } },
  'rangle':{ n: 2, f: function (a) {
      var r = a[0], th = toRad(a[1]);
      return C(r.re * Math.cos(th.re) - r.im * Math.sin(th.re) * 0, 0) &&
             C(cabs(r) * Math.cos(th.re), cabs(r) * Math.sin(th.re));
    } },
  /* --- coordinate conversion, returns TWO values --- */
  'pol':   { n: 2, f: function (a) {
      return { kind: 'pair', labels: ['r', 'θ'],
               values: [C(cabs(C(a[0].re, a[1].re)), 0), fromRad(C(Math.atan2(a[1].re, a[0].re), 0))] };
    } },
  'rec':   { n: 2, f: function (a) {
      var r = a[0].re, th = toRad(a[1]).re;
      return { kind: 'pair', labels: ['x', 'y'], values: [C(r * Math.cos(th), 0), C(r * Math.sin(th), 0)] };
    } },
  /* --- matrices --- */
  'det':   { n: 1, f: function (a) { if (!isMat(a[0])) mathError(); return matDet(a[0]); } },
  'trn':   { n: 1, f: function (a) {
      if (isMat(a[0])) return matTrn(a[0]);
      if (isVct(a[0])) return a[0];
      mathError();
    } },
  'dot':   { n: 2, f: function (a) { if (!isVct(a[0]) || !isVct(a[1])) mathError(); return vctDot(a[0], a[1]); } },
  'cross': { n: 2, f: function (a) { if (!isVct(a[0]) || !isVct(a[1])) mathError(); return vctCross(a[0], a[1]); } }
};

function roundToDisplay(x) {
  if (!isFinite(x)) return x;
  var d = (state.display === 'Fix' || state.display === 'Sci') ? clamp(state.dispDigits, 0, 9) : 10;
  if (state.display === 'Fix') { var p = Math.pow(10, d); return Math.round(x * p) / p; }
  return Number(x.toPrecision(d));
}

function callFn(name, args) {
  var f = FNS[name];
  if (!f) syntaxError();
  if (f.n >= 0 && args.length !== f.n) syntaxError();
  return f.f(args);
}

/* ---- binary operators ------------------------------------------------ */
function binOp(op, l, r) {
  if (isNum(l) && isNum(r)) {
    switch (op) {
      case '+': return cadd(l, r);
      case '-': return csub(l, r);
      case '*': return cmul(l, r);
      case '/': return cdiv(l, r);
      case '^': return cpow(l, r);
      case 'mod': {
        if (Math.abs(l.im) > 1e-12 || Math.abs(r.im) > 1e-12) mathError();
        if (Math.abs(r.re) < 1e-14) mathError();
        return C(l.re - r.re * Math.floor(l.re / r.re), 0);
      }
    }
  }
  if (isMat(l) && isMat(r)) {
    switch (op) {
      case '+': return matAdd(l, r);
      case '-': return matSub(l, r);
      case '*': return matMul(l, r);
      case '/': return matMul(l, matInv(r));
      case '^': return matPower(l, r);
    }
  }
  if (isNum(l) && isMat(r)) {
    if (op === '*') return matScale(r, l);
    if (op === '+' || op === '-') mathError();
  }
  if (isMat(l) && isNum(r)) {
    if (op === '*' || op === '/') { if (op === '/') return matScale(l, cdiv(C(1, 0), r)); return matScale(l, r); }
    if (op === '+') return matAdd(l, matScale(Mat(r.rows === undefined ? l.rows : l.rows, l.cols,
                       new Array(l.rows * l.cols).fill(0).map(function () { return cclone(r); }))));
  }
  if (isNum(l) && isVct(r)) { if (op === '*') return vctScale(r, l); }
  if (isVct(l) && isNum(r)) { if (op === '*') return vctScale(l, r); if (op === '/') return vctScale(l, cdiv(C(1, 0), r)); }
  if (isVct(l) && isVct(r)) {
    if (op === '+') return vctAdd(l, r);
    if (op === '-') return vctSub(l, r);
    if (op === '*') return vctCross(l, r);      // × is the cross product in VECTOR mode
  }
  if (isVct(l) && isMat(r)) {
    if (op === '*') {                            // vector × matrix, like a real Casio
      if (l.n !== r.rows) mathError();
      return Vct(r.cols, (function () {
        var out = [], c, k, s;
        for (c = 0; c < r.cols; c++) { s = C(0, 0); for (k = 0; k < r.rows; k++) s = cadd(s, cmul(l.data[k], r.data[k * r.cols + c])); out.push(s); }
        return out;
      })());
    }
  }
  mathError();
}
function matPower(m, z) {
  if (Math.abs(z.im) > 1e-12 || Math.abs(z.re - Math.round(z.re)) > 1e-12) mathError();
  var n = Math.round(z.re);
  if (n === 0) {
    var d = [], i;
    for (i = 0; i < m.rows * m.rows; i++) d.push(i % (m.rows + 1) === 0 ? C(1, 0) : C(0, 0));
    return Mat(m.rows, m.rows, d);
  }
  if (n < 0) m = matInv(m);
  var r = m, k;
  for (k = 1; k < Math.abs(n); k++) r = matMul(r, m);
  return r;
}
function postOp(op, x) {
  switch (op) {
    case '²': return sqr(x);
    case '³': return binOp('*', sqr(x), x);
    case '!': return factorialOf(x);
    case '⁻¹': return invert(x);
    case '%': return cscale(x, 0.01);
  }
  mathError();
}
function sqr(x) {
  if (isNum(x)) return cmul(x, x);
  if (isMat(x)) return matMul(x, x);
  if (isVct(x)) return vctDot(x, x);
  mathError();
}
function invert(x) {
  if (isNum(x)) return cdiv(C(1, 0), x);
  if (isMat(x)) return matInv(x);
  mathError();
}
function factorialOf(x) {
  if (!isNum(x) || Math.abs(x.im) > 1e-12) mathError();
  var n = x.re;
  if (n > 170) mathError();
  return factorial(n);
}

/* ---- the evaluator itself ------------------------------------------- */
function ev(node) {
  if (!node) syntaxError();
  switch (node.k) {
    case 'num':    return node.v;
    case 'var':    return cclone(state.vars[node.name] || C(0, 0));
    case 'const':  return node.name === 'π' ? C(Math.PI, 0) : C(Math.E, 0);
    case 'ans':    return state.hasAns ? cclone(state.ans) : C(0, 0);
    case 'preans': return state.preAns ? cclone(state.preAns) : C(0, 0);
    case 'i':      return C(0, 1);
    case 'mat':    return state.mats[node.name] ? matClone(state.mats[node.name]) : Mat(1, 1);
    case 'vct':    return state.vcts[node.name] ? vctClone(state.vcts[node.name]) : Vct(1);
    case 'neg': {
      var v = ev(node.x);
      if (isNum(v)) return cneg(v);
      if (isMat(v)) return matScale(v, C(-1, 0));
      if (isVct(v)) return vctScale(v, C(-1, 0));
      mathError();
    }
    case 'bin':    return binOp(node.op, ev(node.l), ev(node.r));
    case 'post':   return postOp(node.op, ev(node.x));
    case 'pct': {
      var base = ev(node.base), p = ev(node.x);
      if (!isNum(base) || !isNum(p)) mathError();
      var delta = cdiv(cmul(base, p), C(100, 0));
      return node.op === '+' ? cadd(base, delta) : csub(base, delta);
    }
    case 'fn': {
      var args = [];
      for (var i = 0; i < node.args.length; i++) args.push(ev(node.args[i]));
      return callFn(node.name, args);
    }
    case 'raw':    return callRaw(node.name, node.args);
    case 'unaryfn': {
      var x = ev(node.x);
      if (!isNum(x) || Math.abs(x.im) > 1e-12) mathError();
      return C(node.name === 'not' ? ~Math.trunc(x.re) : -Math.trunc(x.re), 0);
    }
  }
  syntaxError();
}

/* =========================================================================
   8. CALCULUS / SOLVER META FUNCTIONS
   These receive their arguments as RAW token slices so they can be
   re-evaluated thousands of times with a variable bound to new values.
   ========================================================================= */

/** Parse once, then evaluate with variable `name` temporarily set to `val`. */
function evalWithVar(toks, name, val) {
  var ast = parseTokens(toks);
  return evalAstWithVar(ast, name, val);
}
function evalAstWithVar(ast, name, val) {
  var old = state.vars[name];
  state.vars[name] = C(val, 0);
  try {
    var r = ev(ast);
    if (!isNum(r)) mathError();
    return r;
  } finally {
    state.vars[name] = old;
  }
}
/** The variable name inside a raw token slice (must be a single variable). */
function varNameOf(toks) {
  if (toks.length === 1 && toks[0].t === 'var') return toks[0].v;
  syntaxError();
}
function numArg(toks, dflt) {
  if (!toks || !toks.length) {
    if (dflt === undefined) syntaxError();
    return dflt;
  }
  var v = ev(parseTokens(toks));
  if (!isNum(v) || Math.abs(v.im) > 1e-9) mathError();
  return v.re;
}
/** Collect the variable names used by an expression (not Ans/constants). */
function varsUsed(toks) {
  var seen = {}, out = [];
  for (var i = 0; i < toks.length; i++) {
    var t = toks[i];
    if (t.t === 'var' && !seen[t.v]) { seen[t.v] = 1; out.push(t.v); }
  }
  return out;
}

function callRaw(name, argToks) {
  var exprT, varName, ast, a, b, i, v;

  if (name === 'sum' || name === 'prod') {
    if (argToks.length !== 4) syntaxError();
    exprT = argToks[0];
    varName = varNameOf(argToks[1]);
    a = Math.round(numArg(argToks[2]));
    b = Math.round(numArg(argToks[3]));
    if (b < a && name === 'sum') return C(0, 0);
    if (Math.abs(b - a) > 1000000) mathError();
    ast = parseTokens(exprT);
    var acc = (name === 'sum') ? C(0, 0) : C(1, 0);
    var step = (a <= b) ? 1 : -1;
    for (i = a; ; i += step) {
      v = evalAstWithVar(ast, varName, i);
      acc = (name === 'sum') ? cadd(acc, v) : cmul(acc, v);
      if (i === b) break;
    }
    return acc;
  }

  if (name === 'intg') {
    if (argToks.length < 2) syntaxError();
    exprT = argToks[0];
    varName = varNameOf(argToks[1]);
    a = numArg(argToks[2], 0);
    b = numArg(argToks[3], (state.vars[varName] ? state.vars[varName].re : 0));
    ast = parseTokens(exprT);
    return C(simpson(ast, varName, a, b), 0);
  }

  if (name === 'diff') {
    if (argToks.length < 2) syntaxError();
    exprT = argToks[0];
    varName = varNameOf(argToks[1]);
    var pt = numArg(argToks[2], (state.vars[varName] ? state.vars[varName].re : 0));
    ast = parseTokens(exprT);
    return C(derivative(ast, varName, pt), 0);
  }

  if (name === 'solve') {
    if (argToks.length < 2) syntaxError();
    exprT = argToks[0];
    varName = varNameOf(argToks[1]);
    var guess = numArg(argToks[2], (state.vars[varName] ? state.vars[varName].re : 0));
    ast = parseTokens(exprT);
    var root = newtonSolve(ast, varName, guess);
    return { kind: 'pair', labels: [varName, 'L−R'],
             values: [C(root, 0), C(evalAstWithVar(ast, varName, root).re, 0)] };
  }
  syntaxError();
}

/** Simpson's rule, refined until it settles (or 20000 slices). */
function simpson(ast, varName, a, b) {
  if (a === b) return 0;
  if (a > b) { var t = a; a = b; b = t; }
  function f(x) {
    var v = evalAstWithVar(ast, varName, x);
    if (!isFinite(v.re) || Math.abs(v.im) > 1e-9) mathError();
    return v.re;
  }
  var n = 100, prev = 0, val = 0, i;
  for (var pass = 0; pass < 8; pass++) {
    var h = (b - a) / n, s = f(a) + f(b);
    for (i = 1; i < n; i += 2) s += 4 * f(a + i * h);
    for (i = 2; i < n - 1; i += 2) s += 2 * f(a + i * h);
    val = s * h / 3;
    if (pass > 0 && Math.abs(val - prev) < 1e-10 * Math.max(1, Math.abs(val))) break;
    prev = val;
    n *= 2;
  }
  return val;
}
/** Central-difference derivative. */
function derivative(ast, varName, x) {
  function f(v) {
    var r = evalAstWithVar(ast, varName, v);
    if (!isFinite(r.re) || Math.abs(r.im) > 1e-9) mathError();
    return r.re;
  }
  var h = 1e-5 * Math.max(1, Math.abs(x));
  var d = (f(x + h) - f(x - h)) / (2 * h);
  if (!isFinite(d)) mathError();
  return d;
}
/** Newton's method (with a bisection fallback for stubborn functions). */
function newtonSolve(ast, varName, guess) {
  function f(v) {
    var r = evalAstWithVar(ast, varName, v);
    if (!isFinite(r.re) || Math.abs(r.im) > 1e-9) return NaN;
    return r.re;
  }
  var x = guess, i;
  for (i = 0; i < 300; i++) {
    var fx = f(x);
    if (!isFinite(fx)) break;
    if (Math.abs(fx) < 1e-13) return x;
    var h = 1e-7 * Math.max(1, Math.abs(x));
    var d = (f(x + h) - f(x - h)) / (2 * h);
    if (!isFinite(d) || Math.abs(d) < 1e-14) break;
    var nx = x - fx / d;
    if (!isFinite(nx)) break;
    if (Math.abs(nx - x) < 1e-13 * Math.max(1, Math.abs(nx))) return nx;
    x = nx;
  }
  // fallback: scan for a sign change and bisect
  var lo = -1e6, hi = 1e6, flo = f(lo), fhi = f(hi), steps = 200, k;
  var prevX = lo, prevF = flo;
  for (k = 0; k <= steps; k++) {
    var cx = lo + (hi - lo) * k / steps, cf = f(cx);
    if (isFinite(prevF) && isFinite(cf) && ((prevF < 0 && cf > 0) || (prevF > 0 && cf < 0))) {
      var A = prevX, B = cx;
      for (var j = 0; j < 200; j++) {
        var mid = (A + B) / 2, fm = f(mid);
        if (!isFinite(fm)) break;
        if ((f(A) < 0) === (fm < 0)) A = mid; else B = mid;
      }
      return (A + B) / 2;
    }
    prevX = cx; prevF = cf;
  }
  mathError();
}

/* =========================================================================
   BASE-N EVALUATOR (BigInt, 64-bit signed two's complement)
   ========================================================================= */
function evBase(node) {
  switch (node.k) {
    case 'num': return wrapSigned(bigFromText(node.raw.m, BASE_INFO[state.base].r));
    case 'bin': {
      var l = evBase(node.l), r = evBase(node.r);
      switch (node.op) {
        case '+': return wrapSigned(l + r);
        case '-': return wrapSigned(l - r);
        case '*': return wrapSigned(l * r);
        case '/': if (r === 0n) mathError(); return wrapSigned(l / r);
        case 'mod': if (r === 0n) mathError(); return wrapSigned(l % r);
        case 'and':  return wrapSigned(BigInt.asUintN(64, toUnsigned(l) & toUnsigned(r)));
        case 'or':   return wrapSigned(BigInt.asUintN(64, toUnsigned(l) | toUnsigned(r)));
        case 'xor':  return wrapSigned(BigInt.asUintN(64, toUnsigned(l) ^ toUnsigned(r)));
        case 'xnor': return wrapSigned(BigInt.asUintN(64, ~(toUnsigned(l) ^ toUnsigned(r))));
      }
      mathError();
    }
    case 'unaryfn': {
      var x = evBase(node.x);
      if (node.name === 'not') return wrapSigned(BigInt.asUintN(64, ~toUnsigned(x)));
      return wrapSigned(-x);
    }
    case 'neg': return wrapSigned(-evBase(node.x));
    case 'pct': mathError();
  }
  mathError();
}
function evaluateBaseTokens(toks) {
  var ast = parseTokens(toks);
  return evBase(ast);
}

/** Evaluate whatever is on the line, in the current mode. */
function evaluateCurrent() {
  if (!state.tokens.length) return null;
  if (state.mode === 'BASE-N') return evaluateBaseTokens(state.tokens);
  return ev(parseTokens(state.tokens));
}
/* =========================================================================
   9. LCD RENDERING
   ========================================================================= */

var IND_DEFS = [
  { id: 'S',    txt: 'S' },
  { id: 'A',    txt: 'A', cls: 'alp' },
  { sep: true },
  { id: 'M',    txt: 'M' },
  { id: 'STO',  txt: 'STO' },
  { id: 'Ans',  txt: 'Ans' },
  { sep: true },
  { id: 'D',    txt: 'D' },
  { id: 'R',    txt: 'R' },
  { id: 'G',    txt: 'G' },
  { sep: true },
  { id: 'Fix',  txt: 'Fix' },
  { id: 'Sci',  txt: 'Sci' },
  { id: 'Norm', txt: 'Norm' },
  { sep: true },
  { id: 'MODE', txt: 'COMP' }
];
var indEls = {};

function buildIndicators() {
  var row = $('indicators');
  row.innerHTML = '';
  IND_DEFS.forEach(function (d) {
    if (d.sep) { row.appendChild(el('span', 'sep')); return; }
    var s = el('span', 'ind' + (d.cls ? ' ' + d.cls : ''), d.txt);
    row.appendChild(s);
    indEls[d.id] = s;
  });
}
function renderIndicators() {
  function set(id, on) { if (indEls[id]) indEls[id].className = 'ind' + (on ? ' on' : '') + (id === 'A' ? ' alp' : ''); }
  set('S', state.shift);
  set('A', state.alpha);
  set('M', state.memUsed);
  set('STO', state.sto || state.rcl);
  set('Ans', state.hasAns);
  set('D', state.angle === 'DEG');
  set('R', state.angle === 'RAD');
  set('G', state.angle === 'GRAD');
  set('Fix', state.display === 'Fix');
  set('Sci', state.display === 'Sci');
  set('Norm', state.display === 'Norm');
  if (indEls.MODE) { indEls.MODE.textContent = state.mode; indEls.MODE.className = 'ind on'; }
}

/** Shrink a piece of text until it fits, like a real Casio does. */
function fitText(node, maxPx, minPx) {
  var parent = node.parentElement;
  var size = maxPx;
  node.style.fontSize = size + 'px';
  while (size > minPx && node.scrollWidth > parent.clientWidth - 1) {
    size -= 0.5;
    node.style.fontSize = size + 'px';
  }
}

function renderLines() {
  var linesEl = $('lines'), ed = $('editor');
  linesEl.style.visibility = 'visible';
  ed.classList.remove('active');

  $('exprText').textContent = exprText(state.tokens);

  // keep the blinking cursor visible by scrolling the top line
  var wrap = $('exprWrap');
  wrap.scrollLeft = wrap.scrollWidth;

  var res = $('resText'), txt;
  if (state.error) {
    txt = state.errorText || 'Syntax ERROR';
    res.className = 'res-text err';
  } else if (state.result === null) {
    txt = '';
    res.className = 'res-text';
  } else {
    txt = state.resultForms.length
      ? state.resultForms[state.resultForm]
      : valueToString(state.result);
    res.className = 'res-text';
  }
  res.textContent = txt;
  fitText(res, 27, 11);
  $('cursor').classList.toggle('hidden', state.error);
}

function renderBaseBar() {
  var bar = $('baseBar');
  function hide() { bar.classList.remove('active'); $('lines').classList.remove('with-base'); }
  if (state.mode !== 'BASE-N' || state.result === null) { hide(); return; }
  var v = state.result;
  if (typeof v !== 'bigint') { hide(); return; }
  $('lines').classList.add('with-base');
  bar.innerHTML = '';
  [['DEC', 10], ['HEX', 16], ['BIN', 2], ['OCT', 8]].forEach(function (p) {
    var s = el('span');
    s.innerHTML = '<b>' + p[0] + '</b> ' + bigToText(v, p[1]);
    bar.appendChild(s);
  });
  bar.classList.add('active');
}

/** The one function that redraws everything. */
function render() {
  renderIndicators();
  if (state.prompt) return renderPrompt();
  if (state.menu) return renderMenu();
  if (state.editor) return;                    // the mode panel owns the screen
  if (state.result && (isMat(state.result) || isVct(state.result))) return renderMatrixResult();
  renderLines();
  renderBaseBar();
}

/* ---- errors --------------------------------------------------------- */
function showError(e) {
  state.error = true;
  state.errorText = (e && e.message === 'Math ERROR') ? 'Math ERROR' :
                    (e && e.message === 'Syntax ERROR') ? 'Syntax ERROR' :
                    (e && e.message) ? e.message : 'Syntax ERROR';
  state.result = null;
  state.resultForms = [];
  state.prompt = null;
  render();
}
function clearError() { state.error = false; state.errorText = ''; }

/* ---- showing a result ------------------------------------------------ */
function setResult(v) {
  state.error = false;
  state.result = v;
  state.resultForms = [];
  state.resultForm = 0;
  state.eng = false;
  state.resultIsDMS = false;
  if (isNum(v)) {
    var base = valueToString(v);
    var forms = [base];
    if (state.mathIO && Math.abs(v.im) < 1e-11) {
      exactForms(v).forEach(function (f) { if (forms.indexOf(f) < 0) forms.push(f); });
    }
    state.resultForms = forms;
  }
  render();
}
function pushHistory(e, r) {
  state.history.unshift({ e: e, r: r, mode: state.mode });
  if (state.history.length > 300) state.history.pop();
  renderHistory();
}

/* =========================================================================
   10. ON-SCREEN MENUS, PROMPTS AND EDITORS
   ========================================================================= */

var PER_PAGE = 9;

function showMenu(title, items, opts) {
  state.menu = { title: title, items: items, page: 0, sel: 0, opts: opts || {} };
  render();
}
function closeMenu() {
  state.menu = null;
  $('editor').classList.remove('active');
  render();
}
function menuPageItems(m) {
  var start = m.page * PER_PAGE;
  return m.items.slice(start, start + PER_PAGE);
}
function menuRun(m, idx) {
  var start = m.page * PER_PAGE;
  var item = m.items[start + idx];
  if (!item) return;
  var act = (typeof item === 'string') ? null : item.act;
  closeMenu();
  if (act) act();
  else render();
}
function renderMenu() {
  var m = state.menu;
  if (!m) return;
  var linesEl = $('lines'), ed = $('editor');
  linesEl.style.visibility = 'hidden';
  ed.innerHTML = '';
  ed.classList.add('active');

  var pages = Math.ceil(m.items.length / PER_PAGE);
  var t = el('div', 'ed-title');
  t.appendChild(el('span', null, m.title));
  t.appendChild(el('span', 'hint', pages > 1 ? ('page ' + (m.page + 1) + '/' + pages) : 'EXIT=AC'));
  ed.appendChild(t);

  var body = el('div', 'ed-body');
  var ul = el('ul', 'menu-list');
  var items = menuPageItems(m);
  items.forEach(function (it, i) {
    var li = el('li', i === m.sel ? 'sel' : '');
    li.appendChild(el('span', 'num', String(i + 1)));
    li.appendChild(el('span', null, typeof it === 'string' ? it : it.label));
    li.addEventListener('click', function () { menuRun(m, i); });
    ul.appendChild(li);
  });
  // key "0" always moves to the next page when the list is longer than one page
  if (pages > 1) {
    var li = el('li', '');
    li.appendChild(el('span', 'num', '0'));
    li.appendChild(el('span', null, '▸ next page'));
    li.addEventListener('click', function () {
      m.page = (m.page + 1) % pages; m.sel = 0; render();
    });
    ul.appendChild(li);
  }
  body.appendChild(ul);
  ed.appendChild(body);

  var foot = el('div', 'ed-foot');
  var b = el('button', 'ed-btn', 'EXIT');
  b.addEventListener('click', closeMenu);
  foot.appendChild(b);
  ed.appendChild(foot);
  renderIndicators();
}

/* ---- prompts (the "X?" style input used by CALC, MATRIX, STAT, ...) --- */
function startPrompt(label, initial, onDone) {
  state.prompt = { label: label, value: (initial === undefined || initial === null) ? '' : String(initial), onDone: onDone };
  render();
}
function renderPrompt() {
  var p = state.prompt;
  var linesEl = $('lines'), ed = $('editor');
  linesEl.style.visibility = 'hidden';
  ed.innerHTML = '';
  ed.classList.add('active');
  var body = el('div', 'ed-body');
  var row = el('div', 'prompt-line');
  row.appendChild(el('span', 'lab', p.label));
  var val = el('span', 'prompt-val', p.value);
  var cur = el('span', 'cur', '|');
  row.appendChild(val); row.appendChild(cur);
  body.appendChild(row);
  ed.appendChild(body);
  var foot = el('div', 'ed-foot');
  var b1 = el('button', 'ed-btn primary', '= OK');
  b1.addEventListener('click', finishPrompt);
  var b2 = el('button', 'ed-btn', 'AC cancel');
  b2.addEventListener('click', function () { state.prompt = null; render(); });
  foot.appendChild(b1); foot.appendChild(b2);
  ed.appendChild(foot);
  renderIndicators();
}
function finishPrompt() {
  var p = state.prompt;
  if (!p) return;
  var raw = p.value;
  state.prompt = null;
  var v;
  try { v = parseInputNumber(raw); }
  catch (e) { showError(e); return; }
  p.onDone(v);
}

/** Turn a typed string into a number (accepts plain numbers and expressions). */
function parseInputNumber(s) {
  s = (s || '').trim();
  if (s === '' || s === '-' || s === '.') return 0;
  if (/^[+-]?(\d+\.?\d*|\.\d+)([eE][+-]?\d+)?$/.test(s)) return parseFloat(s);
  try {
    var v = ev(parseTokens(tokenizeString(s)));
    if (isNum(v) && Math.abs(v.im) < 1e-9) return v.re;
  } catch (e) { /* fall through and try a plain parse */ }
  var n = parseFloat(String(s).replace(/,/g, ''));
  if (isNaN(n)) syntaxError();
  return n;
}

/** Run a chain of prompts, then call done(valuesObject). */
function promptChain(list, done) {
  var values = {};
  function step(i) {
    if (i >= list.length) { done(values); return; }
    var it = list[i];
    startPrompt(it.label, it.value, function (v) {
      values[it.key] = v;
      step(i + 1);
    });
  }
  step(0);
}

/* ---- generic editor panel ------------------------------------------- */
function openEditor(title, hint) {
  var ed = $('editor');
  $('lines').style.visibility = 'hidden';
  ed.innerHTML = '';
  ed.classList.add('active');
  var t = el('div', 'ed-title');
  t.appendChild(el('span', null, title));
  if (hint) t.appendChild(el('span', 'hint', hint));
  ed.appendChild(t);
  var body = el('div', 'ed-body');
  ed.appendChild(body);
  var foot = el('div', 'ed-foot');
  ed.appendChild(foot);
  ed.appendChild(el('div', 'ed-res'));
  return { root: ed, body: body, foot: foot, res: ed.lastChild };
}
function edButton(parent, label, fn, primary) {
  var b = el('button', 'ed-btn' + (primary ? ' primary' : ''), label);
  b.addEventListener('click', fn);
  parent.appendChild(b);
  return b;
}
function edInput(parent, value, wide) {
  var i = el('input', 'cell' + (wide ? ' wide' : ''));
  i.type = 'text';
  i.inputMode = 'decimal';
  i.value = value === undefined ? '' : value;
  parent.appendChild(i);
  return i;
}
function closeEditor() {
  state.editor = null;
  $('editor').classList.remove('active');
  $('editor').innerHTML = '';
  $('lines').style.visibility = 'visible';
  render();
}

/* ---- matrix / vector result display --------------------------------- */
function renderMatrixResult() {
  var v = state.result;
  var p = openEditor((isMat(v) ? 'MatAns' : 'VctAns'), 'AC / EXIT');
  var rows = isMat(v) ? v.rows : 1;
  var cols = isMat(v) ? v.cols : v.n;
  var grid = el('div', 'matgrid');
  grid.style.gridTemplateColumns = 'repeat(' + cols + ', auto)';
  for (var r = 0; r < rows; r++) {
    for (var c = 0; c < cols; c++) {
      var idx = isMat(v) ? r * cols + c : c;
      grid.appendChild(el('div', 'mv', fmtComplex(v.data[idx])));
    }
  }
  var wrap = el('div', 'matwrap');
  wrap.appendChild(el('span', 'matbracket'));
  wrap.appendChild(grid);
  wrap.appendChild(el('span', 'matbracket'));
  p.body.appendChild(wrap);
  state.editor = { kind: 'matresult' };
}

/* =========================================================================
   MINI TOKENIZER — turns a typed string (from an input box) into tokens.
   Used by TABLE / VERIF / INEQ / prompts so users can type formulas.
   ========================================================================= */
var FN_WORDS = {
  'sin': 'sin(', 'cos': 'cos(', 'tan': 'tan(', 'asin': 'sin⁻¹(', 'acos': 'cos⁻¹(', 'atan': 'tan⁻¹(',
  'sinh': 'sinh(', 'cosh': 'cosh(', 'tanh': 'tanh(', 'asinh': 'sinh⁻¹(', 'acosh': 'cosh⁻¹(', 'atanh': 'tanh⁻¹(',
  'ln': 'ln(', 'log': 'log(', 'exp': 'e^(', 'abs': 'Abs(', 'Abs': 'Abs(', 'sqrt': '√(',
  'sum': 'Σ(', 'prod': 'Π(', 'pol': 'Pol(', 'rec': 'Rec(', 'rnd': 'Rnd(',
  'cbrt': '³√(', 'nroot': 'ʸ√(', 'solve': 'SOLVE(', 'arg': 'arg(',
  'conjg': 'Conjg(', 'Conjg': 'Conjg(', 'Re': 'Re(', 're': 'Re(', 'Im': 'Im(', 'im': 'Im(',
  'det': 'det(', 'trn': 'Trn(', 'dot': 'Dot(', 'cross': 'Cross(', 'ident': 'Identity(',
  'not': null, 'and': null, 'or': null, 'xor': null, 'mod': null
};
var FN_CODES = {
  'sin⁻¹(': 'asin', 'cos⁻¹(': 'acos', 'tan⁻¹(': 'atan', 'sinh⁻¹(': 'asinh',
  'cosh⁻¹(': 'acosh', 'tanh⁻¹(': 'atanh', 'e^(': 'exp', 'Abs(': 'abs', '√(': 'sqrt',
  'Σ(': 'sum', 'Π(': 'prod', 'Pol(': 'pol', 'Rec(': 'rec', 'Rnd(': 'rnd'
};

function tokenizeString(s) {
  s = String(s || '').trim();
  s = s.replace(/×/g, '*').replace(/÷/g, '/').replace(/−/g, '-').replace(/–/g, '-');
  var out = [], i = 0;
  function pushNum(m, e) { out.push(numTok(m, e)); }
  while (i < s.length) {
    var c = s[i];
    if (c === ' ' || c === '\t') { i++; continue; }
    if (/[0-9.]/.test(c)) {
      var m = '';
      while (i < s.length && /[0-9.]/.test(s[i])) { m += s[i]; i++; }
      var e = null;
      if ((s[i] === 'e' || s[i] === 'E') && /[0-9+\-]/.test(s[i + 1] || '')) {
        i++;
        e = '';
        if (s[i] === '+' || s[i] === '-') { e += s[i]; i++; }
        while (i < s.length && /[0-9]/.test(s[i])) { e += s[i]; i++; }
      }
      pushNum(m, e);
      continue;
    }
    if (c === 'π') { out.push(tok('const', 'π')); i++; continue; }
    if (c === '∫') { out.push(fnTok('intg', '∫(')); i++; continue; }
    if (s.substr(i, 5) === 'd/dx(') { out.push(fnTok('diff', 'd/dx(')); i += 4; continue; }
    if (s.substr(i, 3) === 'r∠θ') { out.push(fnTok('rangle', 'r∠θ(')); i += 3; continue; }
    if (c === '³' && s[i + 1] === '√') { out.push(fnTok('cbrt', '³√(')); i += 2; continue; }
    if (s.substr(i, 2) === 'ʸ√') { out.push(fnTok('nroot', 'ʸ√(')); i += 2; continue; }
    if (c === '√') { out.push(fnTok('sqrt', '√(')); i++; continue; }
    if (c === 'Σ') { out.push(fnTok('sum', 'Σ(')); i++; continue; }
    if (c === 'Π') { out.push(fnTok('prod', 'Π(')); i++; continue; }
    if (/[a-zA-Z]/.test(c)) {
      var w = '';
      while (i < s.length && /[a-zA-Z0-9⁻¹]/.test(s[i])) { w += s[i]; i++; }
      // in BASE-N mode A-F are simply digits
      if (state.mode === 'BASE-N' && /^[0-9A-Fa-f]+$/.test(w)) { out.push(numTok(w.toUpperCase())); continue; }
      // a trailing ⁻¹ means "inverse":  MatA⁻¹ , sin⁻¹( ... )
      var invSuffix = false;
      if (w.slice(-2) === '⁻¹') {
        var invMap = { sin: 'asin', cos: 'acos', tan: 'atan', sinh: 'asinh', cosh: 'acosh', tanh: 'atanh' };
        if (invMap[w.slice(0, -2)]) { out.push(fnTok(invMap[w.slice(0, -2)], w + '(')); continue; }
        invSuffix = true; w = w.slice(0, -2);
      }
      // inverse trig typed as asin(...)
      if (w === 'asin') { out.push(fnTok('asin', 'sin⁻¹(')); continue; }
      if (w === 'acos') { out.push(fnTok('acos', 'cos⁻¹(')); continue; }
      if (w === 'atan') { out.push(fnTok('atan', 'tan⁻¹(')); continue; }
      if (w === 'asinh') { out.push(fnTok('asinh', 'sinh⁻¹(')); continue; }
      if (w === 'acosh') { out.push(fnTok('acosh', 'cosh⁻¹(')); continue; }
      if (w === 'atanh') { out.push(fnTok('atanh', 'tanh⁻¹(')); continue; }
      if (w.toUpperCase() === 'SOLVE') { out.push(fnTok('solve', 'SOLVE(')); continue; }
      if (w === 'Ans') { out.push(tok('ans')); continue; }
      if (w === 'mod') { out.push(opTok('mod')); continue; }
      if (w === 'and' || w === 'or' || w === 'xor' || w === 'xnor') { out.push(opTok(w)); continue; }
      if (w === 'not') { out.push(opTok('not')); continue; }
      if (w === 'e') { out.push(tok('const', 'e')); continue; }
      if (w === 'i') { out.push(tok('i')); continue; }
      if (w === 'MatA' || w === 'MatB' || w === 'MatC') {
        out.push(tok('mat', w)); if (invSuffix) out.push(postTok('⁻¹')); continue;
      }
      if (w === 'VctA' || w === 'VctB' || w === 'VctC') {
        out.push(tok('vct', w)); if (invSuffix) out.push(postTok('⁻¹')); continue;
      }
      if (w.length === 1 && 'ABCDEFXYM'.indexOf(w) >= 0) {
        out.push(tok('var', w)); if (invSuffix) out.push(postTok('⁻¹')); continue;
      }
      var wk = (FN_WORDS[w] !== undefined) ? w
             : (FN_WORDS[w.toLowerCase()] !== undefined) ? w.toLowerCase() : null;
      if (wk !== null) { out.push(fnTok(wk, FN_WORDS[wk])); if (invSuffix) out.push(postTok('⁻¹')); continue; }
      syntaxError();
    }
    if (c === '+' || c === '*' || c === '/') { out.push(opTok(c)); i++; continue; }
    if (c === '-') { out.push(opTok('-')); i++; continue; }
    if (c === '^') { out.push(opTok('^')); i++; continue; }
    if (c === '(') { out.push(lpTok()); i++; continue; }
    if (c === ')') { out.push(rpTok()); i++; continue; }
    if (c === ',') { out.push(tok('comma')); i++; continue; }
    if (c === '!') { out.push(postTok('!')); i++; continue; }
    if (c === '%') { out.push(postTok('%')); i++; continue; }
    if (c === '²') { out.push(postTok('²')); i++; continue; }
    if (c === '³') { out.push(postTok('³')); i++; continue; }
    if (c === '°') { out.push(tok('dms')); i++; continue; }
    syntaxError();
  }
  return out;
}

/** Evaluate a formula string with optional variable bindings. */
function evalString(str, vars) {
  var toks = tokenizeString(str);
  var saved = {};
  if (vars) { for (var k in vars) { saved[k] = state.vars[k]; state.vars[k] = C(vars[k], 0); } }
  try { return ev(parseTokens(toks)); }
  finally { if (vars) { for (var k2 in saved) state.vars[k2] = saved[k2]; } }
}
/* =========================================================================
   11. EXPRESSION ENTRY  (what the keys actually insert)
   ========================================================================= */

function lastTok() { return state.tokens[state.tokens.length - 1]; }

/** Get the line ready for new input (after "=" or after an error). */
function ensureEditable() {
  if (state.error) { state.error = false; state.errorText = ''; state.tokens = []; state.result = null; state.resultForms = []; }
  if (state.justEquals) { state.tokens = []; state.justEquals = false; }
}
function numTokFromNumber(x) {
  var s = String(x);
  if (s.indexOf('e') >= 0) { var p = s.split('e'); return numTok(p[0], String(parseInt(p[1], 10))); }
  return numTok(s);
}

function insertDigit(d) {
  ensureEditable();
  if (state.mode === 'BASE-N') {
    var rad = BASE_INFO[state.base].r;
    if (parseInt(d, 16) >= rad) return;               // digit not valid in this base
  }
  var last = lastTok();
  if (last && last.t === 'num') {
    if (last.e !== null && last.e !== undefined) {
      if (last.e.length < 3) last.e += d;
    } else if (last.m === '0') {
      last.m = d;
    } else if (last.m.replace(/[^0-9]/g, '').length < 15) {
      last.m += d;
    }
  } else {
    state.tokens.push(numTok(d));
  }
  render();
}
function insertDot() {
  ensureEditable();
  var last = lastTok();
  if (last && last.t === 'num') {
    if (last.e !== null && last.e !== undefined) { if (last.e.indexOf('.') < 0) last.e += '.'; }
    else if (last.m.indexOf('.') < 0) last.m += '.';
  } else {
    state.tokens.push(numTok('0.'));
  }
  render();
}
/** ×10^x  (the EXP key) */
function insertExp() {
  ensureEditable();
  var last = lastTok();
  if (last && last.t === 'num' && (last.e === null || last.e === undefined)) last.e = '';
  else state.tokens.push(numTok('1', ''));
  render();
}
function insertOp(op) {
  if (state.error) { ensureEditable(); }
  if (state.justEquals && state.tokens.length) {         // continue from Ans
    state.tokens = [tok('ans')];
    state.justEquals = false;
  }
  var last = lastTok();
  if (!last) state.tokens.push(tok('ans'));
  else if (last.t === 'op') { state.tokens[state.tokens.length - 1] = opTok(op); render(); return; }
  else if ((last.t === 'lp' || last.t === 'comma') && op !== '-') { render(); return; }
  state.tokens.push(opTok(op));
  render();
}
function insertLP() { ensureEditable(); state.tokens.push(lpTok()); render(); }
function insertRP() {
  ensureEditable();
  var last = lastTok();
  if (last && (last.t === 'lp' || last.t === 'op' || last.t === 'comma')) { render(); return; }
  state.tokens.push(rpTok()); render();
}
function insertFn(name, disp, noargs) {
  ensureEditable();
  state.tokens.push(fnTok(name, disp, noargs));
  if (!noargs) state.tokens.push(lpTok());
  render();
}
function insertPost(v) { ensureEditable(); state.tokens.push(postTok(v)); render(); }
function insertConst(c) { ensureEditable(); state.tokens.push(tok('const', c)); render(); }
function insertAns() { ensureEditable(); state.tokens.push(tok('ans')); render(); }
function insertPreAns() { ensureEditable(); state.tokens.push(tok('preans')); render(); }
function insertI() { ensureEditable(); state.tokens.push(tok('i')); render(); }
function insertDms() { ensureEditable(); state.tokens.push(tok('dms')); render(); }

/** Variables A B C D E F X Y M — also serve STO / RCL. */
function insertVar(name) {
  if (state.sto) {                                   // STO was pending: store now
    var v = state.result !== null ? state.result : (state.hasAns ? state.ans : C(0, 0));
    if (isNum(v)) { state.vars[name] = cclone(v); }
    state.sto = false;
    state.tokens = []; state.justEquals = false;
    render();
    return;
  }
  if (state.rcl) {                                   // RCL was pending: recall the value
    var m = state.vars[name] || C(0, 0);
    ensureEditable();
    state.tokens.push(numTokFromNumber(clean(m.re)));
    state.rcl = false;
    render();
    return;
  }
  ensureEditable();
  state.tokens.push(tok('var', name));
  render();
}

/* ---- memory --------------------------------------------------------- */
function currentValueForMemory() {
  if (state.result !== null && isNum(state.result)) return cclone(state.result);
  if (state.tokens.length) {
    try { var v = evaluateCurrent(); if (isNum(v)) return cclone(v); } catch (e) { /* ignore */ }
  }
  return state.hasAns ? cclone(state.ans) : C(0, 0);
}
function pressMPlus(sign) {
  var v = currentValueForMemory();
  state.memory = sign > 0 ? cadd(state.memory, v) : csub(state.memory, v);
  state.memUsed = true;
  state.justEquals = false;
  render();
}
function pressMR() {
  ensureEditable();
  state.tokens.push(numTokFromNumber(clean(state.memory.re)));
  render();
}
function pressMC() { state.memory = C(0, 0); state.memUsed = false; render(); }

/* ---- DEL / AC / ON -------------------------------------------------- */
function pressDel() {
  if (state.error) { clearEntry(); return; }
  if (!state.tokens.length) return;
  var last = state.tokens.pop();
  if (last.t === 'num') {
    // delete a single character, not the whole number
    if (last.e !== null && last.e !== undefined) {
      if (last.e.length > 1) { state.tokens.push(numTok(last.m, last.e.slice(0, -1))); }
      else if (last.e.length === 1) { state.tokens.push(numTok(last.m, null)); }
    } else if (last.m.length > 1) {
      state.tokens.push(numTok(last.m.slice(0, -1)));
    }
  } else if (last.t === 'lp') {
    var prev = lastTok();
    if (prev && prev.t === 'fn' && !prev.noargs) state.tokens.pop();      // remove "sin(" as one unit
  }
  state.justEquals = false;
  render();
}
function clearEntry() {
  state.tokens = [];
  state.error = false; state.errorText = '';
  state.result = null; state.resultForms = []; state.resultForm = 0;
  state.justEquals = false;
  state.sto = false; state.rcl = false; state.hyp = false;
  state.shift = false; state.alpha = false;
  render();
}
function pressAC() {
  if (state.menu) { closeMenu(); return; }
  if (state.prompt) { state.prompt = null; render(); return; }
  if (state.editor) { closeEditor(); return; }
  clearEntry();
  reopenModeMenu();
}
/** After AC in one of the panel modes, show that mode's menu again. */
function reopenModeMenu() {
  switch (state.mode) {
    case 'MATRIX': openMatrixMode(); break;
    case 'VECTOR': openVectorMode(); break;
    case 'EQN':    openEqnMode(); break;
    case 'STAT':   openStatMode(); break;
    case 'TABLE':  openTableMode(); break;
    case 'RATIO':  openRatioMode(); break;
    case 'DIST':   openDistMenu(); break;
    case 'INEQ':   openIneqMode(); break;
    case 'VERIF':  openVerifMode(); break;
  }
}
function pressON() {
  clearEntry();
  state.menu = null; state.prompt = null;
  closeEditor();
  render();
}

/* ---- = (and the SOLVE / CALC functions on it) ------------------------ */
function pressEquals() {
  if (state.menu) { menuKey('eq'); return; }
  if (state.prompt) { finishPrompt(); return; }
  if (!state.tokens.length) return;
  var text = exprText(state.tokens);
  try {
    var v = evaluateCurrent();
    if (isNum(v)) { state.preAns = state.ans; state.ans = cclone(v); state.hasAns = true; }
    setResult(v);
    state.justEquals = true;
    if (!(isMat(v) || isVct(v))) pushHistory(text, valueToString(v));
  } catch (e) {
    showError(e);
  }
}

/** CALC (ALPHA + =) : ask for a value for every variable, then evaluate. */
function runCalc() {
  if (!state.tokens.length) return;
  var used = varsUsed(state.tokens);
  if (!used.length) { pressEquals(); return; }
  var text = exprText(state.tokens);
  promptChain(used.map(function (n) {
    return { key: n, label: n + '?', value: clean(state.vars[n].re) };
  }), function (vals) {
    var saved = {};
    for (var k in vals) { saved[k] = state.vars[k]; state.vars[k] = C(vals[k], 0); }
    try {
      var v = evaluateCurrent();
      if (isNum(v)) { state.preAns = state.ans; state.ans = cclone(v); state.hasAns = true; }
      setResult(v);
      state.justEquals = true;
      pushHistory(text + '  (' + used.map(function (n) { return n + '=' + vals[n]; }).join(', ') + ')', valueToString(v));
    } catch (e) { showError(e); }
    finally { for (var k2 in saved) state.vars[k2] = saved[k2]; }
  });
}

/** SOLVE (SHIFT + =) : Newton's method on the expression currently typed. */
function runSolve() {
  if (!state.tokens.length) return;
  var used = varsUsed(state.tokens);
  if (!used.length) { showError(new CalcError('Syntax ERROR')); return; }
  var name = used[0];
  startPrompt('Solve for ' + name + ' — ' + name + '?', clean(state.vars[name].re), function (guess) {
    try {
      var ast = parseTokens(state.tokens);
      var root = newtonSolve(ast, name, guess);
      state.vars[name] = C(root, 0);
      var lr = evalAstWithVar(ast, name, root).re;
      var res = { kind: 'pair', labels: [name, 'L−R'], values: [C(root, 0), C(lr, 0)] };
      setResult(res);
      state.justEquals = true;
      pushHistory('SOLVE ' + exprText(state.tokens), valueToString(res));
    } catch (e) { showError(e); }
  });
}

/* ---- S<->D, ENG, DMS ------------------------------------------------- */
function pressSD() {
  if (state.result === null) return;
  if (!isNum(state.result)) return;
  var forms = state.resultForms.slice();
  if (!forms.length) return;
  state.resultForm = (state.resultForm + 1) % forms.length;
  render();
}
function pressEng() {
  if (state.result === null) return;
  if (isNum(state.result)) {
    state.eng = !state.eng;
    state.resultForms = [state.eng ? fmtEng(clean(state.result.re)) : fmtComplex(state.result)];
    state.resultForm = 0;
    render();
  }
}
function convertToDMS() {
  if (state.result === null || !isNum(state.result)) return;
  if (state.resultForms.length && state.resultForms[state.resultForm] === state.resultForms[0]) {
    state.resultForms = [fmtComplex(state.result), fmtDMS(state.result.re)];
    state.resultForm = 1;
  } else {
    state.resultForm = state.resultForm === 0 ? (state.resultForms.length > 1 ? 1 : 0) : 0;
    if (!state.resultForms.some(function (f) { return f.indexOf('°') >= 0; })) {
      state.resultForms[1] = fmtDMS(state.result.re);
      state.resultForm = 1;
    }
  }
  render();
}
function toggleHyp() { state.hyp = !state.hyp; render(); }
function insTrig(base) {
  if (state.hyp) { insertFn(base + 'h', base + 'h('); state.hyp = false; return; }
  insertFn(base, base + '(');
}

/* =========================================================================
   MODE / SETUP / OPTION MENUS
   ========================================================================= */

function setMode(m) {
  state.mode = m;
  state.tokens = [];
  state.result = null; state.resultForms = []; state.resultForm = 0;
  state.error = false;
  state.shift = false; state.alpha = false; state.sto = false; state.rcl = false; state.hyp = false;
  state.menu = null;
  closeEditor();
  if (m === 'BASE-N') openBaseMenu();
  else if (m === 'STAT') openStatMode();
  else if (m === 'MATRIX') openMatrixMode();
  else if (m === 'VECTOR') openVectorMode();
  else if (m === 'EQN') openEqnMode();
  else if (m === 'TABLE') openTableMode();
  else if (m === 'RATIO') openRatioMode();
  else if (m === 'DIST') openDistMenu();
  else if (m === 'INEQ') openIneqMode();
  else if (m === 'VERIF') openVerifMode();
  render();
}

function openModeMenu() {
  showMenu('MODE', [
    { label: 'Calculate      COMP', act: function () { setMode('COMP'); } },
    { label: 'Complex        CMPLX', act: function () { setMode('CMPLX'); } },
    { label: 'Statistics     STAT', act: function () { setMode('STAT'); } },
    { label: 'Base-N         BASE', act: function () { setMode('BASE-N'); } },
    { label: 'Equation       EQN', act: function () { setMode('EQN'); } },
    { label: 'Matrix         MATRIX', act: function () { setMode('MATRIX'); } },
    { label: 'Vector         VECTOR', act: function () { setMode('VECTOR'); } },
    { label: 'Table          TABLE', act: function () { setMode('TABLE'); } },
    { label: 'Ratio          RATIO', act: function () { setMode('RATIO'); } },
    { label: 'Distribution   DIST', act: function () { setMode('DIST'); } },
    { label: 'Inequality     INEQ', act: function () { setMode('INEQ'); } },
    { label: 'Verify         VERIF', act: function () { setMode('VERIF'); } }
  ]);
}

function openSetupMenu() {
  showMenu('SETUP', [
    { label: 'Angle unit: ' + state.angle, act: function () {
        showMenu('ANGLE UNIT', [
          { label: 'Degrees  (DEG)', act: function () { state.angle = 'DEG'; render(); } },
          { label: 'Radians  (RAD)', act: function () { state.angle = 'RAD'; render(); } },
          { label: 'Grads    (GRAD)', act: function () { state.angle = 'GRAD'; render(); } }
        ]);
      } },
    { label: 'Display: ' + state.display + (state.display === 'Norm' ? '' : ' ' + state.dispDigits), act: function () {
        showMenu('DISPLAY', [
          { label: 'Fix (decimal places)', act: function () {
              startPrompt('Fix  0-9 ?', state.dispDigits, function (v) {
                state.display = 'Fix'; state.dispDigits = clamp(Math.round(v), 0, 9); render();
              });
            } },
          { label: 'Sci (significant digits)', act: function () {
              startPrompt('Sci  0-9 ?', state.dispDigits, function (v) {
                state.display = 'Sci'; state.dispDigits = clamp(Math.round(v), 0, 9); render();
              });
            } },
          { label: 'Norm 1 (10 digits)', act: function () { state.display = 'Norm'; state.dispDigits = 10; render(); } },
          { label: 'Norm 2 (4 digits)', act: function () { state.display = 'Norm'; state.dispDigits = 4; render(); } }
        ]);
      } },
    { label: 'Input/Output: ' + (state.mathIO ? 'Math' : 'Line'), act: function () {
        showMenu('INPUT / OUTPUT', [
          { label: 'Math  (fractions, π, √ forms)', act: function () { state.mathIO = true; render(); } },
          { label: 'Line  (decimals, E notation)', act: function () { state.mathIO = false; render(); } }
        ]);
      } },
    { label: 'Clear all memory & variables', act: function () {
        resetMemory(); render();
      } }
  ]);
}
function resetMemory() {
  for (var k in state.vars) state.vars[k] = C(0, 0);
  state.memory = C(0, 0); state.memUsed = false;
  state.ans = C(0, 0); state.preAns = C(0, 0); state.hasAns = false;
  state.mats = { MatA: null, MatB: null, MatC: null };
  state.vcts = { VctA: null, VctB: null, VctC: null };
}

var CONSTANTS = [
  { label: 'π  (pi)', val: 'π' },
  { label: 'e  (Euler)', val: 'e' },
  { label: 'c   speed of light (m/s)', v: 299792458 },
  { label: 'g   gravity (m/s²)', v: 9.80665 },
  { label: 'G   gravitational const', v: 6.6743e-11 },
  { label: 'h   Planck const (J·s)', v: 6.62607015e-34 },
  { label: 'ħ   reduced Planck', v: 1.054571817e-34 },
  { label: 'k   Boltzmann (J/K)', v: 1.380649e-23 },
  { label: 'NA  Avogadro (1/mol)', v: 6.02214076e23 },
  { label: 'R   gas const (J/mol·K)', v: 8.314462618 },
  { label: 'e   elementary charge (C)', v: 1.602176634e-19 },
  { label: 'me  electron mass (kg)', v: 9.1093837015e-31 },
  { label: 'mp  proton mass (kg)', v: 1.67262192369e-27 },
  { label: 'mn  neutron mass (kg)', v: 1.67492749804e-27 },
  { label: 'ε0  vacuum permittivity', v: 8.8541878128e-12 },
  { label: 'μ0  vacuum permeability', v: 1.25663706212e-6 },
  { label: 'F   Faraday (C/mol)', v: 96485.33212 },
  { label: 'σ   Stefan-Boltzmann', v: 5.670374419e-8 },
  { label: 'atm standard atmosphere', v: 101325 },
  { label: 'ly  light year (km)', v: 9.4607304725808e12 }
];
var CONVERSIONS = [
  { label: 'in → cm', f: 2.54 }, { label: 'cm → in', f: 1 / 2.54 },
  { label: 'ft → m', f: 0.3048 }, { label: 'm → ft', f: 1 / 0.3048 },
  { label: 'yd → m', f: 0.9144 }, { label: 'm → yd', f: 1 / 0.9144 },
  { label: 'mile → km', f: 1.609344 }, { label: 'km → mile', f: 1 / 1.609344 },
  { label: 'nmi → m', f: 1852 }, { label: 'm → nmi', f: 1 / 1852 },
  { label: 'acre → m²', f: 4046.8564224 }, { label: 'm² → acre', f: 1 / 4046.8564224 },
  { label: 'gal(US) → L', f: 3.785411784 }, { label: 'L → gal(US)', f: 1 / 3.785411784 },
  { label: 'lb → kg', f: 0.45359237 }, { label: 'kg → lb', f: 1 / 0.45359237 },
  { label: 'oz → g', f: 28.349523125 }, { label: 'g → oz', f: 1 / 28.349523125 },
  { label: 'hp → kW', f: 0.745699872 }, { label: 'kW → hp', f: 1 / 0.745699872 },
  { label: '°F → °C', f: null, t: true }, { label: '°C → °F', f: null, t2: true },
  { label: 'K → °C', f: null, k: true }, { label: '°C → K', f: null, k2: true },
  { label: 'atm → Pa', f: 101325 }, { label: 'Pa → atm', f: 1 / 101325 },
  { label: 'J → cal', f: 1 / 4.184 }, { label: 'cal → J', f: 4.184 }
];

function openConstMenu() {
  showMenu('CONSTANT', CONSTANTS.map(function (c) {
    return { label: c.label, act: function () {
      if (c.val === 'π') insertConst('π');
      else if (c.val === 'e') insertConst('e');
      else { ensureEditable(); state.tokens.push(numTokFromNumber(c.v)); render(); }
    } };
  }));
}
function openConvMenu() {
  showMenu('CONVERSION', CONVERSIONS.map(function (c) {
    return { label: c.label, act: function () {
      var v = state.result !== null && isNum(state.result) ? state.result.re : currentValueForMemory().re;
      var out;
      if (c.t) out = (v - 32) * 5 / 9;
      else if (c.t2) out = v * 9 / 5 + 32;
      else if (c.k) out = v - 273.15;
      else if (c.k2) out = v + 273.15;
      else out = v * c.f;
      setResult(C(out, 0));
      state.justEquals = true;
      pushHistory(v + '  ' + c.label, valueToString(C(out, 0)));
    } };
  }));
}

function openOptnMenu() {
  showMenu('OPTIONS', [
    { label: 'CONST  scientific constants', act: openConstMenu },
    { label: 'CONV   unit conversion', act: openConvMenu },
    { label: 'Prob: Ran#', act: function () { insertFn('ran', 'Ran#', true); } },
    { label: 'Prob: RanInt(a,b)', act: function () { insertFn('ranint', 'RanInt('); } },
    { label: 'Rnd(  round to display', act: function () { insertFn('rnd', 'Rnd('); } },
    { label: 'Pol(  rectangular → polar', act: function () { insertFn('pol', 'Pol('); } },
    { label: 'Rec(  polar → rectangular', act: function () { insertFn('rec', 'Rec('); } },
    { label: '∫(    definite integral', act: function () { insertFn('intg', '∫('); } },
    { label: 'd/dx( derivative', act: function () { insertFn('diff', 'd/dx('); } },
    { label: 'Σ(    summation', act: function () { insertFn('sum', 'Σ('); } },
    { label: 'Π(    product', act: function () { insertFn('prod', 'Π('); } },
    { label: 'SOLVE  (also SHIFT + =)', act: runSolve },
    { label: 'CALC   (also ALPHA + =)', act: runCalc },
    { label: 'PreAns previous answer', act: insertPreAns },
    /* --- page 2: complex --- */
    { label: 'i     imaginary unit', act: insertI },
    { label: 'arg(  argument', act: function () { insertFn('arg', 'arg('); } },
    { label: 'Conjg( conjugate', act: function () { insertFn('conjg', 'Conjg('); } },
    { label: 'Re(   real part', act: function () { insertFn('re', 'Re('); } },
    { label: 'Im(   imaginary part', act: function () { insertFn('im', 'Im('); } },
    { label: 'r∠θ ( magnitude + angle )', act: function () { insertFn('rangle', 'r∠θ('); } },
    { label: 'Abs(  absolute value', act: function () { insertFn('abs', 'Abs('); } },
    /* --- page 3: memory --- */
    { label: 'STO   store to variable', act: function () { state.sto = true; render(); } },
    { label: 'RCL   recall variable', act: function () { state.rcl = true; render(); } },
    { label: 'M+    memory plus', act: function () { pressMPlus(1); } },
    { label: 'M-    memory minus', act: function () { pressMPlus(-1); } },
    { label: 'MR    memory recall', act: pressMR },
    { label: 'MC    memory clear', act: pressMC },
    { label: 'det(  determinant', act: function () { insertFn('det', 'det('); } },
    { label: 'Trn(  transpose', act: function () { insertFn('trn', 'Trn('); } },
    { label: 'Dot(  dot product', act: function () { insertFn('dot', 'Dot('); } },
    { label: 'Cross( cross product', act: function () { insertFn('cross', 'Cross('); } },
    /* --- page 4: BASE-N logic --- */
    { label: 'and   (BASE-N)', act: function () { insertOp('and'); } },
    { label: 'or    (BASE-N)', act: function () { insertOp('or'); } },
    { label: 'xor   (BASE-N)', act: function () { insertOp('xor'); } },
    { label: 'xnor  (BASE-N)', act: function () { insertOp('xnor'); } },
    { label: 'not   (BASE-N)', act: function () { state.tokens.push(opTok('not')); render(); } },
    { label: 'Neg   two\'s complement', act: function () { state.tokens.push(opTok('bneg')); render(); } },
    { label: 'Base: DEC / HEX / BIN / OCT', act: openBaseMenu }
  ]);
}
function openBaseMenu() {
  showMenu('BASE', [
    { label: 'DEC  decimal', act: function () { state.base = 'DEC'; render(); } },
    { label: 'HEX  hexadecimal', act: function () { state.base = 'HEX'; render(); } },
    { label: 'BIN  binary', act: function () { state.base = 'BIN'; render(); } },
    { label: 'OCT  octal', act: function () { state.base = 'OCT'; render(); } }
  ]);
}

/* =========================================================================
   THE fx-991EX KEYPAD
   span: how many of the 30 grid columns the key occupies
   main: the legend printed on the key cap
   sub:  the SHIFT function, printed above the key (white)
   alpha:the ALPHA function, printed above the key (red)
   ========================================================================= */
var KEYS = [
  /* ---- row 1 ---- */
  { id: 'shift', span: 7, main: 'SHIFT', cls: 'k-shift',
    press: function (s) { state.shift = !s; state.alpha = false; } },
  { id: 'alpha', span: 7, main: 'ALPHA', cls: 'k-alpha',
    press: function (s, a) { state.alpha = !a; state.shift = false; } },
  { id: 'menu', span: 9, main: 'MODE<span class="tiny">/SETUP</span>',
    press: openModeMenu, sact: openSetupMenu, aact: openOptnMenu },
  { id: 'on', span: 7, main: 'ON', cls: 'k-on', press: pressON },

  /* ---- row 2 ---- */
  { id: 'pow', span: 6, main: 'x<sup>□</sup>', sub: 'ʸ√□', alpha: 'x³',
    press: function () { insertOp('^'); },
    sact: function () { insertFn('nroot', 'ʸ√('); },
    aact: function () { insertPost('³'); } },
  { id: 'sqrt', span: 6, main: '√<span class="tiny">□</span>', sub: '³√□', alpha: 'x⁻¹',
    press: function () { insertFn('sqrt', '√('); },
    sact: function () { insertFn('cbrt', '³√('); },
    aact: function () { insertPost('⁻¹'); } },
  { id: 'sq', span: 6, main: 'x²', sub: 'n!', alpha: 'Abs(',
    press: function () { insertPost('²'); },
    sact: function () { insertPost('!'); },
    aact: function () { insertFn('abs', 'Abs('); } },
  { id: 'log', span: 6, main: 'log', sub: '10<sup>□</sup>', alpha: 'log<sub>□</sub>□',
    press: function () { insertFn('log', 'log('); },
    sact: function () { insertFn('pow10', '10^('); },
    aact: function () { insertFn('log', 'log<sub>a</sub>('); } },
  { id: 'ln', span: 6, main: 'ln', sub: 'e<sup>□</sup>', alpha: 'mod',
    press: function () { insertFn('ln', 'ln('); },
    sact: function () { insertFn('exp', 'e^('); },
    aact: function () { insertOp('mod'); } },

  /* ---- row 3 ---- */
  { id: 'neg', span: 5, main: '(-)', sub: '%', alpha: 'A',
    press: function () { insertOp('-'); },
    sact: function () { insertPost('%'); },
    aact: function () { insertVar('A'); } },
  { id: 'dms', span: 5, main: '° \' "', sub: '▶DMS', alpha: 'B',
    press: insertDms, sact: convertToDMS, aact: function () { insertVar('B'); } },
  { id: 'hyp', span: 5, main: 'hyp', sub: 'Pol(', alpha: 'C',
    press: toggleHyp,
    sact: function () { insertFn('pol', 'Pol('); },
    aact: function () { insertVar('C'); } },
  { id: 'sin', span: 5, main: 'sin', sub: 'sin⁻¹', alpha: 'D',
    press: function () { insTrig('sin'); },
    sact: function () { insertFn('asin', 'sin⁻¹('); },
    aact: function () { insertVar('D'); } },
  { id: 'cos', span: 5, main: 'cos', sub: 'cos⁻¹', alpha: 'E',
    press: function () { insTrig('cos'); },
    sact: function () { insertFn('acos', 'cos⁻¹('); },
    aact: function () { insertVar('E'); } },
  { id: 'tan', span: 5, main: 'tan', sub: 'tan⁻¹', alpha: 'F',
    press: function () { insTrig('tan'); },
    sact: function () { insertFn('atan', 'tan⁻¹('); },
    aact: function () { insertVar('F'); } },

  /* ---- row 4 ---- */
  { id: 'rcl', span: 5, main: 'RCL', sub: 'STO',
    press: function () { state.rcl = true; render(); },
    sact: function () { state.sto = true; render(); } },
  { id: 'eng', span: 5, main: 'ENG', alpha: 'i',
    press: pressEng, aact: insertI },
  { id: 'lp', span: 5, main: '(', sub: 'Σ(',
    press: insertLP, sact: function () { insertFn('sum', 'Σ('); } },
  { id: 'rp', span: 5, main: ')', sub: 'Π(', alpha: 'X',
    press: insertRP,
    sact: function () { insertFn('prod', 'Π('); },
    aact: function () { insertVar('X'); } },
  { id: 'sd', span: 5, main: 'S⇔D', sub: '∫dx', alpha: 'Y',
    press: pressSD,
    sact: function () { insertFn('intg', '∫('); },
    aact: function () { insertVar('Y'); } },
  { id: 'mplus', span: 5, main: 'M+', sub: 'M-', alpha: 'M',
    press: function () { pressMPlus(1); },
    sact: function () { pressMPlus(-1); },
    aact: function () { insertVar('M'); } },

  /* ---- row 5 ---- */
  { id: '7', span: 6, main: '7', cls: 'k-num', press: function () { insertDigit('7'); } },
  { id: '8', span: 6, main: '8', cls: 'k-num', press: function () { insertDigit('8'); } },
  { id: '9', span: 6, main: '9', cls: 'k-num', press: function () { insertDigit('9'); } },
  { id: 'del', span: 6, main: 'DEL', press: pressDel },
  { id: 'ac', span: 6, main: 'AC', cls: 'k-ac', press: pressAC },

  /* ---- row 6 ---- */
  { id: '4', span: 6, main: '4', cls: 'k-num', press: function () { insertDigit('4'); } },
  { id: '5', span: 6, main: '5', cls: 'k-num', press: function () { insertDigit('5'); } },
  { id: '6', span: 6, main: '6', cls: 'k-num', press: function () { insertDigit('6'); } },
  { id: 'mul', span: 6, main: '×', cls: 'k-op', press: function () { insertOp('*'); } },
  { id: 'div', span: 6, main: '÷', cls: 'k-op', press: function () { insertOp('/'); } },

  /* ---- row 7 ---- */
  { id: '1', span: 6, main: '1', cls: 'k-num', press: function () { insertDigit('1'); } },
  { id: '2', span: 6, main: '2', cls: 'k-num', press: function () { insertDigit('2'); } },
  { id: '3', span: 6, main: '3', cls: 'k-num', press: function () { insertDigit('3'); } },
  { id: 'plus', span: 6, main: '+', sub: 'Pol(', cls: 'k-op',
    press: function () { insertOp('+'); },
    sact: function () { insertFn('pol', 'Pol('); } },
  { id: 'minus', span: 6, main: '−', sub: 'Rec(', cls: 'k-op',
    press: function () { insertOp('-'); },
    sact: function () { insertFn('rec', 'Rec('); } },

  /* ---- row 8 ---- */
  { id: '0', span: 6, main: '0', sub: 'Ran#', cls: 'k-num',
    press: function () { insertDigit('0'); },
    sact: function () { insertFn('ran', 'Ran#', true); } },
  { id: 'dot', span: 6, main: '.', sub: 'Rnd(', cls: 'k-num',
    press: insertDot, sact: function () { insertFn('rnd', 'Rnd('); } },
  { id: 'exp', span: 6, main: '×10<sup>x</sup>', sub: 'π', alpha: 'e',
    press: insertExp,
    sact: function () { insertConst('π'); },
    aact: function () { insertConst('e'); } },
  { id: 'ans', span: 6, main: 'Ans', sub: 'd/dx',
    press: insertAns, sact: function () { insertFn('diff', 'd/dx('); } },
  { id: 'eq', span: 6, main: '=', sub: 'SOLVE', alpha: 'CALC', cls: 'k-eq',
    press: pressEquals, sact: runSolve, aact: runCalc }
];

var KEY_BY_ID = {};
KEYS.forEach(function (k) { KEY_BY_ID[k.id] = k; });

/* in BASE-N hex mode these keys type the hex digits A-F directly */
var HEX_KEYS = { neg: 'A', dms: 'B', hyp: 'C', sin: 'D', cos: 'E', tan: 'F' };

function buildKeypad() {
  var kp = $('keypad');
  kp.innerHTML = '';
  KEYS.forEach(function (k) {
    var b = el('div', 'key' + (k.cls ? ' ' + k.cls : ''));
    b.style.gridColumn = 'span ' + k.span;
    b.setAttribute('data-id', k.id);
    var top = el('div', 'k-top');
    if (k.sub) { var s1 = el('span', 'k-sub'); s1.innerHTML = k.sub; top.appendChild(s1); }
    if (k.alpha) { var s2 = el('span', 'k-alpha'); s2.innerHTML = k.alpha; top.appendChild(s2); }
    b.appendChild(top);
    var m = el('div', 'k-main');
    m.innerHTML = k.main;
    b.appendChild(m);
    b.addEventListener('click', function () { pressKeyById(k.id); });
    kp.appendChild(b);
  });
}
function keyEl(id) { return document.querySelector('.key[data-id="' + id + '"]'); }
function flash(id) {
  var e = keyEl(id);
  if (!e) return;
  e.classList.add('pressed');
  setTimeout(function () { e.classList.remove('pressed'); }, 95);
}
function updateArmedKeys() {
  var s = keyEl('shift'), a = keyEl('alpha');
  if (s) s.classList.toggle('armed', state.shift);
  if (a) a.classList.toggle('armed', state.alpha);
  var h = keyEl('hyp');
  if (h) h.classList.toggle('armed', state.hyp);
}

/** Central key dispatcher: every click and every keyboard shortcut lands here. */
function pressKeyById(id) {
  if (id !== 'shift' && id !== 'alpha') flash(id);

  if (state.menu) { menuKey(id); return; }
  if (state.prompt) { promptKey(id); return; }
  if (state.editor) { editorKey(id); return; }

  var k = KEY_BY_ID[id];
  if (!k) return;

  // BASE-N: the trig/dms/hyp keys become the hex digits A..F
  if (state.mode === 'BASE-N' && state.base === 'HEX' && HEX_KEYS[id]) {
    state.shift = false; state.alpha = false;
    insertDigit(HEX_KEYS[id]);
    return;
  }

  var s = state.shift, a = state.alpha;
  state.shift = false; state.alpha = false;
  var fn = (s && k.sact) ? k.sact : (a && k.aact) ? k.aact : k.press;
  if (fn) fn(s, a);
  render();
}

/* ---- keys pressed while a menu is open -------------------------------- */
function menuKey(id) {
  var m = state.menu;
  if (!m) return;
  if (id === 'ac') { closeMenu(); return; }
  if (id === 'del') { closeMenu(); return; }
  if (id === 'up') { m.sel = (m.sel - 1 + menuPageItems(m).length) % menuPageItems(m).length; render(); return; }
  if (id === 'down') { m.sel = (m.sel + 1) % menuPageItems(m).length; render(); return; }
  if (id === 'eq') { menuRun(m, m.sel); return; }
  var n = -1;
  if (id >= '0' && id <= '9' && id.length === 1) n = parseInt(id, 10);
  if (n === 0) {
    var pages = Math.ceil(m.items.length / PER_PAGE);
    if (pages > 1) { m.page = (m.page + 1) % pages; m.sel = 0; render(); }
    return;
  }
  if (n >= 1 && n <= 9) menuRun(m, n - 1);
}

/* ---- keys pressed while a "X?" prompt is open ------------------------- */
function promptKey(id) {
  var p = state.prompt;
  if (!p) return;
  if (id === 'ac') { state.prompt = null; render(); return; }
  if (id === 'eq') { finishPrompt(); return; }
  if (id === 'del') { p.value = p.value.slice(0, -1); render(); return; }
  if (id === 'dot') { if (p.value.indexOf('.') < 0) p.value += p.value === '' ? '0.' : '.'; render(); return; }
  if (id === 'neg') { p.value = p.value.charAt(0) === '-' ? p.value.slice(1) : '-' + p.value; render(); return; }
  if (id.length === 1 && id >= '0' && id <= '9') { p.value += id; render(); return; }
}

/* ---- keys pressed while a data editor panel is open -------------------- */
function editorKey(id) {
  if (id === 'ac') { closeEditor(); return; }
  if (state.editor && state.editor.onKey) state.editor.onKey(id);
}
/* =========================================================================
   12. MODES
   ========================================================================= */

function showValuePanel(title, rows) {
  var p = openEditor(title, 'AC = exit');
  rows.forEach(function (l) {
    var r = el('div', 'row');
    r.innerHTML = l;
    p.res.appendChild(r);
  });
  state.editor = { kind: 'panel' };
  return p;
}

/* ------------------------------------------------------------------ *
 * 12.1  EQN — equations and systems of equations
 * ------------------------------------------------------------------ */
function openEqnMode() {
  showMenu('EQUATION / FUNCTION', [
    { label: 'Linear           aX + b = 0', act: function () { eqnPoly(1); } },
    { label: 'Quadratic        aX² + bX + c = 0', act: function () { eqnPoly(2); } },
    { label: 'Cubic            aX³ + bX² + cX + d = 0', act: function () { eqnPoly(3); } },
    { label: 'Simultaneous  2 unknowns', act: function () { eqnSim(2); } },
    { label: 'Simultaneous  3 unknowns', act: function () { eqnSim(3); } },
    { label: 'Simultaneous  4 unknowns', act: function () { eqnSim(4); } }
  ]);
}

function quadRoots(a, b, c) {                       // returns [C, C]
  if (Math.abs(a) < 1e-15) {                        // linear
    if (Math.abs(b) < 1e-15) mathError();
    return [C(-c / b, 0), C(-c / b, 0)];
  }
  var disc = csub(cmul(C(b, 0), C(b, 0)), cmul(C(4 * a, 0), C(c, 0)));
  var sq = csqrt(disc);
  return [cdiv(cadd(cneg(C(b, 0)), sq), C(2 * a, 0)),
          cdiv(csub(cneg(C(b, 0)), sq), C(2 * a, 0))];
}
function cubicRoots(a, b, c, d) {                   // returns [C, C, C]
  if (Math.abs(a) < 1e-15) { var q = quadRoots(b, c, d); return [q[0], q[1], q[1]]; }
  var A = b / a, B = c / a, Cc = d / a;
  var p = B - A * A / 3;
  var qq = 2 * A * A * A / 27 - A * B / 3 + Cc;
  var shift = -A / 3;
  var disc = qq * qq / 4 + p * p * p / 27;
  var r1, r2, r3;
  if (disc > 0) {
    var u = Math.cbrt(-qq / 2 + Math.sqrt(disc));
    var v = Math.cbrt(-qq / 2 - Math.sqrt(disc));
    r1 = C(u + v + shift, 0);
    var t1 = u + v;
    var qa = C(1, 0), qb = C(t1, 0), qc = C(t1 * t1 + p, 0);
    var s = csqrt(csub(cmul(qb, qb), cmul(C(4, 0), qc)));
    r2 = cdiv(cadd(cneg(qb), s), C(2, 0)).re + shift;
    r3 = cdiv(csub(cneg(qb), s), C(2, 0)).re + shift;
    return [r1, C(r2, 0), C(r3, 0)];
  }
  if (Math.abs(p) < 1e-15) {
    var t = Math.cbrt(-qq);
    return [C(t + shift, 0), C(t + shift, 0), C(t + shift, 0)];
  }
  var m = 2 * Math.sqrt(-p / 3);
  var arg = clamp((3 * qq) / (2 * p) * Math.sqrt(-3 / p), -1, 1);
  var th = Math.acos(arg) / 3;
  var out = [];
  for (var k = 0; k < 3; k++) out.push(C(m * Math.cos(th - 2 * Math.PI * k / 3) + shift, 0));
  return out;
}

function eqnPoly(deg) {
  state.editor = { kind: 'eqn' };
  var labels = ['a', 'b', 'c', 'd'];
  var p = openEditor('EQN  polynomial', 'AC = exit');
  var tbl = el('table', 'ed-table');
  var tr = el('tr');
  for (var i = 0; i <= deg; i++) tr.appendChild(el('th', null, labels[i]));
  tbl.appendChild(tr);
  var tr2 = el('tr'), inputs = [];
  for (var j = 0; j <= deg; j++) {
    var td = el('td');
    inputs.push(edInput(td, j === 0 ? 1 : (j === deg ? 1 : 0)));
    tr2.appendChild(td);
  }
  tbl.appendChild(tr2);
  p.body.appendChild(tbl);
  p.body.appendChild(el('div', 'ed-note',
    deg === 1 ? 'aX + b = 0' : deg === 2 ? 'aX² + bX + c = 0' : 'aX³ + bX² + cX + d = 0'));

  edButton(p.foot, 'SOLVE', function () {
    var co = inputs.map(function (i2) { return parseInputNumber(i2.value) || 0; });
    var rows;
    try {
      var roots;
      if (deg === 1) {
        if (Math.abs(co[0]) < 1e-15) throw new CalcError('No Solution');
        roots = [C(-co[1] / co[0], 0)];
      } else if (deg === 2) {
        roots = quadRoots(co[0], co[1], co[2]);
      } else {
        roots = cubicRoots(co[0], co[1], co[2], co[3]);
      }
      rows = roots.map(function (r, i) { return '<b>X' + (i + 1) + ' =</b> ' + fmtComplex(r); });
    } catch (e) {
      rows = ['<b>' + (e.message || 'Math ERROR') + '</b>'];
    }
    showValuePanel('EQN result', rows);
  }, true);
}

function eqnSim(n) {
  state.editor = { kind: 'eqn' };
  var names = ['X', 'Y', 'Z', 'W'];
  var p = openEditor('EQN  ' + n + ' unknowns', 'AC = exit');
  var tbl = el('table', 'ed-table');
  var hr = el('tr');
  hr.appendChild(el('th', null, ''));
  for (var c = 0; c < n; c++) hr.appendChild(el('th', null, names[c]));
  hr.appendChild(el('th', null, '='));
  tbl.appendChild(hr);
  var inputs = [];
  for (var r = 0; r < n; r++) {
    var tr = el('tr');
    tr.appendChild(el('td', 'idx', String(r + 1)));
    inputs[r] = [];
    for (var c2 = 0; c2 <= n; c2++) {
      var td = el('td');
      var inp = edInput(td, c2 === n ? 0 : (r === c2 ? 1 : 0));
      inputs[r].push(inp);
      tr.appendChild(td);
    }
    tbl.appendChild(tr);
  }
  p.body.appendChild(tbl);

  edButton(p.foot, 'SOLVE', function () {
    var A = [], b = [];
    for (var i = 0; i < n; i++) {
      b.push(parseInputNumber(inputs[i][n].value) || 0);
      A.push([]);
      for (var j = 0; j < n; j++) A[i].push(C(parseInputNumber(inputs[i][j].value) || 0, 0));
    }
    var rows;
    try {
      var sol = matSolve(Mat(n, n, [].concat.apply([], A)), Vct(n, b.map(function (x) { return C(x, 0); })));
      if (!sol) rows = ['<b>No Solution</b>', 'The system is singular or inconsistent.'];
      else rows = sol.data.map(function (v, i) { return '<b>' + names[i] + ' =</b> ' + fmtComplex(v); });
    } catch (e) {
      rows = ['<b>' + (e.message || 'Math ERROR') + '</b>'];
    }
    showValuePanel('EQN result', rows);
  }, true);
}

/* ------------------------------------------------------------------ *
 * 12.2  STAT — 1-variable / 2-variable statistics and regression
 * ------------------------------------------------------------------ */
function openStatMode() {
  showMenu('STATISTICS', [
    { label: '1-VAR   single variable', act: function () { state.stats.two = false; openStatEditor(); } },
    { label: '2-VAR   paired data + regression', act: function () { state.stats.two = true; openStatEditor(); } }
  ]);
}
function statData() {
  var s = state.stats;
  var xs = s.x.filter(function (v) { return isFinite(v); });
  var ys = s.two ? s.y.filter(function (v) { return isFinite(v); }) : [];
  var n = s.two ? Math.min(xs.length, ys.length) : xs.length;
  return { x: xs.slice(0, n), y: ys.slice(0, n), n: n };
}
function sum(arr) { return arr.reduce(function (a, b) { return a + b; }, 0); }
function medianOf(arr) {
  if (!arr.length) return NaN;
  var a = arr.slice().sort(function (p, q) { return p - q; });
  var m = Math.floor(a.length / 2);
  return a.length % 2 ? a[m] : (a[m - 1] + a[m]) / 2;
}
function statsHTML() {
  var d = statData();
  if (!d.n) return '<b>No data</b>';
  var mean = sum(d.x) / d.n;
  var ss = sum(d.x.map(function (v) { return v * v; }));
  var sx = Math.sqrt(Math.max(0, (ss - d.n * mean * mean) / (d.n - 1 || 1)));
  var sigx = Math.sqrt(Math.max(0, (ss - d.n * mean * mean) / d.n));
  var rows = [
    '<b>n</b> = ' + d.n,
    '<b>x&#772;</b> = ' + fmtNum(mean),
    '<b>&Sigma;x</b> = ' + fmtNum(sum(d.x)),
    '<b>&Sigma;x²</b> = ' + fmtNum(ss),
    '<b>&sigma;x</b> = ' + fmtNum(sigx),
    '<b>sx</b> = ' + fmtNum(sx),
    '<b>minX</b> = ' + fmtNum(Math.min.apply(null, d.x)),
    '<b>maxX</b> = ' + fmtNum(Math.max.apply(null, d.x)),
    '<b>median</b> = ' + fmtNum(medianOf(d.x))
  ];
  if (state.stats.two) {
    var y = d.y, my = sum(y) / y.length;
    var sy = Math.sqrt(Math.max(0, (sum(y.map(function (v) { return v * v; })) - y.length * my * my) / (y.length - 1 || 1)));
    var sxy = 0;
    for (var i = 0; i < y.length; i++) sxy += d.x[i] * y[i];
    rows.push('<b>&#772;y</b> = ' + fmtNum(my),
              '<b>&Sigma;y</b> = ' + fmtNum(sum(y)),
              '<b>&Sigma;y²</b> = ' + fmtNum(sum(y.map(function (v) { return v * v; }))),
              '<b>&Sigma;xy</b> = ' + fmtNum(sxy),
              '<b>&sigma;y</b> = ' + fmtNum(Math.sqrt(Math.max(0, (sum(y.map(function (v) { return v * v; })) - y.length * my * my) / y.length))),
              '<b>sy</b> = ' + fmtNum(sy));
  }
  var reg = state.stats.reg;
  if (reg) {
    rows.push('<b>— regression —</b>');
    rows.push(reg.text);
    rows.push('<b>a</b> = ' + fmtNum(reg.a) + (reg.c !== undefined ? '   <b>b</b> = ' + fmtNum(reg.b) + '   <b>c</b> = ' + fmtNum(reg.c) : '   <b>b</b> = ' + fmtNum(reg.b)));
    if (reg.r !== undefined) rows.push('<b>r</b> = ' + fmtNum(reg.r) + '   <b>r²</b> = ' + fmtNum(reg.r * reg.r));
  }
  return rows.map(function (r) { return '<div class="row">' + r + '</div>'; }).join('');
}
function openStatEditor() {
  var two = state.stats.two;
  state.editor = { kind: 'stat' };
  var p = openEditor('STAT  ' + (two ? '2-VAR' : '1-VAR'), 'AC = exit');
  var tbl = el('table', 'ed-table');
  p.body.appendChild(tbl);
  function rebuild() {
    tbl.innerHTML = '';
    var hr = el('tr');
    hr.appendChild(el('th', null, '#'));
    hr.appendChild(el('th', null, 'X'));
    if (two) hr.appendChild(el('th', null, 'Y'));
    tbl.appendChild(hr);
    for (var i = 0; i < state.stats.x.length; i++) {
      (function (i) {
        var tr = el('tr');
        tr.appendChild(el('td', 'idx', String(i + 1)));
        var td1 = el('td');
        var in1 = edInput(td1, state.stats.x[i]);
        in1.addEventListener('change', function () { state.stats.x[i] = parseInputNumber(in1.value) || 0; });
        tr.appendChild(td1);
        if (two) {
          var td2 = el('td');
          var in2 = edInput(td2, state.stats.y[i]);
          in2.addEventListener('change', function () { state.stats.y[i] = parseInputNumber(in2.value) || 0; });
          tr.appendChild(td2);
        }
        tbl.appendChild(tr);
      })(i);
    }
  }
  rebuild();
  edButton(p.foot, '+ Row', function () { state.stats.x.push(0); if (two) state.stats.y.push(0); rebuild(); });
  edButton(p.foot, '− Row', function () { state.stats.x.pop(); if (two) state.stats.y.pop(); rebuild(); });
  edButton(p.foot, 'Clear', function () { state.stats.x = []; state.stats.y = []; rebuild(); p.res.innerHTML = ''; });
  edButton(p.foot, 'Results', function () { p.res.innerHTML = statsHTML(); }, true);
  if (two) edButton(p.foot, 'Regression', function () { regressionMenu(); });
  if (state.stats.reg) {
    edButton(p.foot, 'ŷ(x)', function () {
      startPrompt('x?', 0, function (x) {
        showValuePanel('Prediction', ['<b>ŷ =</b> ' + fmtNum(regPredict(state.stats.reg, x))]);
      });
    });
    edButton(p.foot, 'x̂(y)', function () {
      startPrompt('y?', 0, function (y) {
        showValuePanel('Prediction', ['<b>x̂ =</b> ' + fmtNum(regInverse(state.stats.reg, y))]);
      });
    });
  }
  if (state.stats.lastHTML) p.res.innerHTML = state.stats.lastHTML;
}
function regressionMenu() {
  showMenu('REGRESSION', [
    { label: 'Linear     y = a + bx', act: function () { doRegression('lin'); } },
    { label: 'Quadratic  y = a + bx + cx²', act: function () { doRegression('quad'); } },
    { label: 'Logarithmic y = a + b·ln x', act: function () { doRegression('log'); } },
    { label: 'Exponential y = a·e^(bx)', act: function () { doRegression('exp'); } },
    { label: 'Power      y = a·x^b', act: function () { doRegression('pow'); } },
    { label: 'Inverse    y = a + b/x', act: function () { doRegression('inv'); } }
  ]);
}
function doRegression(type) {
  var d = statData();
  if (d.n < 2) { state.stats.reg = null; openStatEditor(); return; }
  var n = d.n, x = d.x, y = d.y;
  var SX = sum(x), SY = sum(y), SXX = sum(x.map(function (v) { return v * v; }));
  var SYY = sum(y.map(function (v) { return v * v; }));
  var SXY = 0;
  for (var i = 0; i < n; i++) SXY += x[i] * y[i];
  var a, b, c, r;
  function rsq(f) {
    var my = SY / n, ss = 0, sst = 0;
    for (var i = 0; i < n; i++) { ss += Math.pow(y[i] - f(x[i]), 2); sst += Math.pow(y[i] - my, 2); }
    return sst === 0 ? 1 : Math.max(0, 1 - ss / sst);
  }
  if (type === 'lin' || type === 'inv' || type === 'log') {
    var xs = x.map(function (v) { return type === 'lin' ? v : (type === 'inv' ? 1 / v : Math.log(v)); });
    if (xs.some(function (v) { return !isFinite(v); })) { state.stats.reg = null; openStatEditor(); return; }
    var SX2 = sum(xs), SXX2 = sum(xs.map(function (v) { return v * v; })), SXY2 = 0;
    for (var i2 = 0; i2 < n; i2++) SXY2 += xs[i2] * y[i2];
    var den = n * SXX2 - SX2 * SX2;
    if (Math.abs(den) < 1e-14) { state.stats.reg = null; openStatEditor(); return; }
    b = (n * SXY2 - SX2 * SY) / den;
    a = (SY - b * SX2) / n;
    var f = function (v) { var t = type === 'lin' ? v : (type === 'inv' ? 1 / v : Math.log(v)); return a + b * t; };
    r = Math.sqrt(rsq(f));
    if ((n * SXX2 - SX2 * SX2) !== 0) {
      var num = n * SXY2 - SX2 * SY;
      var den2 = Math.sqrt((n * SXX2 - SX2 * SX2) * (n * SYY - SY * SY));
      r = den2 === 0 ? 1 : num / den2;
    }
    state.stats.reg = { type: type, a: a, b: b,
      text: type === 'lin' ? 'y = a + bx' : (type === 'inv' ? 'y = a + b/x' : 'y = a + b·ln x'), r: r };
  } else if (type === 'quad') {
    var S3 = sum(x.map(function (v) { return v * v * v; }));
    var S4 = sum(x.map(function (v) { return Math.pow(v, 4); }));
    var T2 = 0;
    for (var i3 = 0; i3 < n; i3++) T2 += x[i3] * x[i3] * y[i3];
    var sol = solveLinear(
      [[n, SX, SXX], [SX, SXX, S3], [SXX, S3, S4]],
      [SY, SXY, T2]);
    if (!sol) { state.stats.reg = null; openStatEditor(); return; }
    a = sol[0]; b = sol[1]; c = sol[2];
    var f2 = function (v) { return a + b * v + c * v * v; };
    r = Math.sqrt(rsq(f2));
    state.stats.reg = { type: 'quad', a: a, b: b, c: c, text: 'y = a + bx + cx²', r: r };
  } else {
    var ok = x.every(function (v) { return v > 0; }) && (type === 'pow' ? y.every(function (v) { return v > 0; }) : true);
    if (type === 'exp') ok = y.every(function (v) { return v > 0; });
    if (!ok) { state.stats.reg = null; openStatEditor(); return; }
    var lx = x.map(function (v) { return Math.log(v); });
    var ly = y.map(function (v) { return Math.log(v); });
    var SLX = sum(lx), SLY = sum(ly), SLXX = sum(lx.map(function (v) { return v * v; }));
    var SLXY = 0;
    for (var i4 = 0; i4 < n; i4++) SLXY += lx[i4] * ly[i4];
    var den3 = n * SLXX - SLX * SLX;
    if (Math.abs(den3) < 1e-14) { state.stats.reg = null; openStatEditor(); return; }
    b = (n * SLXY - SLX * SLY) / den3;
    a = Math.exp((SLY - b * SLX) / n);
    var f3 = type === 'exp' ? function (v) { return a * Math.exp(b * v); }
                            : function (v) { return a * Math.pow(v, b); };
    r = Math.sqrt(rsq(f3));
    state.stats.reg = { type: type, a: a, b: b,
      text: type === 'exp' ? 'y = a·e^(bx)' : 'y = a·x^b', r: r };
  }
  state.stats.lastHTML = statsHTML();
  openStatEditor();
}
function regPredict(m, x) {
  switch (m.type) {
    case 'lin': return m.a + m.b * x;
    case 'inv': return m.a + m.b / x;
    case 'log': return m.a + m.b * Math.log(x);
    case 'exp': return m.a * Math.exp(m.b * x);
    case 'pow': return m.a * Math.pow(x, m.b);
    case 'quad': return m.a + m.b * x + m.c * x * x;
  }
  return NaN;
}
function regInverse(m, y) {
  switch (m.type) {
    case 'lin': return (y - m.a) / m.b;
    case 'inv': return m.b / (y - m.a);
    case 'log': return Math.exp((y - m.a) / m.b);
    case 'exp': return Math.log(y / m.a) / m.b;
    case 'pow': return Math.pow(y / m.a, 1 / m.b);
  }
  // quadratic: solve numerically
  var lo = -1e9, hi = 1e9, best = NaN, bestErr = Infinity;
  for (var i = 0; i <= 400; i++) {
    var x = lo + (hi - lo) * i / 400, e = Math.abs(regPredict(m, x) - y);
    if (e < bestErr) { bestErr = e; best = x; }
  }
  return best;
}

/* ------------------------------------------------------------------ *
 * 12.3  MATRIX
 * ------------------------------------------------------------------ */
function openMatrixMode() {
  showMenu('MATRIX', [
    { label: 'MatA   insert MatA', act: function () { ensureEditable(); state.tokens.push(tok('mat', 'MatA')); render(); } },
    { label: 'MatB   insert MatB', act: function () { ensureEditable(); state.tokens.push(tok('mat', 'MatB')); render(); } },
    { label: 'MatC   insert MatC', act: function () { ensureEditable(); state.tokens.push(tok('mat', 'MatC')); render(); } },
    { label: 'Dim    set dimensions', act: matrixDimMenu },
    { label: 'Data   edit values', act: matrixDataMenu },
    { label: 'det(   determinant', act: function () { insertFn('det', 'det('); } },
    { label: 'Trn(   transpose', act: function () { insertFn('trn', 'Trn('); } },
    { label: 'Identity( n )', act: function () { insertFn('ident', 'Identity('); } },
    { label: 'Help — what you can type', act: function () {
        showValuePanel('MATRIX help', [
          'MatA+MatB   MatA−MatB   MatA×MatB',
          'MatA÷MatB (= MatA×MatB⁻¹)',
          'det(MatA)   Trn(MatA)   MatA⁻¹',
          '3×MatA   MatA²   MatA³',
          'Press = to see a matrix result.'
        ]);
      } }
  ]);
}
function matrixDimMenu() {
  showMenu('MATRIX DIM', ['MatA', 'MatB', 'MatC'].map(function (name) {
    return { label: name, act: function () {
      promptChain([
        { key: 'r', label: name + ' rows?', value: (state.mats[name] ? state.mats[name].rows : 2) },
        { key: 'c', label: name + ' columns?', value: (state.mats[name] ? state.mats[name].cols : 2) }
      ], function (v) {
        var r = clamp(Math.round(v.r), 1, 6), c = clamp(Math.round(v.c), 1, 6);
        state.mats[name] = Mat(r, c);
        openMatrixEditor(name);
      });
    } };
  }));
}
function matrixDataMenu() {
  showMenu('MATRIX DATA', ['MatA', 'MatB', 'MatC'].map(function (name) {
    return { label: name, act: function () {
      if (!state.mats[name]) {
        promptChain([
          { key: 'r', label: name + ' rows?', value: 2 },
          { key: 'c', label: name + ' columns?', value: 2 }
        ], function (v) {
          state.mats[name] = Mat(clamp(Math.round(v.r), 1, 6), clamp(Math.round(v.c), 1, 6));
          openMatrixEditor(name);
        });
      } else openMatrixEditor(name);
    } };
  }));
}
function openMatrixEditor(name) {
  state.editor = { kind: 'matrix', name: name };
  var m = state.mats[name];
  var p = openEditor(name + '  ' + m.rows + '×' + m.cols, 'AC = exit');
  var grid = el('div', 'matwrap');
  var inner = el('div', 'matgrid');
  inner.style.gridTemplateColumns = 'repeat(' + m.cols + ', auto)';
  var inputs = [];
  for (var r = 0; r < m.rows; r++) {
    for (var c = 0; c < m.cols; c++) {
      inputs.push(edInput(inner, fmtComplex(m.data[r * m.cols + c])));
    }
  }
  grid.appendChild(el('span', 'matbracket'));
  grid.appendChild(inner);
  grid.appendChild(el('span', 'matbracket'));
  p.body.appendChild(grid);
  edButton(p.foot, 'SAVE', function () {
    var vals = inputs.map(function (i) { return parseInputNumber(i.value) || 0; });
    state.mats[name] = Mat(m.rows, m.cols, vals.map(function (v) { return C(v, 0); }));
    openMatrixMode();
  }, true);
  edButton(p.foot, 'Cancel', openMatrixMode);
}

/* ------------------------------------------------------------------ *
 * 12.4  VECTOR
 * ------------------------------------------------------------------ */
function openVectorMode() {
  showMenu('VECTOR', [
    { label: 'VctA   insert VctA', act: function () { ensureEditable(); state.tokens.push(tok('vct', 'VctA')); render(); } },
    { label: 'VctB   insert VctB', act: function () { ensureEditable(); state.tokens.push(tok('vct', 'VctB')); render(); } },
    { label: 'VctC   insert VctC', act: function () { ensureEditable(); state.tokens.push(tok('vct', 'VctC')); render(); } },
    { label: 'Dim    set dimension', act: vectorDimMenu },
    { label: 'Data   edit values', act: vectorDataMenu },
    { label: 'Dot(   dot product', act: function () { insertFn('dot', 'Dot('); } },
    { label: 'Cross( cross product', act: function () { insertFn('cross', 'Cross('); } },
    { label: 'Abs(   magnitude', act: function () { insertFn('abs', 'Abs('); } },
    { label: 'Help — what you can type', act: function () {
        showValuePanel('VECTOR help', [
          'VctA+VctB   VctA−VctB',
          'VctA×VctB  = cross product',
          'Dot(VctA,VctB)  Cross(VctA,VctB)',
          'Abs(VctA)  = magnitude',
          '3×VctA   VctA×MatA'
        ]);
      } }
  ]);
}
function vectorDimMenu() {
  showMenu('VECTOR DIM', ['VctA', 'VctB', 'VctC'].map(function (name) {
    return { label: name, act: function () {
      startPrompt(name + ' dimension (2 or 3)?', (state.vcts[name] ? state.vcts[name].n : 3), function (v) {
        state.vcts[name] = Vct(clamp(Math.round(v), 1, 3));
        openVectorEditor(name);
      });
    } };
  }));
}
function vectorDataMenu() {
  showMenu('VECTOR DATA', ['VctA', 'VctB', 'VctC'].map(function (name) {
    return { label: name, act: function () {
      if (!state.vcts[name]) {
        startPrompt(name + ' dimension (2 or 3)?', 3, function (v) {
          state.vcts[name] = Vct(clamp(Math.round(v), 1, 3));
          openVectorEditor(name);
        });
      } else openVectorEditor(name);
    } };
  }));
}
function openVectorEditor(name) {
  state.editor = { kind: 'vector', name: name };
  var v = state.vcts[name];
  var p = openEditor(name + '  (' + v.n + ')', 'AC = exit');
  var grid = el('div', 'matwrap');
  var inner = el('div', 'matgrid');
  inner.style.gridTemplateColumns = 'repeat(' + v.n + ', auto)';
  var inputs = [];
  for (var i = 0; i < v.n; i++) inputs.push(edInput(inner, fmtComplex(v.data[i])));
  grid.appendChild(el('span', 'matbracket'));
  grid.appendChild(inner);
  grid.appendChild(el('span', 'matbracket'));
  p.body.appendChild(grid);
  edButton(p.foot, 'SAVE', function () {
    state.vcts[name] = Vct(v.n, inputs.map(function (i2) { return C(parseInputNumber(i2.value) || 0, 0); }));
    openVectorMode();
  }, true);
  edButton(p.foot, 'Cancel', openVectorMode);
}

/* ------------------------------------------------------------------ *
 * 12.5  TABLE  (f(X) over a range)
 * ------------------------------------------------------------------ */
function openTableMode() {
  state.editor = { kind: 'table' };
  var p = openEditor('TABLE  f(X)', 'AC = exit');
  var t = el('table', 'ed-table');
  var r1 = el('tr');
  r1.appendChild(el('th', null, 'f(X) ='));
  var td = el('td');
  var fIn = edInput(td, state.tbl.f, true);
  r1.appendChild(td);
  t.appendChild(r1);
  var mk = function (label, val) {
    var tr = el('tr');
    tr.appendChild(el('th', null, label));
    var tdx = el('td');
    var inp = edInput(tdx, val);
    tr.appendChild(tdx);
    t.appendChild(tr);
    return inp;
  };
  var sIn = mk('Start', state.tbl.start);
  var eIn = mk('End', state.tbl.end);
  var stIn = mk('Step', state.tbl.step);
  p.body.appendChild(t);
  p.body.appendChild(el('div', 'ed-note', 'Any expression in X, e.g. X²−3X+2'));
  edButton(p.foot, 'TABLE', function () {
    var f = fIn.value, a, b, st;
    try {
      a = parseInputNumber(sIn.value); b = parseInputNumber(eIn.value); st = parseInputNumber(stIn.value);
    } catch (e) { p.res.innerHTML = '<b>Syntax ERROR</b>'; return; }
    if (!st || (b - a) / st > 200 || (b - a) / st < 0) { p.res.innerHTML = '<b>Range ERROR</b> (max 200 rows)'; return; }
    state.tbl = { f: f, start: a, end: b, step: st };
    var rows = [];
    for (var x = a; x <= b + 1e-9; x += st) {
      var y;
      try { y = fmtComplex(evalString(f, { X: x })); } catch (e) { y = 'ERROR'; }
      rows.push('<tr><td class="idx">' + fmtNum(x) + '</td><td>' + y + '</td></tr>');
    }
    p.res.innerHTML = '<table class="ed-table"><tr><th>X</th><th>f(X)</th></tr>' + rows.join('') + '</table>';
  }, true);
  edButton(p.foot, 'Clear', function () { p.res.innerHTML = ''; });
}

/* ------------------------------------------------------------------ *
 * 12.6  RATIO  (proportions:  a : b = c : X )
 * ------------------------------------------------------------------ */
function openRatioMode() {
  showMenu('RATIO', [
    { label: 'a : b = c : X   (find X)', act: function () {
        promptChain([
          { key: 'a', label: 'a?', value: 2 },
          { key: 'b', label: 'b?', value: 3 },
          { key: 'c', label: 'c?', value: 8 }
        ], function (v) {
          if (!v.a) { showValuePanel('RATIO', ['<b>Math ERROR</b>']); return; }
          showValuePanel('RATIO  a:b = c:X', [
            v.a + ' : ' + v.b + ' = ' + v.c + ' : <b>' + fmtNum(v.c * v.b / v.a) + '</b>'
          ]);
        });
      } },
    { label: 'a : b = X : d   (find X)', act: function () {
        promptChain([
          { key: 'a', label: 'a?', value: 2 },
          { key: 'b', label: 'b?', value: 3 },
          { key: 'd', label: 'd?', value: 12 }
        ], function (v) {
          if (!v.b) { showValuePanel('RATIO', ['<b>Math ERROR</b>']); return; }
          showValuePanel('RATIO  a:b = X:d', [
            v.a + ' : ' + v.b + ' = <b>' + fmtNum(v.a * v.d / v.b) + '</b> : ' + v.d
          ]);
        });
      } }
  ]);
}

/* ------------------------------------------------------------------ *
 * 12.7  DISTRIBUTION
 * ------------------------------------------------------------------ */
function erf(x) {
  var s = x < 0 ? -1 : 1;
  x = Math.abs(x);
  var t = 1 / (1 + 0.3275911 * x);
  var y = 1 - (((((1.061405429 * t - 1.453152027) * t) + 1.421413741) * t - 0.284496736) * t + 0.254829592) * t * Math.exp(-x * x);
  return s * y;
}
function normPdf(x, mu, sg) { return Math.exp(-Math.pow(x - mu, 2) / (2 * sg * sg)) / (sg * Math.sqrt(2 * Math.PI)); }
function normCdf(x, mu, sg) { return 0.5 * (1 + erf((x - mu) / (sg * Math.SQRT2))); }
function invNorm(p, mu, sg) {
  var lo = -1e4, hi = 1e4, i;
  for (i = 0; i < 200; i++) {
    var mid = (lo + hi) / 2;
    if (normCdf(mid, mu, sg) < p) lo = mid; else hi = mid;
  }
  return (lo + hi) / 2;
}
function binomPdf(x, n, p) {
  if (x < 0 || x > n) return 0;
  var lgamma = Math.log(gammaFn(n + 1)) - Math.log(gammaFn(x + 1)) - Math.log(gammaFn(n - x + 1));
  return Math.exp(lgamma + x * Math.log(p) + (n - x) * Math.log(1 - p));
}
function binomCdf(x, n, p) {
  var s = 0;
  for (var i = 0; i <= Math.floor(x); i++) s += binomPdf(i, n, p);
  return s;
}
function poissonPdf(x, lam) { return Math.exp(-lam + x * Math.log(lam) - Math.log(gammaFn(x + 1))); }
function poissonCdf(x, lam) {
  var s = 0;
  for (var i = 0; i <= Math.floor(x); i++) s += poissonPdf(i, lam);
  return s;
}
function openDistMenu() {
  showMenu('DISTRIBUTION', [
    { label: 'Normal P.D.', act: function () {
        promptChain([{ key: 'x', label: 'x?', value: 0 }, { key: 's', label: 'σ?', value: 1 }, { key: 'm', label: 'μ?', value: 0 }],
          function (v) { showValuePanel('Normal P.D.', ['<b>' + fmtNum(normPdf(v.x, v.m, v.s)) + '</b>']); });
      } },
    { label: 'Normal C.D.', act: function () {
        promptChain([{ key: 'l', label: 'lower?', value: -1 }, { key: 'u', label: 'upper?', value: 1 },
                     { key: 's', label: 'σ?', value: 1 }, { key: 'm', label: 'μ?', value: 0 }],
          function (v) { showValuePanel('Normal C.D.', ['<b>' + fmtNum(normCdf(v.u, v.m, v.s) - normCdf(v.l, v.m, v.s)) + '</b>']); });
      } },
    { label: 'Inverse Normal', act: function () {
        promptChain([{ key: 'p', label: 'area p?', value: 0.5 }, { key: 's', label: 'σ?', value: 1 }, { key: 'm', label: 'μ?', value: 0 }],
          function (v) { showValuePanel('Inverse Normal', ['<b>' + fmtNum(invNorm(v.p, v.m, v.s)) + '</b>']); });
      } },
    { label: 'Binomial P.D.', act: function () {
        promptChain([{ key: 'x', label: 'x?', value: 3 }, { key: 'n', label: 'n?', value: 10 }, { key: 'p', label: 'p?', value: 0.5 }],
          function (v) { showValuePanel('Binomial P.D.', ['<b>' + fmtNum(binomPdf(Math.round(v.x), Math.round(v.n), v.p)) + '</b>']); });
      } },
    { label: 'Binomial C.D.', act: function () {
        promptChain([{ key: 'x', label: 'x?', value: 3 }, { key: 'n', label: 'n?', value: 10 }, { key: 'p', label: 'p?', value: 0.5 }],
          function (v) { showValuePanel('Binomial C.D.', ['<b>' + fmtNum(binomCdf(Math.round(v.x), Math.round(v.n), v.p)) + '</b>']); });
      } },
    { label: 'Poisson P.D.', act: function () {
        promptChain([{ key: 'x', label: 'x?', value: 3 }, { key: 'l', label: 'λ?', value: 2 }],
          function (v) { showValuePanel('Poisson P.D.', ['<b>' + fmtNum(poissonPdf(Math.round(v.x), v.l)) + '</b>']); });
      } },
    { label: 'Poisson C.D.', act: function () {
        promptChain([{ key: 'x', label: 'x?', value: 3 }, { key: 'l', label: 'λ?', value: 2 }],
          function (v) { showValuePanel('Poisson C.D.', ['<b>' + fmtNum(poissonCdf(Math.round(v.x), v.l)) + '</b>']); });
      } }
  ]);
}

/* ------------------------------------------------------------------ *
 * 12.8  INEQUALITY  (quadratic / cubic)
 * ------------------------------------------------------------------ */
function openIneqMode() {
  showMenu('INEQUALITY', [
    { label: 'aX² + bX + c  (quadratic)', act: function () { ineqPanel(2); } },
    { label: 'aX³ + bX² + cX + d  (cubic)', act: function () { ineqPanel(3); } }
  ]);
}
function ineqPanel(deg) {
  state.editor = { kind: 'ineq' };
  var p = openEditor('INEQ  degree ' + deg, 'AC = exit');
  var labels = ['a', 'b', 'c', 'd'];
  var t = el('table', 'ed-table');
  var hr = el('tr'), tr = el('tr'), inputs = [];
  for (var i = 0; i <= deg; i++) {
    hr.appendChild(el('th', null, labels[i]));
    var td = el('td');
    inputs.push(edInput(td, i === 0 ? 1 : (i === deg ? -1 : 0)));
    tr.appendChild(td);
  }
  t.appendChild(hr); t.appendChild(tr);
  p.body.appendChild(t);
  [['> 0', 'gt'], ['≥ 0', 'ge'], ['< 0', 'lt'], ['≤ 0', 'le']].forEach(function (op) {
    edButton(p.foot, op[0], function () { solveIneq(deg, inputs, op[1]); }, op[1] === 'gt');
  });
}
function signAt(co, deg, x) {
  var v = 0;
  for (var i = 0; i <= deg; i++) v += co[i] * Math.pow(x, deg - i);
  return v;
}
function solveIneq(deg, inputs, mode) {
  var co = inputs.map(function (i) { return parseInputNumber(i.value) || 0; });
  var rows;
  try {
    var roots;
    if (deg === 2) roots = quadRoots(co[0], co[1], co[2]);
    else roots = cubicRoots(co[0], co[1], co[2], co[3]);
    var real = roots.filter(function (r) { return Math.abs(r.im) < 1e-9; }).map(function (r) { return r.re; })
                    .sort(function (a, b) { return a - b; });
    var uniq = [];
    real.forEach(function (r) { if (!uniq.length || Math.abs(r - uniq[uniq.length - 1]) > 1e-9) uniq.push(r); });
    var pts = [];
    if (uniq.length) {
      pts.push(uniq[0] - 1);
      uniq.forEach(function (r) { pts.push(r); });
      pts.push(uniq[uniq.length - 1] + 1);
      for (var i = 0; i < uniq.length - 1; i++) pts.push((uniq[i] + uniq[i + 1]) / 2);
      pts.sort(function (a, b) { return a - b; });
    } else {
      pts = [0];
    }
    var intervals = [];
    var tested = [];
    for (var k = 0; k < pts.length; k++) {
      var x = pts[k];
      if (tested.some(function (t) { return Math.abs(t - x) < 1e-9; })) continue;
      tested.push(x);
      var v = signAt(co, deg, x);
      var ok = mode === 'gt' ? v > 1e-12 : mode === 'ge' ? v >= -1e-12 : mode === 'lt' ? v < -1e-12 : v <= 1e-12;
      if (ok) intervals.push(x);
    }
    if (!intervals.length) rows = ['<b>No solution</b>'];
    else if (intervals.length === 1 && Math.abs(deg % 2) === 1 && intervals.length && uniq.length === 0) {
      rows = ['<b>All real X</b>'];
    } else {
      // build readable interval notation from the accepted sample points
      var bounds = [-Infinity].concat(uniq, [Infinity]);
      var out = [];
      for (var s = 0; s < bounds.length - 1; s++) {
        var lo = bounds[s], hi = bounds[s + 1];
        var mid = (isFinite(lo) && isFinite(hi)) ? (lo + hi) / 2 : (isFinite(lo) ? lo + 1 : hi - 1);
        var v2 = signAt(co, deg, mid);
        var ok2 = mode === 'gt' ? v2 > 1e-12 : mode === 'ge' ? v2 >= -1e-12 : mode === 'lt' ? v2 < -1e-12 : v2 <= 1e-12;
        if (!ok2) continue;
        var txt = (isFinite(lo) ? fmtNum(lo) : '−∞') + ' < X < ' + (isFinite(hi) ? fmtNum(hi) : '∞');
        out.push(txt);
      }
      if (!out.length) out = ['No solution'];
      rows = out.map(function (r) { return '<b>' + r + '</b>'; });
      rows.push('roots: ' + (uniq.length ? uniq.map(fmtNum).join(' , ') : 'none (real)'));
    }
  } catch (e) {
    rows = ['<b>' + (e.message || 'Math ERROR') + '</b>'];
  }
  showValuePanel('INEQ result', rows);
}

/* ------------------------------------------------------------------ *
 * 12.9  VERIFY  (is LHS = RHS an identity?)
 * ------------------------------------------------------------------ */
function openVerifMode() {
  state.editor = { kind: 'verif' };
  var p = openEditor('VERIFY  LHS = RHS ?', 'AC = exit');
  var t = el('table', 'ed-table');
  var mk = function (label, val) {
    var tr = el('tr');
    tr.appendChild(el('th', null, label));
    var td = el('td');
    var i = edInput(td, val, true);
    tr.appendChild(td);
    t.appendChild(tr);
    return i;
  };
  var lhs = mk('LHS', 'sin(X)²+cos(X)²');
  var rhs = mk('RHS', '1');
  p.body.appendChild(t);
  edButton(p.foot, 'VERIFY', function () {
    var vars = ['X', 'Y', 'A', 'B', 'C'];
    var used = [];
    var lt = tokenizeString(lhs.value), rt = tokenizeString(rhs.value);
    vars.forEach(function (v) {
      if (varsUsed(lt).indexOf(v) >= 0 || varsUsed(rt).indexOf(v) >= 0) used.push(v);
    });
    if (!used.length) used = ['X'];
    var worst = 0, sample = null, ok = true;
    for (var trial = 0; trial < 60; trial++) {
      var vals = {};
      used.forEach(function (v) { vals[v] = (Math.random() * 20 - 10); });
      var a, b;
      try { a = evalString(lhs.value, vals); b = evalString(rhs.value, vals); }
      catch (e) { continue; }
      if (!isNum(a) || !isNum(b)) continue;
      var diff = cabs(csub(a, b));
      var scale = Math.max(1, cabs(a), cabs(b));
      if (diff / scale > 1e-7) {
        ok = false;
        if (diff / scale > worst) {
          worst = diff / scale;
          sample = used.map(function (v) { return v + '=' + fmtNum(vals[v]); }).join(', ') +
                   '  →  ' + fmtComplex(a) + ' ≠ ' + fmtComplex(b);
        }
      }
    }
    showValuePanel('VERIFY', ok
      ? ['<b>TRUE</b> — equal at all ' + 60 + ' random test points.']
      : ['<b>FALSE</b> — not an identity.', sample || '']);
  }, true);
  edButton(p.foot, 'Example', function () { lhs.value = 'sin(X)²+cos(X)²'; rhs.value = '1'; });
}
/* =========================================================================
   13. FINAL WIRING: extra functions, keyboard, history, startup
   ========================================================================= */

/* --- Identity matrix (used by MATRIX mode) ---------------------------- */
FNS['ident'] = {
  n: 1, f: function (a) {
    var n = clamp(Math.round(a[0].re), 1, 10), d = [], i;
    for (i = 0; i < n * n; i++) d.push(i % (n + 1) === 0 ? C(1, 0) : C(0, 0));
    return Mat(n, n, d);
  }
};
/* --- friendly uppercase aliases (used when formulas are typed by hand) -- */
FNS['Abs'] = FNS['abs']; FNS['Re'] = FNS['re']; FNS['Im'] = FNS['im'];
FNS['Conjg'] = FNS['conjg']; FNS['SOLVE'] = FNS['solve'];
/* --- r∠θ  (magnitude + angle -> complex) ------------------------------ */
FNS['rangle'] = {
  n: 2, f: function (a) {
    var r = cabs(a[0]), th = toRad(a[1]).re;
    return C(r * Math.cos(th), r * Math.sin(th));
  }
};
/* --- BASE-N values are BigInt, teach the formatter about them ---------- */
var _valueToString = valueToString;
valueToString = function (v) {
  if (typeof v === 'bigint') return baseLabel(v);
  return _valueToString(v);
};
/* --- keep the SHIFT / ALPHA / hyp keycaps lit ------------------------- */
var _render = render;
render = function () { _render(); updateArmedKeys(); };

/* ------------------------------------------------------------------ *
 * HISTORY
 * ------------------------------------------------------------------ */
function renderHistory() {
  var list = $('histList');
  list.innerHTML = '';
  if (!state.history.length) {
    list.appendChild(el('div', 'hist-empty', 'No calculations yet'));
    return;
  }
  state.history.forEach(function (h, i) {
    var it = el('div', 'hist-item');
    it.appendChild(el('div', 'he', h.e));
    it.appendChild(el('div', 'hr', '= ' + h.r));
    it.addEventListener('click', function () { recallHistory(i); });
    list.appendChild(it);
  });
}
function recallHistory(i) {
  var h = state.history[i];
  if (!h) return;
  try { state.tokens = tokenizeString(h.e); }
  catch (e) { state.tokens = []; }
  state.justEquals = false; state.error = false;
  state.result = null; state.resultForms = [];
  render();
}

/* ------------------------------------------------------------------ *
 * KEYBOARD SUPPORT
 * ------------------------------------------------------------------ */
var KEY_IDS = {
  '0': '0', '1': '1', '2': '2', '3': '3', '4': '4', '5': '5', '6': '6', '7': '7', '8': '8', '9': '9',
  '.': 'dot', '+': 'plus', '-': 'minus', '*': 'mul', '/': 'div', '^': 'pow',
  '(': 'lp', ')': 'rp', '=': 'eq', 'Enter': 'eq', 'Backspace': 'del', 'Delete': 'del',
  'Escape': 'ac', 'ArrowUp': 'up', 'ArrowDown': 'down'
};

function handleKeyDown(e) {
  // never steal keys from the input boxes inside the mode editors
  if (e.target && (e.target.tagName === 'INPUT' || e.target.tagName === 'SELECT')) return;
  var k = e.key;

  // history recall with the arrow keys (only when no menu is open)
  if (!state.menu && !state.prompt && !state.editor) {
    if (k === 'ArrowUp' || k === 'ArrowDown') {
      e.preventDefault();
      if (!state.history.length) return;
      if (k === 'ArrowUp') state.histIndex = Math.min(state.histIndex + 1, state.history.length - 1);
      else state.histIndex = Math.max(state.histIndex - 1, -1);
      if (state.histIndex < 0) { state.tokens = []; }
      else recallHistory(state.histIndex);
      return;
    }
  }

  if (KEY_IDS[k] !== undefined) {
    e.preventDefault();
    pressKeyById(KEY_IDS[k]);
    return;
  }

  if (k === '!') { e.preventDefault(); insertPost('!'); return; }
  if (k === '%') { e.preventDefault(); insertPost('%'); return; }
  if (k === ',') { e.preventDefault(); state.tokens.push(tok('comma')); render(); return; }
  if (k === ' ') { e.preventDefault(); return; }

  if (k.length === 1 && /[a-zA-Z]/.test(k)) {
    e.preventDefault();
    switch (k) {
      case 's': insTrig('sin'); return;
      case 'S': insertFn('asin', 'sin⁻¹('); return;
      case 'c': insTrig('cos'); return;
      case 'C': insertFn('acos', 'cos⁻¹('); return;
      case 't': insTrig('tan'); return;
      case 'T': insertFn('atan', 'tan⁻¹('); return;
      case 'l': insertFn('log', 'log('); return;
      case 'L': insertFn('pow10', '10^('); return;
      case 'n': insertFn('ln', 'ln('); return;
      case 'N': insertFn('exp', 'e^('); return;
      case 'r': insertFn('sqrt', '√('); return;
      case 'R': insertFn('cbrt', '³√('); return;
      case 'q': insertPost('²'); return;
      case 'p': insertConst('π'); return;
      case 'P': insertConst('π'); return;
      case 'e': insertExp(); return;
      case 'E': insertConst('e'); return;
      case 'a': insertAns(); return;
      case 'A': insertVar('A'); return;
      case 'i': insertI(); return;
      case 'h': toggleHyp(); return;
      case 'B': insertVar('B'); return;
      case 'D': insertVar('D'); return;
      case 'F': insertVar('F'); return;
      case 'X': insertVar('X'); return;
      case 'Y': insertVar('Y'); return;
      case 'M': insertVar('M'); return;
      case 'x': insertVar('X'); return;
      case 'y': insertVar('Y'); return;
      case 'm': insertVar('M'); return;
    }
  }
}

/* ------------------------------------------------------------------ *
 * STARTUP
 * ------------------------------------------------------------------ */
function init() {
  state.vars = { A: C(0, 0), B: C(0, 0), C: C(0, 0), D: C(0, 0), E: C(0, 0), F: C(0, 0), X: C(0, 0), Y: C(0, 0), M: C(0, 0) };
  state.memory = C(0, 0);
  state.ans = C(0, 0);
  state.preAns = C(0, 0);
  state.mats = { MatA: null, MatB: null, MatC: null };
  state.vcts = { VctA: null, VctB: null, VctC: null };
  state.stats = { two: false, x: [], y: [], reg: null, lastHTML: '' };

  buildIndicators();
  buildKeypad();
  renderHistory();

  $('histClear').addEventListener('click', function () {
    state.history = [];
    state.histIndex = -1;
    renderHistory();
  });
  document.addEventListener('keydown', handleKeyDown);

  render();
}

if (typeof document !== 'undefined') {
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init);
  else init();
}
