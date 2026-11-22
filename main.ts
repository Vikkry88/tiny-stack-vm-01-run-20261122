import { mkdirSync, readdirSync, readFileSync, statSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

function meta(op) {
  if (op === 0x00) return [0, 0, 0];
  if (op === 0x01) return [1, 0, 1];
  if (op === 0x02) return [4, 0, 1];
  if (op === 0x03) return [0, 1, 0];
  if (op === 0x04) return [0, 1, 2];
  if (op === 0x05) return [0, 2, 2];
  if (op === 0x06) return [0, 2, 3];
  if (op === 0x07) return [0, 3, 3];
  if (op >= 0x10 && op <= 0x16) return [0, 2, 1];
  if (op === 0x17) return [0, 1, 1];
  if (op >= 0x18 && op <= 0x1a) return [0, 2, 1];
  if (op === 0x1b) return [0, 1, 1];
  if (op >= 0x1c && op <= 0x1e) return [0, 2, 1];
  if (op >= 0x20 && op <= 0x22) return [0, 2, 1];
  if (op === 0x30) return [2, 0, 0];
  if (op === 0x31 || op === 0x32) return [2, 1, 0];
  if (op === 0x33) return [2, 0, 0];
  if (op === 0x34) return [0, 0, 0];
  if (op === 0x40) return [0, 1, 1];
  if (op === 0x41) return [0, 2, 0];
  if (op === 0x50 || op === 0x51) return [0, 1, 0];
  if (op === 0x52) return [0, 0, 1];
  if (op === 0x53) return [0, 1, 0];
  return null;
}

function run(prog, inp) {
  const st = new Int32Array(256);
  const cs = new Int32Array(64);
  const mem = new Int32Array(256);
  const out = Buffer.alloc(65536);
  let sp = 0, csp = 0, pc = 0, steps = 0, ip = 0, ol = 0;
  const done = (code) => ({ out: Buffer.from(out.subarray(0, ol)), exit: code });
  while (true) {
    if (steps >= 1000000) return done(10);
    if (pc < 0 || pc >= prog.length) return done(9);
    const op = prog[pc];
    const m = meta(op);
    if (m === null) return done(5);
    const imm = m[0], pops = m[1], pushes = m[2];
    if (pc + 1 + imm > prog.length) return done(9);
    if (sp < pops) return done(2);
    if (sp - pops + pushes > 256) return done(3);
    const nxt = pc + 1 + imm;
    if (op === 0x00) return done(0);
    if (op === 0x01) {
      const b = prog[pc + 1];
      st[sp++] = b < 128 ? b : b - 256;
      pc = nxt;
    } else if (op === 0x02) {
      st[sp++] = (prog[pc + 1] | (prog[pc + 2] << 8) | (prog[pc + 3] << 16) | (prog[pc + 4] << 24)) | 0;
      pc = nxt;
    } else if (op === 0x03) {
      sp--; pc = nxt;
    } else if (op === 0x04) {
      st[sp] = st[sp - 1]; sp++; pc = nxt;
    } else if (op === 0x05) {
      const t = st[sp - 1]; st[sp - 1] = st[sp - 2]; st[sp - 2] = t; pc = nxt;
    } else if (op === 0x06) {
      st[sp] = st[sp - 2]; sp++; pc = nxt;
    } else if (op === 0x07) {
      const a = st[sp - 3], b = st[sp - 2], c = st[sp - 1];
      st[sp - 3] = b; st[sp - 2] = c; st[sp - 1] = a; pc = nxt;
    } else if (op === 0x17) {
      st[sp - 1] = (-st[sp - 1]) | 0; pc = nxt;
    } else if (op === 0x1b) {
      st[sp - 1] = ~st[sp - 1]; pc = nxt;
    } else if ((op >= 0x10 && op <= 0x16) || (op >= 0x18 && op <= 0x1a) || (op >= 0x1c && op <= 0x1e) || (op >= 0x20 && op <= 0x22)) {
      const b = st[sp - 1], a = st[sp - 2];
      let r;
      if (op === 0x10) r = (a + b) | 0;
      else if (op === 0x11) r = (a - b) | 0;
      else if (op === 0x12) r = Math.imul(a, b);
      else if (op === 0x13) { if (b === 0) return done(4); r = ((a - (a % b)) / b) | 0; }
      else if (op === 0x14) { if (b === 0) return done(4); r = (a % b) | 0; }
      else if (op === 0x15) { if (b === 0) return done(4); const au = a >>> 0, bu = b >>> 0; r = ((au - (au % bu)) / bu) | 0; }
      else if (op === 0x16) { if (b === 0) return done(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
      else if (op === 0x18) r = a & b;
      else if (op === 0x19) r = a | b;
      else if (op === 0x1a) r = a ^ b;
      else if (op === 0x1c) r = (a << (b & 31)) | 0;
      else if (op === 0x1d) r = a >> (b & 31);
      else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
      else if (op === 0x20) r = a === b ? 1 : 0;
      else if (op === 0x21) r = a < b ? 1 : 0;
      else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
      sp--; st[sp - 1] = r | 0; pc = nxt;
    } else if (op === 0x30 || op === 0x31 || op === 0x32) {
      let off = prog[pc + 1] | (prog[pc + 2] << 8);
      if (off >= 32768) off -= 65536;
      if (op === 0x30) pc = nxt + off;
      else {
        const v = st[--sp];
        pc = (op === 0x31 ? v === 0 : v !== 0) ? nxt + off : nxt;
      }
    } else if (op === 0x33) {
      if (csp >= 64) return done(7);
      cs[csp++] = nxt;
      pc = prog[pc + 1] | (prog[pc + 2] << 8);
    } else if (op === 0x34) {
      if (csp === 0) return done(8);
      pc = cs[--csp];
    } else if (op === 0x40) {
      const ad = st[sp - 1];
      if (ad < 0 || ad > 255) return done(6);
      st[sp - 1] = mem[ad]; pc = nxt;
    } else if (op === 0x41) {
      const ad = st[sp - 1], v = st[sp - 2];
      if (ad < 0 || ad > 255) return done(6);
      mem[ad] = v; sp -= 2; pc = nxt;
    } else if (op === 0x50) {
      const v = st[sp - 1];
      const neg = v < 0;
      let u = neg ? -v : v;
      let len = neg ? 1 : 0;
      let t = u;
      do { len++; t = Math.floor(t / 10); } while (t > 0);
      if (ol + len > 65536) return done(11);
      sp--;
      let p = ol + len;
      do { out[--p] = 48 + (u % 10); u = Math.floor(u / 10); } while (u > 0);
      if (neg) out[--p] = 45;
      ol += len;
      pc = nxt;
    } else if (op === 0x51) {
      if (ol + 1 > 65536) return done(11);
      out[ol++] = st[--sp] & 255; pc = nxt;
    } else if (op === 0x52) {
      st[sp++] = ip < inp.length ? inp[ip++] : -1; pc = nxt;
    } else if (op === 0x53) {
      return done(st[sp - 1] & 255);
    } else {
      return done(5);
    }
    steps++;
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const dir = join(I, id);
  try { if (!statSync(dir).isDirectory()) continue; } catch { continue; }
  let prog, inp;
  try { prog = readFileSync(join(dir, 'program.bin')); } catch { prog = Buffer.alloc(0); }
  try { inp = readFileSync(join(dir, 'input.bin')); } catch { inp = Buffer.alloc(0); }
  const r = run(prog, inp);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), String(r.exit) + '\n');
}
