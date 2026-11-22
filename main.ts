// Tiny stack VM for make.fun's tiny-stack ISA v1, written from ISA.md and
// vm.mjs (the reference). One run answers a whole set: per /input/<id>/
// program.bin + input.bin it writes /output/<id>/stdout.bin and exit.txt.
// 32-bit wrapping integers; 256-value data stack; 64-deep call stack;
// 256 words of memory; a trap ends the program at once with its own exit
// code, keeping the output written before it. Node 22, no dependencies.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const MIN = -2147483648;
const enc = new TextEncoder();
// opcode -> [immediate bytes, pops, pushes]; an unlisted byte is trap 5.
const META = {
  0x00: [0, 0, 0], 0x01: [1, 0, 1], 0x02: [4, 0, 1], 0x03: [0, 1, 0],
  0x04: [0, 1, 2], 0x05: [0, 2, 2], 0x06: [0, 2, 3], 0x07: [0, 3, 3],
  0x10: [0, 2, 1], 0x11: [0, 2, 1], 0x12: [0, 2, 1], 0x13: [0, 2, 1],
  0x14: [0, 2, 1], 0x15: [0, 2, 1], 0x16: [0, 2, 1], 0x17: [0, 1, 1],
  0x18: [0, 2, 1], 0x19: [0, 2, 1], 0x1a: [0, 2, 1], 0x1b: [0, 1, 1],
  0x1c: [0, 2, 1], 0x1d: [0, 2, 1], 0x1e: [0, 2, 1], 0x20: [0, 2, 1],
  0x21: [0, 2, 1], 0x22: [0, 2, 1], 0x30: [2, 0, 0], 0x31: [2, 1, 0],
  0x32: [2, 1, 0], 0x33: [2, 0, 0], 0x34: [0, 0, 0], 0x40: [0, 1, 1],
  0x41: [0, 2, 0], 0x50: [0, 1, 0], 0x51: [0, 1, 0], 0x52: [0, 0, 1],
  0x53: [0, 1, 0],
};
// Two-operand arithmetic/logic: throws the trap code on division by zero.
const BIN = {
  0x10: (a, b) => (a + b) | 0,
  0x11: (a, b) => (a - b) | 0,
  0x12: Math.imul,
  0x13: (a, b) => { if (!b) throw 4; return a === MIN && b === -1 ? a : (a / b) | 0; },
  0x14: (a, b) => { if (!b) throw 4; return b === -1 ? 0 : (a % b) | 0; },
  0x15: (a, b) => { if (!b) throw 4; return Math.floor((a >>> 0) / (b >>> 0)) | 0; },
  0x16: (a, b) => { if (!b) throw 4; return ((a >>> 0) % (b >>> 0)) | 0; },
  0x18: (a, b) => a & b,
  0x19: (a, b) => a | b,
  0x1a: (a, b) => a ^ b,
  0x1c: (a, b) => a << (b & 31),
  0x1d: (a, b) => a >> (b & 31),
  0x1e: (a, b) => (a >>> (b & 31)) | 0,
  0x20: (a, b) => (a === b ? 1 : 0),
  0x21: (a, b) => (a < b ? 1 : 0),
  0x22: (a, b) => ((a >>> 0) < (b >>> 0) ? 1 : 0),
};

function run(p, inp) {
  const n = p.length;
  const s = new Int32Array(256); let sp = 0;
  const c = new Int32Array(64); let cp = 0;
  const m = new Int32Array(256);
  const o = new Uint8Array(65536); let ol = 0;
  let ip = 0, pc = 0, steps = 0;
  const done = (code) => ({ out: o.slice(0, ol), exit: code });
  try {
    for (;;) {
      if (steps === 1000000) throw 10;
      if (pc < 0 || pc >= n) throw 9;
      const meta = META[p[pc]];
      if (!meta) throw 5;
      const [imm, pops, pushes] = meta;
      if (pc + imm >= n) throw 9;
      steps++;
      const nx = pc + 1 + imm;
      if (sp < pops) throw 2;
      if (sp - pops + pushes > 256) throw 3;
      const op = p[pc];
      pc = nx;
      if (op === 0x00) return done(0);
      if (op === 0x01) { s[sp++] = (p[nx - 1] << 24) >> 24; continue; }
      if (op === 0x02) { s[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); continue; }
      if (op === 0x03) { sp--; continue; }
      if (op === 0x04) { s[sp] = s[sp - 1]; sp++; continue; }
      if (op === 0x05) { const t = s[sp - 1]; s[sp - 1] = s[sp - 2]; s[sp - 2] = t; continue; }
      if (op === 0x06) { s[sp] = s[sp - 2]; sp++; continue; }
      if (op === 0x07) { const a = s[sp - 3]; s[sp - 3] = s[sp - 2]; s[sp - 2] = s[sp - 1]; s[sp - 1] = a; continue; }
      if (op === 0x17) { s[sp - 1] = -s[sp - 1] | 0; continue; }
      if (op === 0x1b) { s[sp - 1] = ~s[sp - 1]; continue; }
      if (BIN[op]) { const b = s[sp - 1], a = s[sp - 2]; sp -= 2; s[sp++] = BIN[op](a, b); continue; }
      if (op === 0x30 || op === 0x31 || op === 0x32) {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) { const v = s[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = nx + rel;
        continue;
      }
      if (op === 0x33) {
        if (cp === 64) throw 7;
        c[cp++] = nx; pc = p[nx - 2] | (p[nx - 1] << 8); continue;
      }
      if (op === 0x34) { if (!cp) throw 8; pc = c[--cp]; continue; }
      if (op === 0x40) {
        const a = s[sp - 1];
        if (a < 0 || a > 255) throw 6;
        s[sp - 1] = m[a]; continue;
      }
      if (op === 0x41) {
        const a = s[sp - 1], v = s[sp - 2];
        if (a < 0 || a > 255) throw 6;
        sp -= 2; m[a] = v; continue;
      }
      if (op === 0x50) {
        const b = enc.encode(String(s[sp - 1]));
        if (ol + b.length > 65536) throw 11;
        sp--; o.set(b, ol); ol += b.length; continue;
      }
      if (op === 0x51) { if (ol + 1 > 65536) throw 11; o[ol++] = s[--sp] & 255; continue; }
      if (op === 0x52) { s[sp++] = ip < inp.length ? inp[ip++] : -1; continue; }
      if (op === 0x53) return done(s[--sp] & 255);
    }
  } catch (e) {
    if (typeof e === 'number') return done(e);
    throw e;
  }
}

for (const id of readdirSync(I).sort()) {
  const { out, exit } = run(
    readFileSync(join(I, id, 'program.bin')),
    readFileSync(join(I, id, 'input.bin')),
  );
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), out);
  writeFileSync(join(O, id, 'exit.txt'), exit + '\n');
}
