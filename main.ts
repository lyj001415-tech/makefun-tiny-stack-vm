import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// A stack VM for make.fun's tiny stack ISA, following the reference VM rule for rule:
// wrapping 32-bit arithmetic (Math.imul for MUL), signed and unsigned division kept apart,
// shift counts masked to 5 bits, every trap in its own exit code, and the step and output
// limits checked in the reference's order. Ends (halt, exit, trap) throw the exit code.
// Decode table: immediate length per opcode, -1 for an invalid opcode. Built once so the
// hot loop reads one entry instead of re-deriving the length and validity on every step.
const DT = new Int8Array(256).fill(-1);
for (let o = 0; o < 256; o++) {
  if (o < 8 || (o >= 0x10 && o <= 0x1e) || (o >= 0x20 && o <= 0x22) || (o >= 0x30 && o <= 0x34) || o === 0x40 || o === 0x41 || (o >= 0x50 && o <= 0x53))
    DT[o] = o === 1 ? 1 : o === 2 ? 4 : o >= 0x30 && o <= 0x33 ? 2 : 0;
}

function run(P, I) {
  const n = P.length;
  const D = new Int32Array(256);
  const C = new Int32Array(64);
  const M = new Int32Array(256);
  const B = new Uint8Array(65536);
  let sp = 0, cp = 0, pc = 0, steps = 0, ip = 0, ol = 0;
  try {
    for (;;) {
      if (steps === 1e6) throw 10;
      if (pc < 0 || pc >= n) throw 9;
      const op = P[pc];
      const imm = DT[op];
      if (imm < 0) throw 5;
      if (pc + imm >= n) throw 9;
      steps++;
      const nx = pc + 1 + imm;
      pc = nx;
      switch (op) {
        case 0x00:
          throw 0;
        case 0x01:
          if (sp === 256) throw 3;
          D[sp++] = (P[nx - 1] << 24) >> 24;
          break;
        case 0x02:
          if (sp === 256) throw 3;
          D[sp++] = P[nx - 4] | (P[nx - 3] << 8) | (P[nx - 2] << 16) | (P[nx - 1] << 24);
          break;
        case 0x03:
          if (sp < 1) throw 2;
          sp--;
          break;
        case 0x04:
          if (sp < 1) throw 2;
          if (sp === 256) throw 3;
          D[sp] = D[sp - 1];
          sp++;
          break;
        case 0x05: {
          if (sp < 2) throw 2;
          const t = D[sp - 1];
          D[sp - 1] = D[sp - 2];
          D[sp - 2] = t;
          break;
        }
        case 0x06:
          if (sp < 2) throw 2;
          if (sp === 256) throw 3;
          D[sp] = D[sp - 2];
          sp++;
          break;
        case 0x07: {
          if (sp < 3) throw 2;
          const t = D[sp - 3];
          D[sp - 3] = D[sp - 2];
          D[sp - 2] = D[sp - 1];
          D[sp - 1] = t;
          break;
        }
        case 0x17:
          if (sp < 1) throw 2;
          D[sp - 1] = -D[sp - 1];
          break;
        case 0x1b:
          if (sp < 1) throw 2;
          D[sp - 1] = ~D[sp - 1];
          break;
        case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
        case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
        case 0x20: case 0x21: case 0x22: {
          if (sp < 2) throw 2;
          const b = D[sp - 1];
          const a = D[sp - 2];
          let r;
          if (op === 0x10) r = a + b;
          else if (op === 0x11) r = a - b;
          else if (op === 0x12) r = Math.imul(a, b);
          else if (op === 0x13) { if (b === 0) throw 4; r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
          else if (op === 0x14) { if (b === 0) throw 4; r = b === -1 ? 0 : a % b; }
          else if (op === 0x15) { if (b === 0) throw 4; r = Math.floor((a >>> 0) / (b >>> 0)); }
          else if (op === 0x16) { if (b === 0) throw 4; r = (a >>> 0) % (b >>> 0); }
          else if (op === 0x18) r = a & b;
          else if (op === 0x19) r = a | b;
          else if (op === 0x1a) r = a ^ b;
          else if (op === 0x1c) r = a << (b & 31);
          else if (op === 0x1d) r = a >> (b & 31);
          else if (op === 0x1e) r = a >>> (b & 31);
          else if (op === 0x20) r = a === b ? 1 : 0;
          else if (op === 0x21) r = a < b ? 1 : 0;
          else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
          D[sp - 2] = r;
          sp--;
          break;
        }
        case 0x30: case 0x31: case 0x32: {
          const rel = ((P[nx - 2] | (P[nx - 1] << 8)) << 16) >> 16;
          if (op === 0x30) pc = nx + rel;
          else {
            if (sp < 1) throw 2;
            const v = D[--sp];
            if ((op === 0x31) === (v === 0)) pc = nx + rel;
          }
          break;
        }
        case 0x33:
          if (cp === 64) throw 7;
          C[cp++] = nx;
          pc = P[nx - 2] | (P[nx - 1] << 8);
          break;
        case 0x34:
          if (cp === 0) throw 8;
          pc = C[--cp];
          break;
        case 0x40: {
          if (sp < 1) throw 2;
          const a = D[sp - 1];
          if (a < 0 || a > 255) throw 6;
          D[sp - 1] = M[a];
          break;
        }
        case 0x41: {
          if (sp < 2) throw 2;
          const a = D[sp - 1];
          if (a < 0 || a > 255) throw 6;
          M[a] = D[sp - 2];
          sp -= 2;
          break;
        }
        case 0x50: {
          if (sp < 1) throw 2;
          const v = D[sp - 1];
          const neg = v < 0;
          const m = neg ? -v : v;
          let len = neg ? 1 : 0;
          let t = m;
          do { len++; t = Math.floor(t / 10); } while (t > 0);
          if (ol + len > 65536) throw 11;
          sp--;
          let j = ol + len;
          t = m;
          do { B[--j] = 48 + (t % 10); t = Math.floor(t / 10); } while (t > 0);
          if (neg) B[ol] = 45;
          ol += len;
          break;
        }
        case 0x51:
          if (sp < 1) throw 2;
          if (ol === 65536) throw 11;
          B[ol++] = D[--sp] & 255;
          break;
        case 0x52:
          if (sp === 256) throw 3;
          D[sp++] = ip < I.length ? I[ip++] : -1;
          break;
        case 0x53:
          if (sp < 1) throw 2;
          throw D[sp - 1] & 255;
      }
    }
  } catch (e) {
    return [B.subarray(0, ol), typeof e === 'number' ? e : 0];
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  let inp;
  try {
    inp = readFileSync(join(I, id, 'input.bin'));
  } catch {
    inp = new Uint8Array(0);
  }
  const [out, code] = run(readFileSync(join(I, id, 'program.bin')), inp);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), out);
  writeFileSync(join(O, id, 'exit.txt'), `${code}\n`);
}
