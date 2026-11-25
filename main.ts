// Tiny stack VM: a faithful interpreter of make.fun's tiny stack ISA v1.
// Reads every instance under $MAKEFUN_INPUT_DIR (default /input) and writes
// /output/<id>/stdout.bin + exit.txt. Node 22, no dependencies.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

function run(p: Uint8Array, inp: Uint8Array): { out: Uint8Array; code: number } {
  const D = new Int32Array(256); // data stack
  const C = new Int32Array(64); // call stack (return addresses)
  const M = new Int32Array(256); // memory words
  const out = new Uint8Array(65536);
  let sp = 0, csp = 0, pc = 0, steps = 0, olen = 0, ipos = 0;
  const done = (code: number) => ({ out: out.slice(0, olen), code });
  for (;;) {
    if (steps === 1_000_000) return done(10);
    if (pc < 0 || pc >= p.length) return done(9);
    const op = p[pc];
    // immediate length and stack effect per opcode
    let imm = 0, pops = 0, pushes = 0;
    if (op === 0x01) { imm = 1; pushes = 1; }
    else if (op === 0x02) { imm = 4; pushes = 1; }
    else if (op === 0x03) pops = 1;
    else if (op === 0x04) { pops = 1; pushes = 2; }
    else if (op === 0x05 || op === 0x06) { pops = 2; pushes = op === 0x05 ? 2 : 3; }
    else if (op === 0x07) { pops = 3; pushes = 3; }
    else if (op >= 0x10 && op <= 0x22) { pops = op === 0x17 || op === 0x1b ? 1 : 2; pushes = 1; }
    else if (op === 0x30) imm = 2;
    else if (op === 0x31 || op === 0x32) { imm = 2; pops = 1; }
    else if (op === 0x33) imm = 2;
    else if (op === 0x40) { pops = 1; pushes = 1; }
    else if (op === 0x41) pops = 2;
    else if (op === 0x50 || op === 0x51 || op === 0x53) pops = 1;
    else if (op === 0x52) pushes = 1;
    else if (op !== 0x00 && op !== 0x34) return done(5); // unknown opcode
    if (pc + imm >= p.length) return done(9); // immediate cut off by the end
    steps++;
    const next = pc + 1 + imm;
    if (sp < pops) return done(2);
    if (sp - pops + pushes > 256) return done(3);
    pc = next;
    switch (op) {
      case 0x00: return done(0); // HALT
      case 0x01: D[sp++] = (p[next - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 0x02: D[sp++] = p[next - 4] | (p[next - 3] << 8) | (p[next - 2] << 16) | (p[next - 1] << 24); break; // PUSH32
      case 0x03: sp--; break; // POP
      case 0x04: D[sp] = D[sp - 1]; sp++; break; // DUP
      case 0x05: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; } // SWAP
      case 0x06: D[sp] = D[sp - 2]; sp++; break; // OVER
      case 0x07: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; } // ROT
      case 0x17: D[sp - 1] = -D[sp - 1] | 0; break; // NEG
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break; // NOT
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = D[sp - 1], a = D[sp - 2];
        let r: number;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) { if (b === 0) return done(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
        else if (op === 0x14) { if (b === 0) return done(4); r = b === -1 ? 0 : (a % b) | 0; }
        else if (op === 0x15) { if (b === 0) return done(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
        else if (op === 0x16) { if (b === 0) return done(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
        else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU
        sp -= 2; D[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: { // JMP / JZ / JNZ
        const rel = ((p[next - 2] | (p[next - 1] << 8)) << 16) >> 16;
        const take = op === 0x30 || (op === 0x31) === (D[--sp] === 0);
        if (take) pc = next + rel;
        break;
      }
      case 0x33: // CALL
        if (csp === 64) return done(7);
        C[csp++] = next;
        pc = p[next - 2] | (p[next - 1] << 8);
        break;
      case 0x34: // RET
        if (csp === 0) return done(8);
        pc = C[--csp];
        break;
      case 0x40: { // LOAD
        const addr = D[sp - 1];
        if (addr < 0 || addr >= 256) return done(6);
        D[sp - 1] = M[addr];
        break;
      }
      case 0x41: { // STORE
        const addr = D[sp - 1], v = D[sp - 2];
        if (addr < 0 || addr >= 256) return done(6);
        sp -= 2; M[addr] = v;
        break;
      }
      case 0x50: { // PRINT
        const s = String(D[sp - 1]);
        if (olen + s.length > 65536) return done(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        break;
      }
      case 0x51: // PUTC
        if (olen + 1 > 65536) return done(11);
        out[olen++] = D[--sp] & 255;
        break;
      case 0x52: D[sp++] = ipos < inp.length ? inp[ipos++] : -1; break; // IN
      case 0x53: return done(D[--sp] & 255); // EXIT
    }
  }
}

for (const d of readdirSync(I, { withFileTypes: true }).sort((a, b) => (a.name < b.name ? -1 : 1))) {
  if (!d.isDirectory()) continue; // answer only instance directories
  const id = d.name;
  const r = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), new Uint8Array(readFileSync(join(I, id, 'input.bin'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
