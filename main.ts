// Tiny stack VM for make.fun's ISA v1 (see kit program/generator/subject/ISA.md).
// Runs every /input/<id>/program.bin on /input/<id>/input.bin and writes
// /output/<id>/stdout.bin + /output/<id>/exit.txt. Node 22, stdlib only.
// Deterministic: no clock, no randomness, no environment-dependent behaviour.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const IN = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Runs one program on its input. Returns [stdout bytes, exit code 0-255].
function run(p, inp) {
  const n = p.length;
  const S = new Int32Array(256); // data stack
  let sp = 0;
  const C = new Int32Array(64); // call stack
  let cp = 0;
  const M = new Int32Array(256); // memory, zeroed
  const out = new Uint8Array(65536);
  let ol = 0, ip = 0, pc = 0, st = 0;
  const end = (e) => [out.subarray(0, ol), e];

  for (;;) {
    // 1. Step limit, checked before fetching (trap 10).
    if (st === 1000000) return end(10);
    // 2. pc outside the program (trap 9).
    if (pc < 0 || pc >= n) return end(9);
    const op = p[pc];
    // 3. Unknown opcode (trap 5). Valid: 00-07, 10-1E, 20-22, 30-34, 40-41, 50-53.
    const ok = op <= 7 || (op >= 0x10 && op <= 0x1e) || (op >= 0x20 && op <= 0x22) ||
      (op >= 0x30 && op <= 0x34) || (op >= 0x40 && op <= 0x41) || (op >= 0x50 && op <= 0x53);
    if (!ok) return end(5);
    // Immediate length: PUSH8=1, PUSH32=4, JMP/JZ/JNZ/CALL=2, else 0.
    const im = op === 1 ? 1 : op === 2 ? 4 : op >= 0x30 && op <= 0x33 ? 2 : 0;
    // 4. Immediate cut off by the end of the program (trap 9).
    if (pc + im >= n) return end(9);
    st++;
    const nx = pc + 1 + im; // address of the next instruction
    pc = nx;

    switch (op) {
      case 0x00: // HALT
        return end(0);
      case 0x01: // PUSH8: signed 8-bit, sign-extended
        if (sp > 255) return end(3);
        S[sp++] = (p[nx - 1] << 24) >> 24;
        break;
      case 0x02: // PUSH32: signed 32-bit, little-endian
        if (sp > 255) return end(3);
        S[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24);
        break;
      case 0x03: // POP
        if (sp < 1) return end(2);
        sp--;
        break;
      case 0x04: // DUP
        if (sp < 1) return end(2);
        if (sp > 255) return end(3);
        S[sp] = S[sp - 1];
        sp++;
        break;
      case 0x05: // SWAP
        if (sp < 2) return end(2);
        { const t = S[sp - 1]; S[sp - 1] = S[sp - 2]; S[sp - 2] = t; }
        break;
      case 0x06: // OVER
        if (sp < 2) return end(2);
        if (sp > 255) return end(3);
        S[sp] = S[sp - 2];
        sp++;
        break;
      case 0x07: // ROT: ( a b c -- b c a )
        if (sp < 3) return end(2);
        { const t = S[sp - 3]; S[sp - 3] = S[sp - 2]; S[sp - 2] = S[sp - 1]; S[sp - 1] = t; }
        break;
      case 0x17: // NEG
        if (sp < 1) return end(2);
        S[sp - 1] = -S[sp - 1] | 0;
        break;
      case 0x1b: // NOT
        if (sp < 1) return end(2);
        S[sp - 1] = ~S[sp - 1];
        break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: { // binary arithmetic / logic / compare
        if (sp < 2) return end(2);
        const b = S[sp - 1], a = S[sp - 2];
        let r;
        switch (op) {
          case 0x10: r = (a + b) | 0; break; // ADD, wraps
          case 0x11: r = (a - b) | 0; break; // SUB, wraps
          case 0x12: r = Math.imul(a, b); break; // MUL, low 32 bits
          case 0x13: // DIV, signed, truncates toward zero
            if (b === 0) return end(4);
            r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
            break;
          case 0x14: // MOD, sign of a
            if (b === 0) return end(4);
            r = b === -1 ? 0 : (a % b) | 0;
            break;
          case 0x15: // DIVU, unsigned
            if (b === 0) return end(4);
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
            break;
          case 0x16: // MODU, unsigned
            if (b === 0) return end(4);
            r = ((a >>> 0) % (b >>> 0)) | 0;
            break;
          case 0x18: r = a & b; break; // AND
          case 0x19: r = a | b; break; // OR
          case 0x1a: r = a ^ b; break; // XOR
          case 0x1c: r = a << (b & 31); break; // SHL, low 5 bits of count
          case 0x1d: r = a >> (b & 31); break; // SHR, arithmetic
          case 0x1e: r = (a >>> (b & 31)) | 0; break; // SHRU, logical
          case 0x20: r = a === b ? 1 : 0; break; // EQ
          case 0x21: r = a < b ? 1 : 0; break; // LT, signed
          default: r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU, unsigned
        }
        sp -= 2;
        S[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: { // JMP / JZ / JNZ: signed 16-bit offset from next
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = op === 0x30;
        if (op !== 0x30) {
          if (sp < 1) return end(2);
          const v = S[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = nx + rel;
        break;
      }
      case 0x33: // CALL: unsigned 16-bit target
        if (cp === 64) return end(7);
        C[cp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 0x34: // RET
        if (cp === 0) return end(8);
        pc = C[--cp];
        break;
      case 0x40: { // LOAD
        if (sp < 1) return end(2);
        const a = S[sp - 1];
        if (a < 0 || a > 255) return end(6);
        S[sp - 1] = M[a];
        break;
      }
      case 0x41: { // STORE: ( v addr -- )
        if (sp < 2) return end(2);
        const a = S[sp - 1];
        if (a < 0 || a > 255) return end(6);
        M[a] = S[sp - 2];
        sp -= 2;
        break;
      }
      case 0x50: { // PRINT: decimal ASCII, no newline
        if (sp < 1) return end(2);
        const s = String(S[sp - 1]);
        if (ol + s.length > 65536) return end(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[ol++] = s.charCodeAt(i);
        break;
      }
      case 0x51: // PUTC: one byte, low 8 bits
        if (sp < 1) return end(2);
        if (ol + 1 > 65536) return end(11);
        out[ol++] = S[--sp] & 255;
        break;
      case 0x52: // IN: next input byte, -1 when used up
        if (sp > 255) return end(3);
        S[sp++] = ip < inp.length ? inp[ip++] : -1;
        break;
      default: // 0x53 EXIT: code is the low byte
        if (sp < 1) return end(2);
        return end(S[--sp] & 255);
    }
  }
}

for (const id of readdirSync(IN).sort()) {
  const [stdout, exit] = run(
    readFileSync(join(IN, id, 'program.bin')),
    readFileSync(join(IN, id, 'input.bin')),
  );
  mkdirSync(join(OUT, id), { recursive: true });
  writeFileSync(join(OUT, id, 'stdout.bin'), stdout);
  writeFileSync(join(OUT, id, 'exit.txt'), exit + '\n');
}
