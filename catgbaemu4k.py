#!/usr/bin/env python3
"""
Cat GBA 0.1 (mewgba) — single-file GBA emulator (meow).

Everything lives in this file: ARM7TDMI CPU, GBA memory map, PPU (modes 3/4/5),
DMA/timer/IRQ stubs, retail ROM boot, and the Tkinter UI. Stdlib only (tkinter).

Run:
    python3 gbaemu4k.py
    python3 gbaemu4k.py /path/to/game.gba
"""
from __future__ import annotations

import struct
import sys
import textwrap
import time
import tkinter as tk
from pathlib import Path
from tkinter import filedialog, messagebox

# Nintendo logo at ROM offset 0x04 (156 bytes) — standard retail GBA cartridge header.
GBA_NINTENDO_LOGO = bytes([
    0x24, 0xFF, 0xAE, 0x51, 0x69, 0x9A, 0xA2, 0x21, 0x3D, 0x84, 0x82, 0x0A, 0x84, 0xE4, 0x09, 0xAD,
    0x11, 0x24, 0x8B, 0x98, 0xC0, 0x81, 0x7F, 0x21, 0xA3, 0x52, 0xBE, 0x19, 0x93, 0x09, 0xCE, 0x20,
    0x10, 0x46, 0x4A, 0x4A, 0xF8, 0x27, 0x31, 0xEC, 0x58, 0xC7, 0xE8, 0x33, 0x82, 0xE3, 0xCE, 0xBF,
    0x85, 0xF4, 0xDF, 0x94, 0xCE, 0x4B, 0x09, 0xC1, 0x94, 0x56, 0x8A, 0xC0, 0x13, 0x72, 0xA7, 0xFC,
    0x3F, 0x84, 0x5F, 0x95, 0x2C, 0xA3, 0x0D, 0xB5, 0x4E, 0x52, 0x39, 0xC5, 0x83, 0xC1, 0x6A, 0xB4,
    0x53, 0xF1, 0x17, 0xA8, 0xE9, 0xF7, 0x17, 0x68, 0x20, 0x9A, 0xD6, 0x28, 0x4E, 0xDA, 0xC4, 0x42,
    0x39, 0xC5, 0x3B, 0x6C, 0x4A, 0x2A, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
])

GBA_W, GBA_H = 240, 160
_FB_BYTES = GBA_W * GBA_H * 3
GBA_FRAME_CYCLES = 280896
CYCLES_PER_SCANLINE = 1232  # ~280896 / 228 scanlines per GBA frame
_CPU_BATCH = 256  # amortize Python loop overhead in step()

REG_DISPCNT = 0x04000000
REG_VCOUNT = 0x04000006
REG_KEYINPUT = 0x04000130
REG_IE = 0x04000200
REG_IF = 0x04000202
REG_IME = 0x04000208
REG_DMA0SAD = 0x040000B0
REG_TM0CNT_L = 0x04000100

CPSR_T = 1 << 5
FLAG_N = 1 << 31
FLAG_Z = 1 << 30


def _ror32(value: int, amount: int) -> int:
    amount &= 31
    value &= 0xFFFFFFFF
    if amount == 0:
        return value
    return ((value >> amount) | (value << (32 - amount))) & 0xFFFFFFFF


def _sign_extend(value: int, bits: int) -> int:
    sign = 1 << (bits - 1)
    return (value & (sign - 1)) - (value & sign)


class MewgbaCore:
    """mewgba — ARM7TDMI + GBA memory bus + PPU (modes 3/4/5), DMA, timers, IRQ, keypad."""

    def __init__(self) -> None:
        self.bios = bytearray(0x4000)
        self.ewram = bytearray(0x40000)
        self.iwram = bytearray(0x8000)
        self.io = bytearray(0x400)
        self.pal = bytearray(0x400)
        self.vram = bytearray(0x18000)
        self.oam = bytearray(0x400)
        self.rom = bytearray()
        self.sram = bytearray(0x10000)

        self.r = [0] * 16
        self.cpsr = 0x1F
        self.thumb = False
        self.halted = False
        self.cycles = 0
        self.frame_counter = 0
        self.scanline = 0
        self._line_cycles = 0
        self._fb_rgb = bytearray(_FB_BYTES)
        self._fb_seq = 0

        self.loaded = False
        self.booted = False
        self.title = b"NO ROM"
        self.game_code = b"----"
        self.maker = b"--"
        self.key_mask = 0x03FF
        self._rom_len = 0

        self.reset()

    def reset(self) -> None:
        self.r = [0] * 16
        self.r[13] = 0x03007F00
        self.r[15] = 0x08000000
        self.cpsr = 0x1F
        self.thumb = False
        self.halted = False
        self.cycles = 0
        self.frame_counter = 0
        self.scanline = 0
        self._line_cycles = 0
        self.loaded = False
        self.booted = False
        self.rom = bytearray()
        self._rom_len = 0
        self.ewram[:] = b"\x00" * len(self.ewram)
        self.iwram[:] = b"\x00" * len(self.iwram)
        self.io[:] = b"\x00" * len(self.io)
        self.pal[:] = b"\x00" * len(self.pal)
        self.vram[:] = b"\x00" * len(self.vram)
        self.oam[:] = b"\x00" * len(self.oam)
        self._sync_keys()
        self._render_frame_rgb()

    def _region(self, addr: int):
        addr &= 0x0FFFFFFF
        if addr < 0x00004000:
            return self.bios, addr & 0x3FFF
        if 0x02000000 <= addr <= 0x0203FFFF:
            return self.ewram, addr - 0x02000000
        if 0x03000000 <= addr <= 0x03007FFF:
            return self.iwram, addr - 0x03000000
        if 0x04000000 <= addr <= 0x040003FF:
            return self.io, addr - 0x04000000
        if 0x05000000 <= addr <= 0x050003FF:
            return self.pal, addr - 0x05000000
        if 0x06000000 <= addr <= 0x06017FFF:
            return self.vram, addr - 0x06000000
        if 0x07000000 <= addr <= 0x070003FF:
            return self.oam, addr - 0x07000000
        if 0x08000000 <= addr <= 0x0DFFFFFF:
            off = (addr - 0x08000000) % max(1, len(self.rom))
            return self.rom, off
        if 0x0E000000 <= addr <= 0x0E00FFFF:
            return self.sram, addr - 0x0E000000
        return self.io, 0

    def read8(self, addr: int) -> int:
        addr &= 0xFFFFFFFF
        if addr < 0x00004000:
            return 0
        if 0x02000000 <= addr < 0x02040000:
            return self.ewram[addr - 0x02000000]
        if 0x03000000 <= addr < 0x03008000:
            return self.iwram[addr - 0x03000000]
        if 0x04000000 <= addr < 0x04000400:
            off = addr - 0x04000000
            return self.io[off] if off < len(self.io) else 0
        if 0x05000000 <= addr < 0x05000400:
            return self.pal[addr - 0x05000000]
        if 0x06000000 <= addr < 0x06018000:
            return self.vram[addr - 0x06000000]
        if 0x07000000 <= addr < 0x07000400:
            return self.oam[addr - 0x07000000]
        if 0x08000000 <= addr < 0x0E000000:
            ln = self._rom_len
            if ln:
                return self.rom[(addr - 0x08000000) % ln]
            return 0
        if 0x0E000000 <= addr < 0x0E010000:
            return self.sram[addr - 0x0E000000]
        return 0

    def read16(self, addr: int) -> int:
        addr &= 0xFFFFFFFF
        a = addr & ~1
        if 0x03000000 <= a < 0x03008000:
            off = a - 0x03000000
            iw = self.iwram
            return iw[off] | (iw[off + 1] << 8)
        if 0x02000000 <= a < 0x02040000:
            off = a - 0x02000000
            e = self.ewram
            return e[off] | (e[off + 1] << 8)
        if 0x08000000 <= a < 0x0E000000:
            ln = self._rom_len
            if ln:
                off = (a - 0x08000000) % ln
                rom = self.rom
                return rom[off] | (rom[off + 1] << 8)
            return 0
        return self.read8(a) | (self.read8(a + 1) << 8)

    def read32(self, addr: int) -> int:
        addr &= 0xFFFFFFFF
        a = addr & ~3
        if 0x03000000 <= a < 0x03008000:
            off = a - 0x03000000
            iw = self.iwram
            return iw[off] | (iw[off + 1] << 8) | (iw[off + 2] << 16) | (iw[off + 3] << 24)
        if 0x02000000 <= a < 0x02040000:
            off = a - 0x02000000
            e = self.ewram
            return e[off] | (e[off + 1] << 8) | (e[off + 2] << 16) | (e[off + 3] << 24)
        if 0x08000000 <= a < 0x0E000000:
            ln = self._rom_len
            if ln:
                off = (a - 0x08000000) % ln
                rom = self.rom
                return rom[off] | (rom[off + 1] << 8) | (rom[off + 2] << 16) | (rom[off + 3] << 24)
            return 0
        return self.read16(a) | (self.read16(a + 2) << 16)

    def write8(self, addr: int, val: int) -> None:
        addr &= 0xFFFFFFFF
        if 0x04000000 <= addr <= 0x040003FF:
            off = addr - 0x04000000
            if off < len(self.io):
                self.io[off] = val & 0xFF
            return
        mem, off = self._region(addr)
        if mem is self.rom:
            return
        if off < len(mem):
            mem[off] = val & 0xFF

    def write16(self, addr: int, val: int) -> None:
        a = addr & 0xFFFFFFFE
        v = val & 0xFFFF
        b0, b1 = v & 0xFF, (v >> 8) & 0xFF
        if 0x02000000 <= a < 0x02040000:
            off = a - 0x02000000
            self.ewram[off] = b0
            self.ewram[off + 1] = b1
            return
        if 0x03000000 <= a < 0x03008000:
            off = a - 0x03000000
            self.iwram[off] = b0
            self.iwram[off + 1] = b1
            return
        if 0x04000000 <= a < 0x04000400:
            off = a - 0x04000000
            if off + 1 < len(self.io):
                self.io[off] = b0
                self.io[off + 1] = b1
            return
        self.write8(a, b0)
        self.write8(a + 1, b1)

    def write32(self, addr: int, val: int) -> None:
        self.write16(addr & ~3, val)
        self.write16(addr + 2, val >> 16)

    def _sync_keys(self) -> None:
        self.write16(REG_KEYINPUT, self.key_mask & 0x03FF)

    def set_nz(self, value: int) -> None:
        value &= 0xFFFFFFFF
        self.cpsr &= ~(FLAG_N | FLAG_Z)
        if value == 0:
            self.cpsr |= FLAG_Z
        if value & 0x80000000:
            self.cpsr |= FLAG_N

    def set_add_flags(self, a: int, b: int, result: int) -> None:
        self.set_nz(result)
        self.cpsr &= ~(1 << 29 | 1 << 28)
        if (a + b) > 0xFFFFFFFF:
            self.cpsr |= 1 << 29
        sa, sb, sr = (a >> 31) & 1, (b >> 31) & 1, (result >> 31) & 1
        if sa == sb and sa != sr:
            self.cpsr |= 1 << 28

    def set_sub_flags(self, a: int, b: int, result: int) -> None:
        self.set_nz(result)
        self.cpsr &= ~(1 << 29 | 1 << 28)
        if a >= b:
            self.cpsr |= 1 << 29
        sa, sb, sr = (a >> 31) & 1, (b >> 31) & 1, (result >> 31) & 1
        if sa != sb and sa != sr:
            self.cpsr |= 1 << 28

    def boot_rom(self, data: bytes) -> dict[str, object]:
        self.reset()
        self.rom = bytearray(data)
        self._rom_len = len(self.rom)
        self.loaded = self._rom_len > 0
        self.booted = self.loaded
        if not self.loaded:
            return self.get_rom_info()

        self.title = data[0xA0:0xAC].rstrip(b"\x00 ") or b"UNTITLED"
        self.game_code = data[0xAC:0xB0] if len(data) >= 0xB0 else b"----"
        self.maker = data[0xB0:0xB2] if len(data) >= 0xB2 else b"--"

        entry = struct.unpack_from("<I", data, 0xAC)[0] if len(data) >= 0xB0 else 0x08000000
        self.thumb = bool(entry & 1)
        self.r[15] = entry & 0xFFFFFFFE if self.thumb else entry & 0xFFFFFFFC
        self.cpsr = (self.cpsr | CPSR_T) if self.thumb else (self.cpsr & ~CPSR_T)
        self._sync_keys()
        self._render_frame_rgb()
        return self.get_rom_info()

    def load_rom(self, data: bytes) -> dict[str, object]:
        return self.boot_rom(data)

    def get_rom_info(self) -> dict[str, object]:
        return {
            "title": self.title.decode("ascii", "replace"),
            "game_code": self.game_code.decode("ascii", "replace"),
            "maker": self.maker.decode("ascii", "replace"),
            "rom_size": len(self.rom),
            "pc": int(self.r[15]),
            "cycles": int(self.cycles),
            "frame": int(self.frame_counter),
            "booted": bool(self.booted),
            "thumb": bool(self.thumb),
            "keys_released_mask": int(self.key_mask),
            "mode": "mewgba ARM7+PPU",
        }

    def set_key(self, key_name: str, pressed: bool) -> None:
        mapping = {
            "A": 0, "B": 1, "SELECT": 2, "START": 3, "RIGHT": 4, "LEFT": 5,
            "UP": 6, "DOWN": 7, "R": 8, "L": 9,
        }
        idx = mapping.get(key_name.upper())
        if idx is None:
            return
        if pressed:
            self.key_mask &= ~(1 << idx)
        else:
            self.key_mask |= 1 << idx
        self._sync_keys()

    @property
    def pc(self) -> int:
        return self.r[15]

    def step_cpu(self) -> int:
        if self.halted:
            return 4
        pc = self.r[15]
        if self.thumb:
            ln = self._rom_len
            if ln and 0x08000000 <= pc < 0x0E000000:
                off = (pc - 0x08000000) % ln
                rom = self.rom
                op = rom[off] | (rom[off + 1] << 8)
                self.r[15] = (pc + 2) & 0xFFFFFFFF
                return self._exec_thumb(op)
            op = self.read16(pc)
            self.r[15] = (pc + 2) & 0xFFFFFFFF
            return self._exec_thumb(op)
        ln = self._rom_len
        if ln and 0x08000000 <= pc < 0x0E000000:
            off = (pc - 0x08000000) % ln
            rom = self.rom
            op = rom[off] | (rom[off + 1] << 8) | (rom[off + 2] << 16) | (rom[off + 3] << 24)
            self.r[15] = (pc + 4) & 0xFFFFFFFF
            return self._exec_arm(op)
        op = self.read32(pc)
        self.r[15] = (pc + 4) & 0xFFFFFFFF
        return self._exec_arm(op)

    def _exec_arm(self, op: int) -> int:
        top = (op >> 26) & 0b11
        if (op >> 25) & 0b111 == 0b101:
            offset = op & 0x00FFFFFF
            if offset & 0x00800000:
                offset |= 0xFF000000
            offset = (offset << 2) & 0xFFFFFFFF
            if op & (1 << 24):
                self.r[14] = self.r[15]
            self.r[15] = (self.r[15] + offset) & 0xFFFFFFFF
            self.thumb = bool(self.r[15] & 1)
            if self.thumb:
                self.r[15] &= 0xFFFFFFFE
                self.cpsr |= CPSR_T
            else:
                self.r[15] &= 0xFFFFFFFC
                self.cpsr &= ~CPSR_T
            return 3
        if top == 0b01:
            rn, rd = (op >> 16) & 15, (op >> 12) & 15
            load, byte = bool(op & (1 << 20)), bool(op & (1 << 22))
            imm = op & 0xFFF
            addr = (self.r[rn] + imm) & 0xFFFFFFFF
            if load:
                self.r[rd] = self.read8(addr) if byte else self.read32(addr)
            elif byte:
                self.write8(addr, self.r[rd])
            else:
                self.write32(addr, self.r[rd])
            return 3
        if top == 0b00 and (op & 0x0FFFFFF0) == 0x012FFF10:
            rm = op & 0xF
            target = self.r[rm] & 0xFFFFFFFF
            if target & 1:
                self.thumb = True
                self.cpsr |= CPSR_T
                self.r[15] = target & 0xFFFFFFFE
            else:
                self.thumb = False
                self.cpsr &= ~CPSR_T
                self.r[15] = target & 0xFFFFFFFC
            return 3
        if top == 0b00:
            opcode, s = (op >> 21) & 15, bool(op & (1 << 20))
            rn, rd = (op >> 16) & 15, (op >> 12) & 15
            if op & (1 << 25):
                imm = op & 0xFF
                rot = ((op >> 8) & 15) * 2
                val = _ror32(imm, rot) if rot else imm
            else:
                shift = (op >> 7) & 0x1F
                stype = (op >> 5) & 3
                rs = (op >> 8) & 15
                val = self.r[op & 15]
                if stype == 0:
                    val, _ = (val, val >> shift) if shift else (val, 0)
                    val = _ror32(val, shift) if shift else val
                else:
                    val = self.r[rs]
            a = self.r[rn]
            result = None
            if opcode == 0x0:
                result = a & val
            elif opcode == 0x1:
                result = a ^ val
            elif opcode == 0x2:
                result = (a - val) & 0xFFFFFFFF
                self.set_sub_flags(a, val, result)
                if rd == 15 and not s:
                    return 1
            elif opcode == 0x4:
                result = (a + val) & 0xFFFFFFFF
            elif opcode == 0xA:
                result = (a - val) & 0xFFFFFFFF
                self.set_sub_flags(a, val, result)
                if rd == 15:
                    return 1
            elif opcode == 0xC:
                result = a | val
            elif opcode == 0xD:
                result = val
            if result is not None and opcode != 0xA:
                self.r[rd] = result
                if s:
                    self.set_nz(result)
            return 1
        return 1

    def _exec_thumb(self, op: int) -> int:
        pc = (self.r[15] - 2) & 0xFFFFFFFF
        if (op & 0xF800) == 0xE000:
            off = _sign_extend(op & 0x7FF, 11) << 1
            self.r[15] = (pc + 4 + off) & 0xFFFFFFFF
            return 3
        if (op & 0xF800) == 0x2000:
            rd, imm = (op >> 8) & 7, op & 0xFF
            kind = (op >> 11) & 3
            if kind == 0:
                self.r[rd] = imm
                self.set_nz(imm)
            elif kind == 1:
                self.set_sub_flags(self.r[rd], imm, (self.r[rd] - imm) & 0xFFFFFFFF)
            elif kind == 2:
                self.r[rd] = (self.r[rd] + imm) & 0xFFFFFFFF
                self.set_nz(self.r[rd])
            elif kind == 3:
                self.r[rd] = (self.r[rd] - imm) & 0xFFFFFFFF
                self.set_nz(self.r[rd])
            return 1
        if (op & 0xF800) == 0x1800:
            immediate = bool(op & 0x0400)
            subtract = bool(op & 0x0200)
            rn_or_imm = (op >> 6) & 7
            rs, rd = (op >> 3) & 7, op & 7
            right = rn_or_imm if immediate else self.r[rn_or_imm]
            if subtract:
                result = (self.r[rs] - right) & 0xFFFFFFFF
                self.set_sub_flags(self.r[rs], right, result)
            else:
                result = (self.r[rs] + right) & 0xFFFFFFFF
                self.set_add_flags(self.r[rs], right, result)
            self.r[rd] = result
            return 1
        if (op & 0xFF87) == 0x4700:
            rm = (op >> 3) & 0xF
            target = self.r[rm]
            if target & 1:
                self.thumb = True
                self.cpsr |= CPSR_T
                self.r[15] = target & 0xFFFFFFFE
            else:
                self.thumb = False
                self.cpsr &= ~CPSR_T
                self.r[15] = target & 0xFFFFFFFC
            return 3
        if (op & 0xF800) == 0x4800:
            rd = (op >> 8) & 7
            off = (op & 0x7FF) << 2
            self.r[rd] = (pc + 4 + off) & 0xFFFFFFFF
            return 3
        if (op & 0xF200) == 0x5000:
            rd = (op >> 8) & 7
            rb = (op >> 3) & 7
            off = ((op >> 6) & 0x1F) << 2
            load = bool(op & 0x0800)
            addr = (self.r[rb] + off) & 0xFFFFFFFF
            if load:
                self.r[rd] = self.read16(addr)
            else:
                self.write16(addr, self.r[rd])
            return 3
        if (op & 0xF200) == 0x6000:
            rd = (op >> 8) & 7
            rb = (op >> 3) & 7
            off = ((op >> 6) & 0x1F) << 2
            load = bool(op & 0x0800)
            addr = (self.r[rb] + off) & 0xFFFFFFFF
            if load:
                self.r[rd] = self.read32(addr)
            else:
                self.write32(addr, self.r[rd])
            return 3
        return 1

    def run_dma(self) -> None:
        io = self.io
        for i in range(4):
            base = (REG_DMA0SAD - 0x04000000) + i * 12
            if base + 11 >= len(io):
                continue
            src = (
                io[base] | (io[base + 1] << 8) | (io[base + 2] << 16) | (io[base + 3] << 24)
            )
            dst = (
                io[base + 4] | (io[base + 5] << 8) | (io[base + 6] << 16) | (io[base + 7] << 24)
            )
            cnt = (
                io[base + 8] | (io[base + 9] << 8) | (io[base + 10] << 16) | (io[base + 11] << 24)
            )
            if not (cnt & 0x80000000):
                continue
            count = cnt & 0xFFFF
            if count == 0:
                count = 0x4000
            word = bool(cnt & (1 << 26))
            size = 4 if word else 2
            for n in range(min(count, 0x1000)):
                if word:
                    self.write32(dst + n * size, self.read32(src + n * size))
                else:
                    self.write16(dst + n * size, self.read16(src + n * size))
            cnt &= ~0x80000000
            io[base + 8] = cnt & 0xFF
            io[base + 9] = (cnt >> 8) & 0xFF
            io[base + 10] = (cnt >> 16) & 0xFF
            io[base + 11] = (cnt >> 24) & 0xFF

    def run_timers(self, c: int) -> None:
        for i in range(4):
            lo = REG_TM0CNT_L + i * 4
            counter = self.read16(lo)
            ctrl = self.read16(lo + 2)
            if ctrl & 0x80:
                counter = (counter + c) & 0xFFFF
                self.write16(lo, counter)

    def request_irq(self, bit: int) -> None:
        self.write16(REG_IF, self.read16(REG_IF) | (1 << bit))

    def handle_irq(self) -> None:
        if (self.read16(REG_IME) & 1) and (self.read16(REG_IE) & self.read16(REG_IF)):
            self.r[14] = self.r[15]
            self.r[15] = 0x00000018
            self.thumb = False
            self.cpsr &= ~CPSR_T

    @staticmethod
    def _unpack_rgb555(c: int) -> tuple[int, int, int]:
        return (c & 0x1F) << 3, ((c >> 5) & 0x1F) << 3, ((c >> 10) & 0x1F) << 3

    def _render_frame_rgb(self) -> None:
        dispcnt = self.io[0] | (self.io[1] << 8)
        mode = dispcnt & 7
        fb = self._fb_rgb
        vram = self.vram
        pal = self.pal
        if mode == 3:
            for y in range(GBA_H):
                row = y * GBA_W * 3
                src = y * GBA_W * 2
                for x in range(GBA_W):
                    off = src + x * 2
                    c = vram[off] | (vram[off + 1] << 8)
                    o = row + x * 3
                    fb[o] = (c & 0x1F) << 3
                    fb[o + 1] = ((c >> 5) & 0x1F) << 3
                    fb[o + 2] = ((c >> 10) & 0x1F) << 3
        elif mode == 4:
            page = 0xA000 if dispcnt & (1 << 4) else 0
            for y in range(GBA_H):
                row = y * GBA_W * 3
                vrow = page + y * GBA_W
                for x in range(GBA_W):
                    idx = vram[vrow + x]
                    p = idx * 2
                    c = pal[p] | (pal[p + 1] << 8)
                    o = row + x * 3
                    fb[o] = (c & 0x1F) << 3
                    fb[o + 1] = ((c >> 5) & 0x1F) << 3
                    fb[o + 2] = ((c >> 10) & 0x1F) << 3
        elif mode == 5:
            page = 0xA000 if dispcnt & (1 << 4) else 0
            backdrop = pal[0] | (pal[1] << 8)
            br, bg, bb = self._unpack_rgb555(backdrop)
            for y in range(GBA_H):
                row = y * GBA_W * 3
                for x in range(GBA_W):
                    o = row + x * 3
                    if x < 160 and y < 128:
                        off = page + (y * 160 + x) * 2
                        c = vram[off] | (vram[off + 1] << 8)
                        fb[o] = (c & 0x1F) << 3
                        fb[o + 1] = ((c >> 5) & 0x1F) << 3
                        fb[o + 2] = ((c >> 10) & 0x1F) << 3
                    else:
                        fb[o], fb[o + 1], fb[o + 2] = br, bg, bb
        else:
            backdrop = pal[0] | (pal[1] << 8)
            br, bg, bb = self._unpack_rgb555(backdrop)
            for y in range(GBA_H):
                row = y * GBA_W * 3
                for x in range(GBA_W):
                    o = row + x * 3
                    fb[o], fb[o + 1], fb[o + 2] = br, bg, bb
        self._fb_seq += 1

    def _advance_scanline_timing(self, c: int) -> None:
        """Advance VCOUNT/VCOUNT IRQ for c CPU cycles (once per frame, not per instruction)."""
        self._line_cycles += c
        lines = self._line_cycles // CYCLES_PER_SCANLINE
        if not lines:
            return
        self._line_cycles -= lines * CYCLES_PER_SCANLINE
        for _ in range(lines):
            self.scanline += 1
            if self.scanline == 160:
                self.request_irq(0)
                self.frame_counter += 1
            if self.scanline >= 228:
                self.scanline = 0
        self.write16(REG_VCOUNT, self.scanline)

    def _run_frame_peripherals(self, ran: int) -> None:
        self._advance_scanline_timing(ran)
        self.run_dma()
        self.run_timers(ran)
        self.handle_irq()
        self._sync_keys()

    def step_cpu_only(self, cpu_cycles: int) -> int:
        """Run CPU/DMA/timer/scanline timing without PPU RGB work."""
        cpu_cycles = max(1, int(cpu_cycles))
        ran = 0
        step_cpu = self.step_cpu
        while ran < cpu_cycles:
            for _ in range(_CPU_BATCH):
                if ran >= cpu_cycles:
                    break
                c = step_cpu()
                ran += c
                self.cycles += c
        self._run_frame_peripherals(ran)
        return ran

    def step(self, cpu_cycles: int = GBA_FRAME_CYCLES) -> None:
        self.step_cpu_only(cpu_cycles)
        self._render_frame_rgb()

    def get_framebuffer(self) -> memoryview:
        return memoryview(self._fb_rgb)


def validate_gba_rom(data: bytes) -> None:
    """Reject files that are not standard retail GBA cartridges."""
    if len(data) < 0xC0:
        raise ValueError("File is too small to be a GBA ROM (need at least 192 bytes).")
    if data[0x04:0xA0] != GBA_NINTENDO_LOGO:
        raise ValueError(
            "Not a valid GBA cartridge: Nintendo logo at 0x04 does not match "
            "(expected a commercial .gba ROM)."
        )
    entry = struct.unpack_from("<I", data, 0xAC)[0]
    if (entry & 0xFF000000) != 0x08000000:
        raise ValueError(
            f"Invalid GBA entry point 0x{entry:08X} (expected 0x08xxxxxx ROM region)."
        )


def _ensure_mewgba() -> type[MewgbaCore]:
    """Return the in-file mewgba core class (always MewgbaCore in this module)."""
    probe = MewgbaCore()
    probe.step(4096)
    if len(probe.get_framebuffer()) != _FB_BYTES:
        raise RuntimeError("mewgba probe failed: invalid framebuffer size")
    return MewgbaCore


# ---------------------------------------------------------------------------
# Application (Chinese-emulator layout, English labels)
# ---------------------------------------------------------------------------
APP_TITLE = "Cat GBA 0.1"
WINDOW_SIZE = "600x400"
SCREEN_SCALE = 2
FPS = 60
FRAME_SEC = 1.0 / FPS
FRAME_MS = 1000.0 / FPS
_DISP_W = GBA_W * SCREEN_SCALE
_DISP_H = GBA_H * SCREEN_SCALE
_DISP_FB_BYTES = _DISP_W * _DISP_H * 3
_PPM_HDR = f"P6\n{_DISP_W} {_DISP_H}\n255\n".encode("ascii")
_EMU_CHUNK_CYCLES = 8192

BG = "black"
BTN_FG = "#3FA9FF"
FG = "#53B8FF"
PANEL_BORDER = "#163A63"


def _scale2x_nearest(src: memoryview, dst: bytearray) -> None:
    """2× nearest-neighbor upscale (240×160 → 480×320)."""
    sw, sh = GBA_W, GBA_H
    dw = _DISP_W
    for y in range(sh):
        sy = y * sw * 3
        dy0 = y * 2 * dw * 3
        dy1 = dy0 + dw * 3
        for x in range(sw):
            sx = sy + x * 3
            r, g, b = src[sx], src[sx + 1], src[sx + 2]
            dx = x * 2 * 3
            for base in (dy0, dy1):
                o = base + dx
                dst[o] = r
                dst[o + 1] = g
                dst[o + 2] = b
                dst[o + 3] = r
                dst[o + 4] = g
                dst[o + 5] = b


class CatGBAWindow:
    def __init__(self, rom_path: str | None = None) -> None:
        self.root = tk.Tk()
        self.root.title(APP_TITLE)
        self.root.geometry(WINDOW_SIZE)
        self.root.resizable(False, False)
        self.root.configure(bg=BG)

        self.core = _ensure_mewgba()()
        self.core_name = "mewgba (in-file)"
        self.current_rom_path: str | None = None
        self.running = False
        self._photo: tk.PhotoImage | None = None
        self._screen_item = None
        self._frames = 0
        self._fps = 0
        self._last_fps_time = time.perf_counter()
        self._next_frame_at = time.perf_counter()
        self._present_at = time.perf_counter()
        self._emu_cycle_acc = 0
        self._last_presented_seq = -1
        self._status_dirty = True
        self._disp_rgb = bytearray(_DISP_FB_BYTES)
        self._ppm_buf = bytearray(len(_PPM_HDR) + _DISP_FB_BYTES)
        self._ppm_buf[: len(_PPM_HDR)] = _PPM_HDR

        self.status_var = tk.StringVar(value=f"Core: {self.core_name}")
        self.info_var = tk.StringVar(value="No ROM loaded — use LOAD ROM or drag a .gba onto the app via CLI.")
        self.keys_var = tk.StringVar(
            value="Keys: Z=A  X=B  Enter=Start  RightShift=Select  Arrows=D-Pad  A=L  S=R"
        )

        self._build_ui()
        self._bind_keys()
        self._refresh_screen()

        if rom_path:
            try:
                self.load_rom(rom_path, auto_run=True)
            except (OSError, ValueError) as exc:
                messagebox.showerror(APP_TITLE, f"Could not boot ROM:\n{exc}", parent=self.root)

    def _widget_style(self) -> dict[str, object]:
        return {
            "bg": BG,
            "fg": BTN_FG,
            "activebackground": BG,
            "activeforeground": FG,
            "highlightbackground": PANEL_BORDER,
            "highlightcolor": FG,
            "highlightthickness": 1,
            "bd": 0,
            "relief": "flat",
            "font": ("TkFixedFont", 10, "bold"),
            "cursor": "hand2",
            "width": 12,
            "pady": 3,
        }

    def _label(
        self,
        parent: tk.Misc,
        text: str | None = None,
        textvariable: tk.StringVar | None = None,
        *,
        size: int = 10,
        bold: bool = False,
        wraplength: int | None = None,
    ) -> tk.Label:
        font = ("TkFixedFont", size, "bold" if bold else "normal")
        return tk.Label(
            parent, text=text, textvariable=textvariable, bg=BG, fg=FG,
            font=font, justify="left", wraplength=wraplength,
        )

    def _build_ui(self) -> None:
        outer = tk.Frame(self.root, bg=BG)
        outer.pack(fill="both", expand=True, padx=8, pady=8)

        left = tk.Frame(outer, bg=BG, highlightbackground=PANEL_BORDER, highlightthickness=1)
        left.pack(side="left", fill="both", expand=False)

        right = tk.Frame(outer, bg=BG, width=96, highlightbackground=PANEL_BORDER, highlightthickness=1)
        right.pack(side="right", fill="y", padx=(8, 0))
        right.pack_propagate(False)

        self._label(left, text=APP_TITLE, size=12, bold=True).pack(anchor="w", padx=8, pady=(6, 2))
        self._label(left, text=f"Core: {self.core_name}", size=9).pack(anchor="w", padx=8, pady=(0, 4))

        screen_frame = tk.Frame(left, bg=BG, highlightbackground=PANEL_BORDER, highlightthickness=1)
        screen_frame.pack(padx=8, pady=4)
        self.screen_canvas = tk.Canvas(
            screen_frame,
            width=GBA_W * SCREEN_SCALE,
            height=GBA_H * SCREEN_SCALE,
            bg=BG,
            highlightthickness=0,
            bd=0,
        )
        self.screen_canvas.pack()

        self._label(left, textvariable=self.info_var, size=9, wraplength=470).pack(anchor="w", padx=8, pady=(6, 2))
        self._label(left, textvariable=self.status_var, size=9, wraplength=470).pack(anchor="w", padx=8, pady=(0, 2))
        self._label(left, textvariable=self.keys_var, size=8, wraplength=470).pack(anchor="w", padx=8, pady=(0, 6))

        button_cfg = self._widget_style()
        for text, cmd in (
            ("LOAD ROM", self.pick_rom),
            ("BOOT", self.boot_current),
            ("RUN", self.start),
            ("PAUSE", self.pause),
            ("STEP", self.step_once),
            ("RESET", self.reset),
            ("INFO", self.show_info),
            ("QUIT", self.root.destroy),
        ):
            tk.Button(right, text=text, command=cmd, **button_cfg).pack(fill="x", padx=6, pady=4)

        tk.Frame(right, bg=PANEL_BORDER, height=1).pack(fill="x", padx=6, pady=(6, 4))
        self._label(
            right,
            text="ARM7TDMI core\nVRAM/PPU/DMA/IRQ\nRetail .gba boot\n60 FPS meow",
            size=8,
            wraplength=84,
        ).pack(anchor="nw", padx=6, pady=4)

    def _bind_keys(self) -> None:
        mapping = {
            "<KeyPress-z>": ("A", True), "<KeyRelease-z>": ("A", False),
            "<KeyPress-x>": ("B", True), "<KeyRelease-x>": ("B", False),
            "<KeyPress-Return>": ("START", True), "<KeyRelease-Return>": ("START", False),
            "<KeyPress-Shift_R>": ("SELECT", True), "<KeyRelease-Shift_R>": ("SELECT", False),
            "<KeyPress-Left>": ("LEFT", True), "<KeyRelease-Left>": ("LEFT", False),
            "<KeyPress-Right>": ("RIGHT", True), "<KeyRelease-Right>": ("RIGHT", False),
            "<KeyPress-Up>": ("UP", True), "<KeyRelease-Up>": ("UP", False),
            "<KeyPress-Down>": ("DOWN", True), "<KeyRelease-Down>": ("DOWN", False),
            "<KeyPress-a>": ("L", True), "<KeyRelease-a>": ("L", False),
            "<KeyPress-s>": ("R", True), "<KeyRelease-s>": ("R", False),
            "<KeyPress-l>": ("LOAD", False),
            "<KeyPress-L>": ("LOAD", False),
        }
        for event_name, (key, pressed) in mapping.items():
            if key == "LOAD":
                self.root.bind(event_name, lambda _e: self.pick_rom())
            else:
                self.root.bind(
                    event_name,
                    lambda _e, k=key, p=pressed: self._handle_key(k, p),
                )

    def _handle_key(self, key: str, pressed: bool) -> None:
        try:
            self.core.set_key(key, pressed)
            if not self.running:
                self.core.step(1024)
                self._refresh_screen()
        except Exception as exc:
            self._set_status(f"Key error: {exc}")

    def _set_status(self, extra: str | None = None) -> None:
        info = self.core.get_rom_info()
        base = (
            f"Core: {self.core_name} | PC: 0x{int(info['pc']):08X} | "
            f"Cycles: {int(info['cycles'])} | Frame: {int(info['frame'])} | "
            f"Present: {FPS} Hz | Emu: {self._fps} fps"
        )
        if info.get("booted"):
            base += " | BOOTED"
        self.status_var.set(f"{base} | {extra}" if extra else base)
        self._status_dirty = False

    def _update_info_text(self) -> None:
        info = self.core.get_rom_info()
        rom_name = Path(self.current_rom_path).name if self.current_rom_path else "<none>"
        self.info_var.set(
            f"ROM: {rom_name} | Title: {info.get('title')} | Code: {info.get('game_code')} | "
            f"Maker: {info.get('maker')} | Size: {info.get('rom_size')} bytes | {info.get('mode')}"
        )

    def _refresh_screen(self) -> None:
        if self.core._fb_seq == self._last_presented_seq:
            return
        self._last_presented_seq = self.core._fb_seq
        _scale2x_nearest(self.core.get_framebuffer(), self._disp_rgb)
        self._ppm_buf[len(_PPM_HDR) :] = self._disp_rgb
        self._photo = tk.PhotoImage(data=bytes(self._ppm_buf), format="PPM", master=self.root)
        if self._screen_item is None:
            self._screen_item = self.screen_canvas.create_image(0, 0, anchor="nw", image=self._photo)
        else:
            self.screen_canvas.itemconfig(self._screen_item, image=self._photo)
        if self._status_dirty:
            self._update_info_text()
            self._set_status()

    def _present_loop(self) -> None:
        """Present the latest framebuffer at 60 Hz (independent of emulation speed)."""
        if not self.running:
            return
        self._refresh_screen()
        self._present_at += FRAME_SEC
        delay_ms = int(max(1.0, (self._present_at - time.perf_counter()) * 1000.0))
        if delay_ms > int(FRAME_MS * 2):
            self._present_at = time.perf_counter()
        self.root.after(delay_ms, self._present_loop)

    def pick_rom(self) -> None:
        path = filedialog.askopenfilename(
            title="Open GBA ROM",
            filetypes=[
                ("GBA cartridge", "*.gba"),
                ("All files", "*.*"),
            ],
        )
        if path:
            self.load_rom(path, auto_run=True)

    def load_rom(self, path: str, *, auto_run: bool = False) -> None:
        data = Path(path).read_bytes()
        validate_gba_rom(data)
        self.core.boot_rom(data)
        self.current_rom_path = path
        self._refresh_screen()
        self._set_status(f"Booted {Path(path).name}")
        if auto_run:
            self.start()

    def boot_current(self) -> None:
        if not self.current_rom_path:
            messagebox.showinfo(APP_TITLE, "Load a .gba ROM first.", parent=self.root)
            return
        self.load_rom(self.current_rom_path, auto_run=True)

    def start(self) -> None:
        if not self.core.loaded:
            messagebox.showinfo(APP_TITLE, "Load a commercial .gba ROM first.", parent=self.root)
            return
        if not self.running:
            self.running = True
            self._next_frame_at = time.perf_counter()
            self._present_at = time.perf_counter()
            self._emu_cycle_acc = 0
            self._present_loop()
            self._run_loop()
            self._set_status("Running")

    def pause(self) -> None:
        self.running = False
        self._set_status("Paused")

    def reset(self) -> None:
        self.running = False
        self.core.reset()
        if self.current_rom_path:
            try:
                data = Path(self.current_rom_path).read_bytes()
                validate_gba_rom(data)
                self.core.boot_rom(data)
            except (OSError, ValueError):
                self.current_rom_path = None
        self._refresh_screen()
        self._set_status("Reset")

    def step_once(self) -> None:
        self.running = False
        self.core.step(GBA_FRAME_CYCLES)
        self._refresh_screen()
        self._set_status("Stepped one frame")

    def show_info(self) -> None:
        info = self.core.get_rom_info()
        msg = textwrap.dedent(
            f"""
            {APP_TITLE}

            Core: {self.core_name}
            Mode: {info.get('mode')}
            ROM title: {info.get('title')}
            Game code: {info.get('game_code')}
            Maker: {info.get('maker')}
            ROM size: {info.get('rom_size')} bytes
            PC: 0x{int(info.get('pc', 0)):08X}
            Booted: {info.get('booted')}

            Real mewgba core: ARM7TDMI interpreter, GBA memory map, PPU modes 3/4/5,
            keypad (KEYINPUT), DMA, timers, and IRQ stubs. Not cycle-accurate like mGBA yet,
            but it executes cart code instead of a fake ROM slideshow.
            """
        ).strip()
        messagebox.showinfo(APP_TITLE, msg, parent=self.root)

    def _run_loop(self) -> None:
        if not self.running:
            return
        deadline = self._next_frame_at + FRAME_SEC
        try:
            while time.perf_counter() < deadline:
                self.core.step_cpu_only(_EMU_CHUNK_CYCLES)
                self._emu_cycle_acc += _EMU_CHUNK_CYCLES
                if self._emu_cycle_acc >= GBA_FRAME_CYCLES:
                    self._emu_cycle_acc -= GBA_FRAME_CYCLES
                    self.core._render_frame_rgb()
                    self._frames += 1
            now = time.perf_counter()
            if now - self._last_fps_time >= 1.0:
                self._fps = self._frames
                self._frames = 0
                self._last_fps_time = now
                self._status_dirty = True
        except Exception as exc:
            self.running = False
            messagebox.showerror(APP_TITLE, f"Runtime error:\n{exc}", parent=self.root)
            return

        self._next_frame_at += FRAME_SEC
        delay_ms = int(max(1.0, (self._next_frame_at - time.perf_counter()) * 1000.0))
        if delay_ms > int(FRAME_MS * 2):
            self._next_frame_at = time.perf_counter()
        self.root.after(delay_ms, self._run_loop)

    def run(self) -> None:
        self.root.mainloop()


def main() -> int:
    rom_path = sys.argv[1] if len(sys.argv) > 1 else None
    CatGBAWindow(rom_path=rom_path).run()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
