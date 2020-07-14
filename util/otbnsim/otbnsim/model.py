# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from random import getrandbits
from collections import deque
from attrdict import AttrDict

from riscvmodel.model import Model, State, Environment
from riscvmodel.isa import TerminateException
from riscvmodel.types import RegisterFile, Register, SingleRegister, TraceRegister, TraceIntegerRegister, Trace, TracePC, BitflagRegister

from .variant import RV32IXotbn


class TraceCallStackPush(Trace):
    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "RAS push {:08x}".format(self.value)


class TraceCallStackPop(Trace):
    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "RAS pop {:08x}".format(self.value)


class TraceLoopStart(Trace):
    def __init__(self, iterations, bodysize):
        self.iterations = iterations
        self.bodysize = bodysize

    def __str__(self):
        return "Start LOOP, {} iterations, bodysize: {}".format(
            self.iterations, self.bodysize)


class TraceLoopIteration(Trace):
    def __init__(self, iter, total):
        self.iter = iter
        self.total = total

    def __str__(self):
        return "LOOP iteration {}/{}".format(self.iter, self.total)


class OTBNIntRegisterFile(RegisterFile):
    def __init__(self, num: int, bits: int, immutable: list = {}):
        super().__init__(num, bits, immutable)
        self.callstack = deque()
        self.cs_update = []

    def __setitem__(self, key, value):
        if key == 1:
            self.cs_update.append(TraceCallStackPush(value))
        elif not self.regs[key].immutable:
            reg = Register(self.bits)
            reg.set(value)
            self.regs_updates.append(TraceIntegerRegister(key, reg))

    def __getitem__(self, key):
        if key == 1:
            return self.callstack.popleft()
        return self.regs[key]

    def commit(self):
        for cs in self.cs_update:
            self.callstack.appendleft(cs.value)
        self.cs_update.clear()
        super().commit()

class FlagGroups:
    def __init__(self):
        super().__init__()
        self.groups = { 0: BitflagRegister(["C", "L", "M", "Z"], prefix = "FG0."), 1: BitflagRegister(["C", "L", "M", "Z"], prefix = "FG1.") }

    def __getitem__(self, key):
        return self.groups[key]

    def __setitem__(self, key, value):
        self.groups[key].set(value)

    def changes(self):
        return self.groups[0].changes() + self.groups[1].changes()

    def commit(self):
        self.groups[0].commit()
        self.groups[1].commit()

class OTBNState(State):
    def __init__(self):
        super().__init__(RV32IXotbn)
        self.intreg = OTBNIntRegisterFile(32, 32, {0: 0})
        self.wreg = RegisterFile(32, 256, {}, prefix="w")
        self.single_regs = {}
        self.single_regs["acc"] = SingleRegister(256, "ACC")
        self.single_regs["mod"] = SingleRegister(256, "MOD")
        self.flags = FlagGroups()

        self.loop_trace = []
        self.loop = deque()

    def __setattr__(self, name, value):
        if name in self.single_regs:
            self.single_regs[name].update(value)
        super().__setattr__(name, value)

    def __getattr__(self, name):
        if name in self.single_regs:
            return self.single_regs[name]
        return super().__getattribute__(name)

    def csr_read(self, index):
        if index == 0x7C0:
            return int(self.wreg)
        elif index == 0x7D0:
            return (int(self.mod) >> 0) & 0xffffffff
        elif index == 0x7D1:
            return (int(self.mod) >> 32) & 0xffffffff
        elif index == 0x7D2:
            return (int(self.mod) >> 64) & 0xffffffff
        elif index == 0x7D3:
            return (int(self.mod) >> 96) & 0xffffffff
        elif index == 0x7D4:
            return (int(self.mod) >> 128) & 0xffffffff
        elif index == 0x7D5:
            return (int(self.mod) >> 160) & 0xffffffff
        elif index == 0x7D6:
            return (int(self.mod) >> 192) & 0xffffffff
        elif index == 0x7D7:
            return (int(self.mod) >> 224) & 0xffffffff
        elif index == 0xFC0:
            return getrandbits(32)
        return super().csr_read(self, index)

    def wcsr_read(self, index):
        if index == 0:
            return int(self.mod)
        elif index == 1:
            return getrandbits(256)
        elif index == 2:
            return int(self.acc)

    def wcsr_write(self, index, value):
        old = None
        if index == 0:
            old = int(self.mod)
            self.mod = value
        return old

    def loop_start(self, iterations, bodysize):
        self.loop.appendleft({
            "iterations": iterations,
            "bodysize": bodysize,
            "count_iterations": 0,
            "count_instructions": -1
        })
        self.loop_trace.append(TraceLoopStart(iterations, bodysize))

    def changes(self):
        c = super().changes()
        if len(self.loop) > 0:
            if self.loop[0][
                    "count_instructions"] == self.loop[0]["bodysize"] - 1:
                self.loop_trace.append(
                    TraceLoopIteration(self.loop[0]["count_iterations"] + 1,
                                       self.loop[0]["iterations"]))
                if self.loop[0][
                        "count_iterations"] == self.loop[0]["iterations"] - 1:
                    self.loop.popleft()
                else:
                    pc = self.pc - (self.loop[0]["bodysize"] - 1) * 4
                    self.pc_update = pc
                    c.append(TracePC(pc))
                    self.loop[0]["count_iterations"] += 1
                    self.loop[0]["count_instructions"] = 0
            else:
                self.loop[0]["count_instructions"] += 1
        c += self.loop_trace
        c += self.wreg.changes()
        c += self.flags.changes()
        for reg in self.single_regs:
            c += self.single_regs[reg].changes()
        return c

    def commit(self):
        super().commit()
        self.wreg.commit()
        self.flags.commit()
        self.loop_trace.clear()
        for reg in self.single_regs:
            self.single_regs[reg].commit()

class OTBNEnvironment(Environment):
    def call(self, state: OTBNState):
        raise TerminateException(0)


class OTBNModel(Model):
    def __init__(self, *, verbose=False):
        super().__init__(RV32IXotbn,
                         environment=OTBNEnvironment(),
                         verbose=verbose,
                         asm_width=35)
        self.state = OTBNState()

    def get_wr_quarterword(self, wridx, qwsel):
        return (int(self.state.wreg[wridx]) >>
                (qwsel * 64)) & 0xffffffffffffffff

    def set_wr_halfword(self, wridx, value, hwsel):
        mask = ((1 << 128) - 1) << (128 if hwsel == 0 else 0)
        curr = int(self.state.wreg[wridx]) & mask
        valpos = (value & ((1 << 128) - 1)) << (128 if hwsel == 1 else 0)
        self.state.wreg[wridx].set(curr | valpos)

    def load_wlen_word_from_memory(self, addr):
        word = self.state.memory.lw(addr)
        word += self.state.memory.lw(addr + 4) << 32
        word += self.state.memory.lw(addr + 8) << 64
        word += self.state.memory.lw(addr + 12) << 96
        word += self.state.memory.lw(addr + 16) << 128
        word += self.state.memory.lw(addr + 20) << 160
        word += self.state.memory.lw(addr + 24) << 192
        word += self.state.memory.lw(addr + 28) << 224
        return word

    def store_wlen_word_to_memory(self, addr, word):
        self.state.memory.sw(addr, word & 0xffffffff)
        self.state.memory.sw(addr + 4, (word >> 32) & 0xffffffff)
        self.state.memory.sw(addr + 8, (word >> 64) & 0xffffffff)
        self.state.memory.sw(addr + 12, (word >> 96) & 0xffffffff)
        self.state.memory.sw(addr + 16, (word >> 128) & 0xffffffff)
        self.state.memory.sw(addr + 20, (word >> 160) & 0xffffffff)
        self.state.memory.sw(addr + 24, (word >> 192) & 0xffffffff)
        self.state.memory.sw(addr + 28, (word >> 224) & 0xffffffff)

    @staticmethod
    def add_with_carry(a, b, carry_in):
        result = a + b + carry_in

        flags_out = AttrDict({"C": (result >> 256) & 1,
                              "L": result & 1,
                              "M": (result >> 255) & 1,
                              "Z": 1 if result == 0 else 0})

        return (result & ((1 << 256) - 1), flags_out)
