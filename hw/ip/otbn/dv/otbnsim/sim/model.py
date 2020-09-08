# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from random import getrandbits
import struct
from typing import List, Optional, Tuple, cast

from attrdict import AttrDict  # type: ignore

from riscvmodel.model import (Model, State,  # type: ignore
                              Environment, TerminateException)
from riscvmodel.types import (RegisterFile, Register,  # type: ignore
                              SingleRegister, Trace, BitflagRegister)

from .variant import RV32IXotbn


class TraceCallStackPush(Trace):  # type: ignore
    def __init__(self, value: int):
        self.value = value

    def __str__(self) -> str:
        return "RAS push {:08x}".format(self.value)


class TraceCallStackPop(Trace):  # type: ignore
    def __init__(self, value: int):
        self.value = value

    def __str__(self) -> str:
        return "RAS pop {:08x}".format(self.value)


class TraceLoopStart(Trace):  # type: ignore
    def __init__(self, iterations: int, bodysize: int):
        self.iterations = iterations
        self.bodysize = bodysize

    def __str__(self) -> str:
        return "Start LOOP, {} iterations, bodysize: {}".format(
            self.iterations, self.bodysize)


class TraceLoopIteration(Trace):  # type: ignore
    def __init__(self, iteration: int, total: int):
        self.iteration = iteration
        self.total = total

    def __str__(self) -> str:
        return "LOOP iteration {}/{}".format(self.iteration, self.total)


class OTBNIntRegisterFile(RegisterFile):  # type: ignore
    def __init__(self) -> None:
        super().__init__(num=32, bits=32, immutable={0: 0})

        # The call stack for x1 and its pending updates
        self.callstack = []  # type: List[int]
        self.have_read_callstack = False
        self.callstack_push_val = None  # type: Optional[int]

    def __setitem__(self, key: int, value: int) -> None:
        # Special handling for the callstack in x1
        if key == 1:
            self.callstack_push_val = value
            return

        # Otherwise, use the base class implementation
        super().__setitem__(key, value)

    def __getitem__(self, key: int) -> Register:
        # Special handling for the callstack in x1
        if key == 1:
            self.have_read_callstack = True

        return cast(Register, super().__getitem__(key))

    def post_insn(self) -> None:
        '''Update the x1 call stack after an instruction executes

        This needs to run after execution (which sets up callstack_push_val and
        have_read_callstack) but before we print the instruction in
        State.issue, because any changes to x1 need to be reflected there.

        '''
        cs_changed = False
        if self.have_read_callstack:
            if self.callstack:
                self.callstack.pop()
                cs_changed = True

        if self.callstack_push_val is not None:
            self.callstack.append(self.callstack_push_val)
            cs_changed = True

        # Update self.regs[1] so that it always points at the top of the stack.
        # If the stack is empty, set it to zero (we need to decide what happens
        # in this case: see issue #3239)
        if cs_changed:
            cs_val = 0
            if self.callstack:
                cs_val = self.callstack[-1]

            super().__setitem__(1, cs_val)

        self.have_read_callstack = False
        self.callstack_push_val = None


class LoopLevel:
    '''An object representing a level in the current loop stack

    start_addr is the first instruction inside the loop (the instruction
    following the loop instruction). insn_count is the number of instructions
    in the loop (and must be positive). restarts is one less than the number of
    iterations, and must be positive.

    '''
    def __init__(self, start_addr: int, insn_count: int, restarts: int):
        assert 0 <= start_addr
        assert 0 < insn_count
        assert 0 < restarts

        self.loop_count = 1 + restarts
        self.restarts_left = restarts
        self.start_addr = start_addr
        self.match_addr = start_addr + 4 * insn_count


class LoopStack:
    '''An object representing the loop stack

    An entry on the loop stack represents a possible back edge: the
    restarts_left counter tracks the number of these back edges. The entry is
    removed when the counter gets to zero.

    '''
    def __init__(self) -> None:
        self.stack = []  # type: List[LoopLevel]
        self.trace = []  # type: List[Trace]

    def start_loop(self,
                   next_addr: int,
                   insn_count: int,
                   loop_count: int) -> Optional[int]:
        '''Start a loop.

        Adds the loop to the stack and returns the next PC if it's not
        straight-line. If the loop count is one, this acts as a NOP (and
        doesn't change the stack). If the loop count is zero, this doesn't
        change the stack but the next PC will be the match address.

        '''
        assert 0 <= next_addr
        assert 0 < insn_count
        assert 0 <= loop_count

        self.trace.append(TraceLoopStart(loop_count, insn_count))

        if loop_count == 0:
            return next_addr + 4 * insn_count

        if loop_count > 1:
            self.stack.append(LoopLevel(next_addr, insn_count, loop_count - 1))

        return None

    def step(self, next_pc: int) -> Optional[int]:
        '''Update loop stack. If we should loop, return new PC'''
        if self.stack:
            top = self.stack[-1]
            if next_pc == top.match_addr:
                assert top.restarts_left > 0
                top.restarts_left -= 1

                if not top.restarts_left:
                    self.stack.pop()

                # 1-based iteration number
                idx = top.loop_count - top.restarts_left
                self.trace.append(TraceLoopIteration(idx, top.loop_count))

                return top.start_addr

        return next_pc

    def changes(self) -> List[Trace]:
        return self.trace

    def commit(self) -> None:
        self.trace = []


class FlagGroups:
    def __init__(self) -> None:
        self.groups = {
            0: BitflagRegister(["C", "L", "M", "Z"], prefix = "FG0."),
            1: BitflagRegister(["C", "L", "M", "Z"], prefix = "FG1.")
        }

    def __getitem__(self, key: int) -> BitflagRegister:
        assert 0 <= key <= 1
        return self.groups[key]

    def __setitem__(self, key: int, value: int) -> None:
        assert 0 <= key <= 1
        self.groups[key].set(value)

    def changes(self) -> List[Trace]:
        return cast(List[Trace],
                    self.groups[0].changes() + self.groups[1].changes())

    def commit(self) -> None:
        self.groups[0].commit()
        self.groups[1].commit()


class OTBNState(State):  # type: ignore
    def __init__(self) -> None:
        super().__init__(RV32IXotbn)

        # Hack: this matches the superclass constructor, but you need it to
        # explain to mypy what self.pc is (because mypy can't peek into
        # riscvmodel without throwing up lots of errors)
        self.pc = Register(32)

        self.intreg = OTBNIntRegisterFile()
        self.wreg = RegisterFile(num=32, bits=256, immutable={}, prefix="w")
        self.single_regs = {
            'acc': SingleRegister(256, "ACC"),
            'mod': SingleRegister(256, "MOD")
        }
        self.flags = FlagGroups()
        self.loop_stack = LoopStack()

    def csr_read(self, index: int) -> int:
        if index == 0x7C0:
            return int(self.wreg)
        elif 0x7D0 <= index <= 0x7D7:
            bit_shift = 32 * (index - 0x7D0)
            mask32 = (1 << 32) - 1
            return (int(self.mod) >> bit_shift) & mask32
        elif index == 0xFC0:
            return getrandbits(32)
        return cast(int, super().csr_read(self, index))

    def wcsr_read(self, index: int) -> int:
        assert 0 <= index <= 2
        if index == 0:
            return int(self.mod)
        elif index == 1:
            return getrandbits(256)
        else:
            assert index == 2
            return int(self.single_regs['acc'])

    def wcsr_write(self, index: int, value: int) -> None:
        if index == 0:
            self.mod = value

    def loop_start(self, iterations: int, bodysize: int) -> None:
        next_pc = int(self.pc) + 4
        skip_pc = self.loop_stack.start_loop(next_pc, bodysize, iterations)
        if skip_pc is not None:
            self.pc_update.set(skip_pc)

    def loop_step(self) -> None:
        back_pc = self.loop_stack.step(int(self.pc_update))
        if back_pc is not None:
            self.pc = back_pc

    def changes(self) -> List[Trace]:
        c = cast(List[Trace], super().changes())
        c += self.loop_stack.changes()
        c += self.wreg.changes()
        c += self.flags.changes()
        for name, reg in sorted(self.single_regs.items()):
            c += reg.changes()
        return c

    def commit(self) -> None:
        super().commit()
        self.loop_stack.commit()
        self.wreg.commit()
        self.flags.commit()
        for reg in self.single_regs.values():
            reg.commit()


class OTBNEnvironment(Environment):  # type: ignore
    def call(self, state: OTBNState) -> None:
        raise TerminateException(0)


class OTBNModel(Model):  # type: ignore
    def __init__(self, verbose: bool):
        super().__init__(RV32IXotbn,
                         environment=OTBNEnvironment(),
                         verbose=verbose,
                         asm_width=35)
        self.state = OTBNState()

    def get_wr_quarterword(self, wridx: int, qwsel: int) -> int:
        assert 0 <= wridx <= 31
        assert 0 <= qwsel <= 3
        mask = (1 << 64) - 1
        return (int(self.state.wreg[wridx]) >> (qwsel * 64)) & mask

    def set_wr_halfword(self, wridx: int, value: int, hwsel: int) -> None:
        assert 0 <= wridx <= 31
        assert (value >> 128) == 0
        assert 0 <= hwsel <= 1

        mask = ((1 << 128) - 1) << (0 if hwsel else 128)
        curr = int(self.state.wreg[wridx]) & mask
        valpos = value << 128 if hwsel else value
        self.state.wreg[wridx] = curr | valpos

    def load_wlen_word_from_memory(self, addr: int) -> int:
        assert 0 <= addr

        word = 0
        for byte_off in range(0, 32, 4):
            bit_off = byte_off * 8
            word += cast(int, self.state.memory.lw(addr + byte_off)) << bit_off
        return word

    def store_bytes_to_memory(self, addr: int, value: bytes) -> None:
        assert 0 <= addr
        assert 0 == len(value) & 3

        for word_idx, word in enumerate(struct.iter_unpack('<I', value)):
            self.state.memory.sw(addr + 4 * word_idx, word[0])

    @staticmethod
    def add_with_carry(a: int, b: int, carry_in: int) -> Tuple[int, int]:
        result = a + b + carry_in

        carryless_result = result & ((1 << 256) - 1)
        flags_out = AttrDict({"C": (result >> 256) & 1,
                              "L": result & 1,
                              "M": (result >> 255) & 1,
                              "Z": 1 if carryless_result == 0 else 0})

        return (carryless_result, flags_out)

    def post_insn(self) -> None:
        '''Update state after running an instruction but before commit'''
        self.state.loop_step()
        self.state.intreg.post_insn()

    def print_trace(self, disasm: str) -> None:
        '''Print a trace of the current instruction to verbose_file'''
        assert self.verbose
        changes_str = ', '.join([str(t) for t in self.state.changes()])
        self.verbose_file.write(self.asm_tpl.format(disasm, changes_str))
