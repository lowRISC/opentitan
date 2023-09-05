# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Callable, Dict, List, Optional, Sequence, Tuple

from reggen.field import Field
from reggen.register import Register
from reggen.reg_block import RegBlock

from shared.otbn_reggen import load_registers

from .edn_client import EdnClient
from .trace import Trace


class ExtRegChange:
    def __init__(self, op: str, written: int, from_hw: bool, new_value: int):
        self.op = op
        self.written = written
        self.from_hw = from_hw
        self.new_value = new_value


class TraceExtRegChange(Trace):
    def __init__(self, name: str, erc: ExtRegChange):
        self.name = name
        self.erc = erc

    def trace(self) -> str:
        suff = (''
                if self.erc.new_value == self.erc.written
                else ' (now {:#010x})'.format(self.erc.new_value))
        return ("otbn.{} {} {:#010x}{}{}"
                .format(self.name,
                        self.erc.op,
                        self.erc.written,
                        ' (from SW)' if not self.erc.from_hw else '',
                        suff))

    def rtl_trace(self) -> str:
        return '! otbn.{}: {:#010x}'.format(self.name, self.erc.new_value)


class RGField:
    '''A wrapper around a field in a register as parsed by reggen'''
    def __init__(self,
                 name: str,
                 width: int,
                 lsb: int,
                 reset_value: int,
                 swaccess: str):
        # We only support some values of swaccess (the ones we need)
        assert swaccess in ['rw1c', 'rw', 'wo', 'r0w1c', 'ro']
        assert width > 0
        assert lsb >= 0

        self.name = name
        self.width = width
        self.lsb = lsb
        self.value = reset_value

        # swaccess
        self.w1c = swaccess in ['rw1c', 'r0w1c']
        self.read_only = swaccess == 'ro'
        self.read_zero = swaccess in ['wo', 'r0w1c']

        self.next_value = reset_value

    @staticmethod
    def from_field(field: Field) -> 'RGField':
        name = field.name
        assert isinstance(name, str)

        width = field.bits.width()
        assert isinstance(width, int)

        lsb = field.bits.lsb
        assert isinstance(lsb, int)

        reset_value = field.resval or 0
        assert isinstance(reset_value, int)

        swaccess = field.swaccess.key
        assert isinstance(swaccess, str)

        return RGField(name, width, lsb, reset_value, swaccess)

    def _next_sw_read(self) -> int:
        return 0 if self.read_zero else self.next_value

    def write(self, value: int, from_hw: bool) -> int:
        '''Stage the effects of writing a value (see RGReg.write)'''
        assert value >= 0
        masked = value & ((1 << self.width) - 1)

        if self.read_only and not from_hw:
            pass
        elif self.w1c and not from_hw:
            self.next_value &= ~masked
        else:
            self.next_value = masked

        return self._next_sw_read()

    def set_bits(self, value: int) -> int:
        '''Like write, but |=.'''
        masked = value & ((1 << self.width) - 1)
        self.next_value |= masked
        return self._next_sw_read()

    def clear_bits(self, value: int) -> int:
        '''Like write, but &= ~.'''
        self.next_value &= ~value
        return self._next_sw_read()

    def read(self, from_hw: bool) -> int:
        return 0 if (self.read_zero and not from_hw) else self.value

    def commit(self) -> None:
        self.value = self.next_value

    def abort(self) -> None:
        self.next_value = self.value


class RGReg:
    '''A wrapper around a register as parsed by reggen'''
    def __init__(self, fields: List[RGField], double_flopped: bool):
        self.fields = fields
        self.double_flopped = double_flopped
        self._changes = []  # type: List[ExtRegChange]
        self._next_changes = []  # type: List[ExtRegChange]

    @staticmethod
    def from_register(reg: Register, double_flopped: bool) -> 'RGReg':
        return RGReg([RGField.from_field(fd) for fd in reg.fields],
                     double_flopped)

    def _apply_fields(self,
                      func: Callable[[RGField, int], int],
                      value: int) -> int:
        new_val = 0
        for field in self.fields:
            field_new_val = func(field, value >> field.lsb)
            new_val |= field_new_val << field.lsb
        return new_val

    def write(self, value: int, from_hw: bool) -> None:
        '''Stage the effects of writing a value.

        If from_hw is true, this write is from OTBN hardware (rather than the
        bus).

        '''
        assert value >= 0
        now = self._apply_fields(lambda fld, fv: fld.write(fv, from_hw), value)
        changes = self._next_changes if self.double_flopped else self._changes
        changes.append(ExtRegChange('=', value, from_hw, now))

    def set_bits(self, value: int) -> None:
        assert value >= 0
        now = self._apply_fields(lambda fld, fv: fld.set_bits(fv), value)
        changes = self._next_changes if self.double_flopped else self._changes
        changes.append(ExtRegChange('=', value, False, now))

    def read(self, from_hw: bool) -> int:
        value = 0
        for field in self.fields:
            value |= field.read(from_hw) << field.lsb
        return value

    def commit(self) -> None:
        for field in self.fields:
            field.commit()
        self._changes = self._next_changes
        self._next_changes = []

    def abort(self) -> None:
        for field in self.fields:
            field.abort()
        self._changes = []
        self._next_changes = []

    def changes(self) -> List[ExtRegChange]:
        return self._changes


class RndReq(RGReg):
    def __init__(self, name: str):
        super().__init__([RGField(name, 32, 0, 0, 'ro')], False)
        self._client = EdnClient()

    def request(self) -> bool:
        '''Set the flag high and start a request on the EDN client

        Returns True if RND_REQ changed.
        '''
        self._client.request()

        if self.read(True) == 0:
            self.write(1, True)
            return True

        return False

    def poison(self) -> None:
        self._client.poison()

    def forget(self) -> None:
        # Clear any pending request in the RND EDN client
        self._client.forget()
        # Also clear the request flag
        self.write(0, True)

    def take_word(self, word: int, fips_err: bool) -> None:
        self._client.take_word(word, fips_err)

    def edn_reset(self) -> None:
        self._client.edn_reset()

    def cdc_complete(self) -> Tuple[Optional[int], bool, bool, bool]:
        '''Clear the flag and return the data that we've read from EDN.

        Returns the same value as EdnClient.cdc_complete().'''
        (data, retry, fips_err, rep_err) = self._client.cdc_complete()
        if not retry:
            self.write(0, True)
        return (data, retry, fips_err, rep_err)

    def step(self) -> None:
        '''Called on each main clock cycle. Step the client'''
        self._client.step()


def make_flag_reg(name: str, double_flopped: bool) -> RGReg:
    return RGReg([RGField(name, 32, 0, 0, 'ro')], double_flopped)


class OTBNExtRegs:
    '''A class representing OTBN's externally visible CSRs

    This models an extra flop between the core and some of the externally
    visible registers by ensuring that a write only becomes visible after an
    intervening commit.

    '''
    double_flopped_regs = ['STATUS']

    def __init__(self) -> None:
        _, reg_block = load_registers()

        self.regs = {}  # type: Dict[str, RGReg]
        self._dirty = 0

        assert isinstance(reg_block, RegBlock)
        for entry in reg_block.flat_regs:
            assert isinstance(entry.name, str)

            # reggen's validation should have checked that we have no
            # duplicates.
            assert entry.name not in self.regs
            double_flopped = entry.name in self.double_flopped_regs
            self.regs[entry.name] = RGReg.from_register(entry, double_flopped)

        # Add a fake "STOP_PC" register.
        #
        # This isn't in the hardware, but it's used in simulation to help track
        # whether RIG-generated binaries finished where they expected to
        # finish.
        self.regs['STOP_PC'] = make_flag_reg('STOP_PC', True)

        # Add a fake "RND_REQ" register to allow us to tell otbn_core_model to
        # generate an EDN request. Expose it as a field so that the state
        # object can poke it directly.
        self._rnd_req = RndReq('RND_REQ')
        self.regs['RND_REQ'] = self._rnd_req

        # Add a fake "WIPE_START" register. We set this for a single cycle when
        # starting secure wipe and the C++ model can use this to trigger a dump
        # of internal state before it gets zeroed out.
        self.regs['WIPE_START'] = make_flag_reg('WIPE_START', False)

    def _get_reg(self, reg_name: str) -> RGReg:
        reg = self.regs.get(reg_name)
        if reg is None:
            raise ValueError('Unknown register name: {!r}.'.format(reg_name))
        return reg

    def write(self, reg_name: str, value: int, from_hw: bool) -> None:
        '''Stage the effects of writing a value to a register'''
        assert value >= 0
        self._get_reg(reg_name).write(value, from_hw)
        self._dirty = 2

    def set_bits(self, reg_name: str, value: int) -> None:
        '''Set some bits of a register (HW access only)'''
        assert value >= 0
        self._get_reg(reg_name).set_bits(value)
        self._dirty = 2

    def increment_insn_cnt(self) -> None:
        '''Increment the INSN_CNT register'''
        reg = self._get_reg('INSN_CNT')
        assert len(reg.fields) == 1
        fld = reg.fields[0]
        reg.write(min(fld.value + 1, (1 << 32) - 1), True)

    def read(self, reg_name: str, from_hw: bool) -> int:
        reg = self.regs.get(reg_name)
        if reg is None:
            raise ValueError('Unknown register name: {!r}.'.format(reg_name))
        return reg.read(from_hw)

    def step(self) -> None:
        self._rnd_req.step()

    def changes(self) -> Sequence[Trace]:
        # If the dirty flag is not set, we know the only possible change is to
        # the INSN_CNT register.
        if self._dirty == 0:
            return [TraceExtRegChange('INSN_CNT', erc)
                    for erc in self.regs['INSN_CNT'].changes()]

        trace = []
        for name, reg in self.regs.items():
            trace += [TraceExtRegChange(name, erc) for erc in reg.changes()]
        return trace

    def commit(self) -> None:
        # If self._dirty is positive, there might be some pending changes to an
        # ext register. In that case, we need to iterate over all of them,
        # calling commit() to make the changes land.
        #
        # If self._dirty is zero, we know there are no pending changes to ext
        # registers except possibly INSN_CNT. Writes to *that* don't trigger
        # the dirty flag because they happen most cycles.
        if self._dirty > 0:
            for reg in self.regs.values():
                reg.commit()
            self._dirty = max(0, self._dirty - 1)
        else:
            self.regs['INSN_CNT'].commit()

    def abort(self) -> None:
        for reg in self.regs.values():
            reg.abort()
        self._dirty = 0

    def rnd_request(self) -> None:
        if self._rnd_req.request():
            self._dirty = 2

    def rnd_take_word(self, word: int, fips_err: bool) -> None:
        self._rnd_req.take_word(word, fips_err)

    def rnd_reset(self) -> None:
        self._rnd_req.edn_reset()
        self._dirty = 2

    def rnd_cdc_complete(self) -> Tuple[Optional[int], bool, bool]:
        (data, retry, fips_err, rep_err) = self._rnd_req.cdc_complete()
        if not retry:
            self._dirty = 2
        return (data, fips_err, rep_err)

    def rnd_poison(self) -> None:
        self._rnd_req.poison()

    def rnd_forget(self) -> None:
        self._rnd_req.forget()
