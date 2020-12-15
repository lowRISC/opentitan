# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Callable, Dict, List, Sequence

from shared.otbn_reggen import HjsonDict, load_registers

from .trace import Trace


class TraceExtRegChange(Trace):
    def __init__(self, name: str, op: str, written: int, from_hw: bool, new_value: int):
        self.name = name
        self.op = op
        self.written = written
        self.from_hw = from_hw
        self.new_value = new_value

    def trace(self) -> str:
        return ("otbn.{} {} {:#010x}{} (now {:#010x})"
                .format(self.name,
                        self.op,
                        self.written,
                        ' (from HW)' if self.from_hw else '',
                        self.new_value))

    def rtl_trace(self) -> str:
        return '! otbn.{}: {:#010x}'.format(self.name, self.new_value)


class RGField:
    '''A wrapper around a field in a register as parsed by reggen'''
    def __init__(self, as_dict: HjsonDict):
        name = as_dict.get('name')
        assert isinstance(name, str)

        bitinfo = as_dict.get('bitinfo')
        assert isinstance(bitinfo, tuple)
        assert len(bitinfo) == 3
        mask, width, lsb = bitinfo

        reset_value = as_dict.get('genresval')
        assert isinstance(reset_value, int)

        swaccess = as_dict.get('swaccess')
        assert isinstance(swaccess, str)

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
    def __init__(self, as_dict: HjsonDict):
        field_dicts = as_dict.get('fields')
        assert field_dicts is not None
        assert isinstance(field_dicts, list)

        self.fields = [RGField(fd) for fd in field_dicts]

    def _apply_fields(self,
                      func: Callable[[RGField, int], int],
                      value: int) -> int:
        new_val = 0
        for field in self.fields:
            field_new_val = func(field, value >> field.lsb)
            new_val |= field_new_val << field.lsb
        return new_val

    def write(self, value: int, from_hw: bool) -> int:
        '''Stage the effects of writing a value.

        If from_hw is true, this write is from OTBN hardware (rather than the
        bus). Returns the new value visible to software (which will take effect
        after calling commit).

        '''
        assert value >= 0
        return self._apply_fields(lambda fld, fv: fld.write(fv, from_hw),
                                  value)

    def set_bits(self, value: int) -> int:
        assert value >= 0
        return self._apply_fields(lambda fld, fv: fld.set_bits(fv), value)

    def clear_bits(self, value: int) -> int:
        assert value >= 0
        return self._apply_fields(lambda fld, fv: fld.clear_bits(fv), value)

    def read(self, from_hw: bool) -> int:
        value = 0
        for field in self.fields:
            value |= field.read(from_hw) << field.lsb
        return value

    def commit(self) -> None:
        for field in self.fields:
            field.commit()

    def abort(self) -> None:
        for field in self.fields:
            field.abort()


class OTBNExtRegs:
    def __init__(self) -> None:
        _, reg_list = load_registers()

        self.regs = {}  # type: Dict[str, RGReg]
        self.trace = []  # type: List[TraceExtRegChange]

        # We're interested in the proper registers, and don't care about
        # address tracking. So we can just ignore anything without a 'name'
        # attribute.
        for entry in reg_list:
            name = entry.get('name')
            if name is None:
                continue

            assert isinstance(name, str)

            # reggen's validation should have checked that we have no
            # duplicates.
            assert name not in self.regs
            self.regs[name] = RGReg(entry)

    def _get_reg(self, reg_name: str) -> RGReg:
        reg = self.regs.get(reg_name)
        if reg is None:
            raise ValueError('Unknown register name: {!r}.'.format(reg_name))
        return reg

    def write(self, reg_name: str, value: int, from_hw: bool) -> None:
        '''Stage the effects of writing a value to a register'''
        assert value >= 0
        new_val = self._get_reg(reg_name).write(value, from_hw)
        self.trace.append(TraceExtRegChange(reg_name, '=',
                                            value, from_hw, new_val))

    def set_bits(self, reg_name: str, value: int) -> None:
        '''Set some bits of a register (HW access only)'''
        assert value >= 0
        new_val = self._get_reg(reg_name).set_bits(value)
        self.trace.append(TraceExtRegChange(reg_name, '|=',
                                            value, True, new_val))

    def clear_bits(self, reg_name: str, value: int) -> None:
        '''Clear some bits of a register (HW access only)'''
        assert value >= 0
        new_val = self._get_reg(reg_name).clear_bits(value)
        self.trace.append(TraceExtRegChange(reg_name, '&= ~',
                                            value, True, new_val))

    def read(self, reg_name: str, from_hw: bool) -> int:
        reg = self.regs.get(reg_name)
        if reg is None:
            raise ValueError('Unknown register name: {!r}.'.format(reg_name))
        return reg.read(from_hw)

    def changes(self) -> Sequence[Trace]:
        return self.trace

    def commit(self) -> None:
        # We know that we'll only have any pending changes if self.trace is
        # nonempty, so needn't bother calling commit on each register if not.
        if not self.trace:
            return

        for reg in self.regs.values():
            reg.commit()
        self.trace = []

    def abort(self) -> None:
        for reg in self.regs.values():
            reg.abort()
        self.trace = []
