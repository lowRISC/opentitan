#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from copy import deepcopy
from typing import Any, Dict, Iterable, List, Optional

from .insn_yaml import Insn
from .operand import RegOperandType


def get_op_val_str(insn: Insn, op_vals: Dict[str, int], opname: str) -> str:
    '''Get the value of the given (register) operand as a string.'''
    op = insn.name_to_operand[opname]
    assert isinstance(op.op_type, RegOperandType)
    return op.op_type.op_val_to_str(op_vals[opname], None)


class ConstantContext:
    '''Represents known-constant GPRs.

    This datatype is used to track and evaluate GPR pointers for indirect
    references.
    '''
    def __init__(self, values: Dict[str, int]):
        # The x0 register needs to always be 0
        assert values.get('x0', None) == 0
        self.values = values.copy()

    @staticmethod
    def empty() -> 'ConstantContext':
        '''Represents a context with no known constants.'''
        return ConstantContext({'x0': 0})

    def set(self, gpr: str, value: int) -> None:
        '''Set the value of a GPR in the context.'''
        if gpr == 'x0':
            # Ignore writes to x0; it's read-only.
            return
        self.values[gpr] = value

    def get(self, gpr: str) -> Optional[int]:
        '''Get the value of a GPR in the context.'''
        return self.values.get(gpr, None)

    def __contains__(self, gpr: str) -> bool:
        return gpr in self.values

    def __deepcopy__(self, memo: Optional[Dict[int,
                                               Any]]) -> 'ConstantContext':
        return ConstantContext(deepcopy(self.values, memo))

    def includes(self, other: 'ConstantContext') -> bool:
        '''Returns true iff other is a restriction of self.'''
        for k, v in other.values.items():
            if self.get(k) != v:
                return False
        return True

    def intersect(self, other: 'ConstantContext') -> 'ConstantContext':
        '''Returns a new context with only values on which self/other agree.

        Does not modify self or other.
        '''
        out = {}
        for k, v in self.values.items():
            if other.get(k) == v:
                out[k] = v
        return ConstantContext(out)

    def removemany(self, to_remove: Iterable[str]) -> None:
        '''Remove the given registers from the constant context.

        Useful for cases when, for example, the given registers have been
        overwritten. Does nothing for registers that are not known constants,
        or for the special register x0.
        '''
        for reg in to_remove:
            if reg != 'x0':
                self.values.pop(reg, None)

    def update_insn(self, insn: Insn, op_vals: Dict[str, int]) -> None:
        '''Updates to new known constant values GPRs after the instruction.

        Currently, this procedure supports only a limited set of instructions.
        Since constant values only need to be known in order to decode indirect
        references to WDRs and loop counts, this set is chosen based on
        operations likely to happen to those registers: `addi`, `lui`, and
        bignum instructions containing `_inc` op_vals.
        '''
        new_values = {}
        if insn.mnemonic == 'addi':
            grs1_name = get_op_val_str(insn, op_vals, 'grs1')
            if grs1_name in self.values:
                grd_name = get_op_val_str(insn, op_vals, 'grd')
                # Operand is a constant; add/update grd
                new_values[grd_name] = self.values[grs1_name] + op_vals['imm']
        elif insn.mnemonic == 'lui':
            grd_name = get_op_val_str(insn, op_vals, 'grd')
            new_values[grd_name] = op_vals['imm'] << 12
        else:
            # If the instruction has any op_vals ending in _inc,
            # assume we're incrementing the corresponding register
            for op in insn.operands:
                if op.name.endswith('_inc') and op_vals[op.name] != 0:
                    # If reg to be incremented is a constant, increment it
                    inc_op = op.name[:-(len('_inc'))]
                    inc_name = get_op_val_str(insn, op_vals, inc_op)
                    if inc_name in self.values:
                        new_values[inc_name] = self.values[inc_name] + 1

        # If the instruction's information-flow graph indicates that we updated
        # any constant register other than the ones handled above, the value of
        # that register can no longer be determined; remove it from the
        # constants dictionary.
        iflow = insn.iflow.evaluate(op_vals, self.values)
        self.removemany(iflow.all_sinks())

        self.values.update(new_values)


def is_gpr_name(name: str):
    return name in [f'x{i}' for i in range(32)]


def parse_required_constants(constants: List[str]) -> Dict[str, int]:
    '''Parses required initial constants.

    Constants are expected to be provided in the form <reg>:<value>, e.g.
    x5:0xfffffff or x22:0. The value can be expressed in decimal or integer
    form. Only GPRs are accepted as required constants (not wide registers or
    special registers).
    '''
    GPR_MAX = (1 << 32) - 1

    out = {}
    for token in constants:
        reg_and_value = token.split(':')
        if len(reg_and_value) != 2:
            raise ValueError(
                f'Could not parse required constant {token}. Please provide '
                'required constants in the form <reg>:<value>, e.g. x5:3.')
        reg, value = reg_and_value
        if not is_gpr_name(reg):
            raise ValueError(
                f'Cannot parse required constant {token}: {reg} is not a '
                'valid GPR name.')
        if not value.isnumeric():
            raise ValueError(
                f'Cannot parse required constant {token}: {value} is not a '
                'recognized numeric value.')
        value = int(value)
        if value < 0 or value > GPR_MAX:
            raise ValueError(
                f'Cannot parse required constant {token}: {value} is out of '
                'range [0, GPR_MAX].')
        out[reg] = value

    return out
