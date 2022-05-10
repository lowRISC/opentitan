#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import math
import sys
from typing import List, Optional

# Size of OTBN wide data registers.
WDR_SIZE = 256
# Size of bn.mulqacc multiplier.
LIMB_SIZE = 64
# Limbs per WDR.
LIMBS_PER_WDR = WDR_SIZE // LIMB_SIZE
# Assert that limb size divides data register size.
assert (WDR_SIZE % LIMB_SIZE == 0)


class Line:
    '''Represents a single line of a bn.mulqacc block.'''
    def __init__(self, modifiers: List[str], dst: Optional[str], lhs: str,
                 rhs: str, shift: int):
        self.modifiers = modifiers
        self.dst = dst
        self.lhs = lhs
        self.rhs = rhs
        self.shift = shift

    def insn_string(self) -> str:
        '''Return the string representing the instruction.

        Includes 2 spaces after the instruction, which is the minimum required
        padding.
        '''
        # The empty string produces a leading '.' if modifiers exist.
        modifiers_str = '.'.join([''] + self.modifiers)
        return f'bn.mulqacc{modifiers_str}  '

    def dst_string(self) -> str:
        '''Return the string representing the writeback destination.

        Includes a comma and one space of required padding, if self.dst exists.
        '''
        return (self.dst + ', ') if self.dst is not None else ''

    def min_lhs_align(self) -> int:
        '''Returns the minimum column at which the left operand can appear.'''
        return len(self.insn_string()) + len(self.dst_string())

    def pretty(self, lhs_align: Optional[int] = None) -> str:
        '''Stringify the line.

        If `lhs_align` is provided, adds padding to align the left-hand operand
        at that index.
        '''
        insn = self.insn_string()
        dst_str = self.dst_string()
        if lhs_align is not None and lhs_align < len(insn) + len(dst_str):
            raise ValueError(
                f'Cannot align left-hand operand to the index {lhs_align}; '
                f'need {len(insn) + len(dst_str)} characters for '
                f'{insn + dst_str}')
        if lhs_align is None:
            padding = ''
        else:
            padding = ' ' * (lhs_align - len(insn) - len(dst_str))
        return f'{insn}{padding}{dst_str}{self.lhs}, {self.rhs}, {self.shift}'


def make_operand(regs: List[str], limb_index: int) -> str:
    '''Get the string representing the requested limb of the bignum.

    Assumes LIMB_SIZE-bit limbs and WDR_SIZE-bit registers.
    '''
    reg = regs[limb_index // LIMBS_PER_WDR]
    index = limb_index % LIMBS_PER_WDR
    return f'{reg}.{index}'


def make_half_word_writeback(regs: List[str], limb_index: int) -> str:
    '''Get the string representing for the half-word of the result where the
    given limb starts.'''
    reg = regs[limb_index // LIMBS_PER_WDR]
    index = limb_index % LIMBS_PER_WDR
    if index < LIMBS_PER_WDR / 2:
        return f'{reg}.L'
    return f'{reg}.U'


def mask(n: int) -> int:
    '''Return an n-bit mask.'''
    return (1 << n) - 1


def make_block(lhs_bits: int, lhs_regs: List[str], rhs_bits: int,
               rhs_regs: List[str], result_regs: List[str]) -> List[Line]:
    '''Print out the bn.mulqacc block for the bignum product.

    Requires that:
      - The `lhs_regs` list has enough registers to store `lhs_bits` bits
      - The `rhs_regs` list has enough registers to store `rhs_bits` bits
      - The `result_regs` list has enough registers to store the result

    Returns the result as a list, each representing a single line of assembly.
    '''
    # Determine the number of limbs for bn.mulqacc.
    lhs_nlimbs = math.ceil(lhs_bits / LIMB_SIZE)
    rhs_nlimbs = math.ceil(rhs_bits / LIMB_SIZE)

    # Determine the position of the most significant partial product. Note that
    # this product is up to 128 bits, so the actual number of 64-bit limbs in
    # the result is likely 1 higher than this number.

    # Determine the number of "terms" (partial products with the same weight)
    # in the result. For example, if the LHS and RHS each have 2 limbs, the
    # result (a0b0 + (a0b1 + a1b0) << 64 + a1b1 << 128) has 3 terms.
    result_nterms = lhs_nlimbs + rhs_nlimbs - 1

    # Determine the number of full-size words in the result.
    result_nwords = math.ceil((lhs_bits + rhs_bits) / WDR_SIZE)

    # Create the main body of the loop, with half-word writebacks at every 128
    # bits of the result. Track the bounds of the accumulator.
    lines = []
    for i in range(result_nterms):
        # Determine if this is the final word of the result, in which case
        # we'll use a whole-word writeback instead of half-words.
        is_final_word = (i // LIMBS_PER_WDR) == result_nwords - 1
        if is_final_word:
            shift_bits = (i % 4) * 64
        else:
            shift_bits = (i % 2) * 64

        # Gather the partial products for this limb of the result.
        partial_products = []
        for j in range(i + 1):
            if j < lhs_nlimbs and (i - j) < rhs_nlimbs:
                partial_products.append((j, i - j))
        # Sanity check.
        if len(partial_products) == 0:
            raise RuntimeError(f'No partial products for limb {i}!')

        for lhs_idx, rhs_idx in partial_products:
            lines.append(
                Line([], None, make_operand(lhs_regs, lhs_idx),
                     make_operand(rhs_regs, rhs_idx), shift_bits))

        # Every second limb (except for the final word), write back a half-word
        # of the result as part of the last instruction.
        if not is_final_word and i % 2 == 1:
            lines[-1].modifiers.append('so')
            lines[-1].dst = make_half_word_writeback(result_regs, i)

    # It's possible that the last result term crosses a word boundary, so we
    # never will have hit the "final word" condition. If so, we need to add an
    # instruction that just writes back the accumulator to the final word
    # without modifying it. We assume here that w31 = 0.
    if not is_final_word:
        lines.append(Line([], None, 'w31.0', 'w31.0', 0))

    # Write back the final word of the result by adding a `.wo` modifier to the
    # last instruction.
    lines[-1].modifiers.append('wo')
    lines[-1].dst = result_regs[result_nwords - 1]

    # Ensure that the first instruction zeroes the accumulator.
    lines[0].modifiers.append('z')

    return lines


def format_block(lines: List[Line]) -> List[str]:
    '''Format the lines so that the left-hand operands are all aligned.'''
    align = max([line.min_lhs_align() for line in lines])
    return [line.pretty(align) for line in lines]


def is_wdr(reg_name: str) -> bool:
    if not reg_name.startswith('w'):
        return False
    if len(reg_name) < 1:
        return False
    reg_num = reg_name[1:]
    if not reg_num.isnumeric():
        return False
    reg_idx = int(reg_num)
    return (0 <= reg_idx) and (reg_idx <= 31)


def check_regs(regs: List[str], bits: int) -> None:
    '''Checks that register names are valid and there are enough registers to
       store the given number of bits.'''
    for reg_name in regs:
        if not is_wdr(reg_name):
            raise ValueError(f'{reg_name} is not a valid wide data register.')
    if len(regs) * WDR_SIZE < bits:
        raise ValueError(
            f'Register list {regs} does not have enough space to store a '
            f'{bits}-bit number.')
    return


def main() -> int:
    parser = argparse.ArgumentParser(description=(
        'Print out a bn.mulqacc block for the given bignum product.'))
    parser.add_argument('--lhs-bits',
                        type=int,
                        required=True,
                        help='Number of bits in the left-hand operand.')
    parser.add_argument(
        '--lhs-regs',
        nargs='+',
        type=str,
        required=True,
        help='Registers for left-hand operand (little-endian order).')
    parser.add_argument('--rhs-bits',
                        type=int,
                        required=True,
                        help='Number of bits in the right-hand operand.')
    parser.add_argument(
        '--rhs-regs',
        nargs='+',
        type=str,
        required=True,
        help='Registers for the right-hand operand (little-endian order).')
    parser.add_argument(
        '--result-regs',
        nargs='+',
        type=str,
        required=True,
        help=('Registers in which to store the result. Must not overlap with '
              'operand registers.'))
    args = parser.parse_args()

    check_regs(args.lhs_regs, args.lhs_bits)
    check_regs(args.rhs_regs, args.rhs_bits)
    check_regs(args.result_regs, args.lhs_bits + args.rhs_bits)

    # Check that result registers don't overlap with operand registers.
    for reg in args.result_regs:
        if reg in args.lhs_regs or reg in args.rhs_regs:
            raise ValueError(
                f'Result register {reg} also appears in one of the operands.')

    # Check that neither operand is 0 bits.
    if args.lhs_bits == 0 or args.rhs_bits == 0:
        raise ValueError('Both operands must have at least 1 bit.')

    block = make_block(args.lhs_bits, args.lhs_regs, args.rhs_bits,
                       args.rhs_regs, args.result_regs)
    for line in format_block(block):
        print(line)

    return 0


if __name__ == "__main__":
    sys.exit(main())
