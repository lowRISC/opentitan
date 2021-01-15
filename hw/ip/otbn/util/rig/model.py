# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import math
import random
from typing import Dict, List, Optional, Set, Tuple

from shared.operand import (OperandType,
                            ImmOperandType, OptionOperandType, RegOperandType)

from .program import ProgInsn


def extended_euclidean_algorithm(a: int, b: int) -> Tuple[int, int, int]:
    '''The extended Euclidean algorithm.

    Returns a tuple (r, s, t) so that gcd is the GCD of the two inputs and r =
    a s + b t.

    '''
    r, r_nxt = a, b
    s, s_nxt = 1, 0
    t, t_nxt = 0, 1

    while r_nxt:
        q = r // r_nxt
        r, r_nxt = r_nxt, r - q * r_nxt
        s, s_nxt = s_nxt, s - q * s_nxt
        t, t_nxt = t_nxt, t - q * t_nxt

    # If both inputs are non-positive, the result comes out negative and we
    # should flip all the signs.
    if r < 0:
        r, s, t = - r, - s, - t

    return (r, s, t)


def intersect_ranges(a: List[Tuple[int, int]],
                     b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    ret = []
    paired = ([(r, False) for r in a] + [(r, True) for r in b])
    arng = None  # type: Optional[Tuple[int, int]]
    brng = None  # type: Optional[Tuple[int, int]]
    for (lo, hi), is_b in sorted(paired):
        if is_b:
            if arng is not None:
                a0, a1 = arng
                if a0 <= hi and lo <= a1:
                    ret.append((max(a0, lo), min(a1, hi)))
            brng = (lo, hi)
        else:
            if brng is not None:
                b0, b1 = brng
                if b0 <= hi and lo <= b1:
                    ret.append((max(lo, b0), min(hi, b1)))
            arng = (lo, hi)
    return ret


class KnownMem:
    '''A representation of what memory/CSRs have architectural values'''
    def __init__(self, top_addr: int):
        assert top_addr > 0

        self.top_addr = top_addr
        # A list of pairs of addresses. If the pair (lo, hi) is in the list
        # then each byte in the address range {lo..hi - 1} has a known value.
        self.known_ranges = []  # type: List[Tuple[int, int]]

    def copy(self) -> 'KnownMem':
        '''Return a shallow copy of the object'''
        ret = KnownMem(self.top_addr)
        ret.known_ranges = self.known_ranges.copy()
        return ret

    def merge(self, other: 'KnownMem') -> None:
        '''Merge in values from another KnownMem object'''
        assert self.top_addr == other.top_addr
        self.known_ranges = intersect_ranges(self.known_ranges,
                                             other.known_ranges)

    def touch_range(self, base: int, width: int) -> None:
        '''Mark {base .. base + width - 1} as known'''
        assert 0 <= width
        assert 0 <= base <= self.top_addr - width
        for off in range(width):
            self.touch_addr(base + off)

    def touch_addr(self, addr: int) -> None:
        '''Mark word starting at addr as known'''
        assert 0 <= addr < self.top_addr

        # Find the index of the last range that starts below us, if there is
        # one, and the index of the first range that starts above us, if there
        # is one.
        last_idx_below = None
        first_idx_above = None
        for idx, (lo, hi) in enumerate(self.known_ranges):
            if lo <= addr:
                last_idx_below = idx
                continue

            first_idx_above = idx
            break

        # Are we below all other ranges?
        if last_idx_below is None:
            # Are we one address below the next range above? In which case, we
            # need to shuffle it back one.
            if first_idx_above is not None:
                lo, hi = self.known_ranges[first_idx_above]
                assert addr < lo
                if addr == lo - 1:
                    self.known_ranges[first_idx_above] = (lo - 1, hi)
                    return

            # Otherwise, we're disjoint. Add a one-element range at the start.
            self.known_ranges = [(addr, addr + 1)] + self.known_ranges
            return

        # If not, are we inside a range? In that case, there's nothing to do.
        left_lo, left_hi = self.known_ranges[last_idx_below]
        if addr < left_hi:
            return

        left = self.known_ranges[:last_idx_below]

        # Are we just above it?
        if addr == left_hi:
            # If there is no range above, we can just extend the last range by one.
            if first_idx_above is None:
                self.known_ranges = left + [(left_lo, left_hi + 1)]
                return

            # Otherwise, does this new address glue two ranges together?
            assert first_idx_above == last_idx_below + 1
            right_lo, right_hi = self.known_ranges[first_idx_above]
            assert addr < right_lo

            if addr == right_lo - 1:
                self.known_ranges = (left + [(left_lo, right_hi)] +
                                     self.known_ranges[first_idx_above + 1:])
                return

            # Otherwise, we still extend the range by one (but have to put the
            # right hand list back too).
            self.known_ranges = (left + [(left_lo, left_hi + 1)] +
                                 self.known_ranges[first_idx_above:])
            return

        # We are miles above the left range. If there is no range above, we can
        # just append a new 1-element range.
        left_inc = self.known_ranges[:first_idx_above]
        if first_idx_above is None:
            self.known_ranges.append((addr, addr + 1))
            return

        # Otherwise, are we just below the next range?
        assert first_idx_above == last_idx_below + 1
        right_lo, right_hi = self.known_ranges[first_idx_above]
        assert addr < right_lo

        if addr == right_lo - 1:
            self.known_ranges = (left_inc + [(right_lo - 1, right_hi)] +
                                 self.known_ranges[first_idx_above + 1:])
            return

        # If not, we just insert a 1-element range in between
        self.known_ranges = (left_inc + [(addr, addr + 1)] +
                             self.known_ranges[first_idx_above:])
        return

    def pick_lsu_target(self,
                        loads_value: bool,
                        base_addr: int,
                        offset_range: Tuple[int, int],
                        offset_align: int,
                        width: int,
                        addr_align: int) -> Optional[int]:
        '''Try to pick an address with base and offset.

        If loads_value is true, the memory needs a known value for at least
        width bytes starting at that address. The address should be encodable
        as base_addr + offset where offset is in offset_range (inclusive) and
        is a multiple of offset_align. The address must be a multiple of
        addr_align.

        On failure, returns None. On success, returns the chosen address.

        '''
        assert offset_range[0] <= offset_range[1]
        assert 1 <= offset_align
        assert 1 <= width
        assert 1 <= addr_align

        # We're trying to pick an offset and an address so that
        #
        #   base_addr + offset = addr
        #
        # Let's ignore offset_range and questions about valid memory addresses
        # for a second. We have two alignment requirements from offset and
        # addr, which mean we're really trying to satisfy something that looks
        # like
        #
        #    a = b i + c j
        #
        # for a = base_addr; b = -offset_align; c = addr_align: find solutions
        # i, j.
        #
        # This is a 2-variable linear Diophantine equation. If gcd(b, c) does
        # not divide a, there is no solution. Otherwise, the extended Euclidean
        # algorithm yields x0, y0 such that
        #
        #    gcd(b, c) = b x0 + c y0.
        #
        # Multiplying up by a / gcd(b, c) gives
        #
        #    a = b i0 + c j0
        #
        # where i0 = x0 * a / gcd(b, c) and j0 = y0 * a / gcd(b, c).
        #
        # This is the "inhomogeneous part". It's a solution to the equation,
        # and every other solution, (i, j) is a translate of the form
        #
        #    i = i0 + k v
        #    j = j0 - k u
        #
        # for some k, where u = b / gcd(b, c) and v = c / gcd(b, c).
        gcd, x0, y0 = extended_euclidean_algorithm(-offset_align, addr_align)
        assert gcd == -offset_align * x0 + addr_align * y0
        assert 0 < gcd

        if base_addr % gcd:
            return None

        # If gcd divides base_addr, we convert x0 and y0 to an initial solution
        # (i0, j0) as described above by multiplying up by base_addr / gcd.
        scale_factor = base_addr // gcd
        i0 = x0 * scale_factor
        j0 = y0 * scale_factor
        minus_u = offset_align // gcd
        v = addr_align // gcd
        assert 0 < v
        assert 0 < minus_u

        # offset_range gives the possible values of offset, which is - b i
        # in the equations above. Re-arranging the equation for i gives:
        #
        #   k v = i - i0
        #
        # so
        #
        #   b k v = b i - b i0 = - offset - b i0
        #
        # or
        #
        #   k = (- offset - b i0) / (b v)
        #
        # Since b < 0 and v > 0, the denominator is negative and this is an
        # increasing function of offset, so we can get the allowed range for k
        # by evaluating it at the endpoints of offset_range.
        bv = - offset_align * v
        k_max = (-offset_range[1] + offset_align * i0) // bv
        k_min = (-offset_range[0] + offset_align * i0 + (bv - 1)) // bv

        # If k_min > k_max, this means b*v gives such big steps that none
        # landed in the range of allowed offsets
        if k_max < k_min:
            return None

        # Now, we need to consider which memory locations we can actually use.
        # If we're writing memory, we have a single range of allowed addresses
        # (all of memory!). If reading, we need to use self.known_ranges. In
        # either case, adjust for the fact that we need a width-byte access and
        # then rescale everything into "k units".
        #
        # To do that rescaling, we know that c j = addr and that j = j0 - k u.
        # So
        #
        #   j0 - k u = addr / c
        #   k u      = j0 - addr / c
        #   k        = (j0 - addr / c) / u
        #            = (addr / c - j0) / (- u)
        #
        # Since u is negative, this is an increasing function of addr, so we
        # can use address endpoints to get (disjoint) ranges for k.
        k_ranges = []
        k_weights = []
        byte_ranges = (self.known_ranges
                       if loads_value else [(0, self.top_addr - 1)])

        for byte_lo, byte_top in byte_ranges:
            # Since we're doing an access of width bytes, we round byte_top
            # down to the largest base address where the access lies completely
            # in the range.
            base_hi = byte_top - width
            if base_hi < byte_lo:
                continue

            # Compute the valid range for addr/c, rounding inwards.
            word_lo = (byte_lo + addr_align - 1) // addr_align
            word_hi = base_hi // addr_align

            # If word_hi < word_lo, there are no multiples of addr_align in the
            # range [byte_lo, base_hi].
            if word_hi < word_lo:
                continue

            # Now translate by -j0 and divide through by -u, rounding inwards.
            k_hi = (word_hi - j0) // minus_u
            k_lo = (word_lo - j0 + (minus_u - 1)) // minus_u

            # If k_hi < k_lo, that means there are no multiples of u in the
            # range [word_lo - j0, word_hi - j0].
            if k_hi < k_lo:
                continue

            # Finally, take the intersection with [k_min, k_max]. The
            # intersection is non-empty so long as k_lo <= k_max and k_min <=
            # k_hi.
            if k_lo > k_max or k_min > k_hi:
                continue

            k_lo = max(k_lo, k_min)
            k_hi = min(k_hi, k_max)

            k_ranges.append((k_lo, k_hi))
            k_weights.append(k_hi - k_lo + 1)

        if not k_ranges:
            return None

        # We can finally pick a value of k. Pick the range (weighted by
        # k_weights) and then pick uniformly from in that range.
        k_lo, k_hi = random.choices(k_ranges, weights=k_weights)[0]
        k = random.randrange(k_lo, k_hi + 1)

        # Convert back to a solution to the original problem
        i = i0 + k * v
        j = j0 + k * minus_u

        offset = offset_align * i
        addr = addr_align * j

        assert addr == base_addr + offset
        return addr


class CallStack:
    '''An abstract model of the x1 call stack'''
    def __init__(self) -> None:
        self._min_depth = 0
        self._max_depth = 0
        self._elts_at_top = []  # type: List[Optional[int]]

    def copy(self) -> 'CallStack':
        '''Return a deep copy of the call stack'''
        ret = CallStack()
        ret._min_depth = self._min_depth
        ret._max_depth = self._max_depth
        ret._elts_at_top = self._elts_at_top.copy()
        return ret

    def merge(self, other: 'CallStack') -> None:
        self._min_depth = min(self._min_depth, other._min_depth)
        self._max_depth = max(self._max_depth, other._max_depth)
        new_top = []
        for a, b in zip(reversed(self._elts_at_top),
                        reversed(other._elts_at_top)):
            if a == b:
                new_top.append(a)
            else:
                break
        new_top.reverse()
        self._elts_at_top = new_top
        assert self._min_depth <= self._max_depth
        assert len(self._elts_at_top) <= self._max_depth

    def empty(self) -> bool:
        assert 0 <= self._min_depth
        return self._min_depth == 0

    def full(self) -> bool:
        assert self._max_depth <= 8
        return self._max_depth == 8

    def pop(self) -> None:
        assert 0 < self._min_depth
        self._min_depth -= 1
        self._max_depth -= 1
        if self._elts_at_top:
            self._elts_at_top.pop()

    def peek(self) -> Optional[int]:
        assert 0 < self._min_depth
        return self._elts_at_top[-1] if self._elts_at_top else None

    def write(self, value: Optional[int], update: bool) -> None:
        '''Write a value to the call stack.

        The update flag works as described for Model.write_reg

        '''
        if update:
            # If we're updating a write to x1, check that the new value refines
            # the top of the call stack.
            assert self._min_depth > 0
            if self._elts_at_top:
                assert self._elts_at_top[-1] in [None, value]
                self._elts_at_top[-1] = value
            else:
                self._elts_at_top.append(value)
        else:
            assert not self.full()
            self._min_depth += 1
            self._max_depth += 1
            self._elts_at_top.append(value)


class Model:
    '''An abstract model of the processor and memories

    This definitely doesn't try to act as a simulator. Rather, it tracks what
    registers and locations in memory are guaranteed have defined values after
    following the instruction stream to this point.

    '''
    def __init__(self, dmem_size: int, reset_addr: int, fuel: int) -> None:
        assert fuel >= 0
        self.initial_fuel = fuel
        self.fuel = fuel

        self.dmem_size = dmem_size

        # Known values for registers. This is a dictionary mapping register
        # type to a dictionary of known registers of that type. The register
        # type is a string matching the formats in RegOperandType.TYPE_FMTS.
        # The value for a type is another dictionary, mapping register index to
        # an Optional[int]. If the value is a number, the register value is
        # known to currently equal that number. If it is None, the register
        # value is unknown (but the register does have an architectural value).
        #
        # Note that x1 behaves a bit strangely because of the call stack rules,
        # so we don't store it in _known_regs but instead in _call_stack.
        self._known_regs = {}  # type: Dict[str, Dict[int, Optional[int]]]

        # Set x0 (the zeros register)
        self._known_regs['gpr'] = {0: 0}

        # A call stack, representing the contents of x1. The top of the stack
        # is at the end (position -1), to match Python's list.pop function. A
        # entry of None means an entry with an architectural value, but where
        # we don't actually know what it is (usually a result of some
        # arithmetic operation that got written to x1).
        self._call_stack = CallStack()

        # Known values for memory, keyed by memory type ('dmem', 'csr', 'wsr').
        csrs = KnownMem(4096)
        wsrs = KnownMem(4096)
        self._known_mem = {
            'dmem': KnownMem(dmem_size),
            'csr': csrs,
            'wsr': wsrs
        }

        # Valid CSRs and WSRs
        csrs.touch_addr(0x7c0)      # FG0
        csrs.touch_addr(0x7c1)      # FG1
        csrs.touch_addr(0x7c8)      # FLAGS
        csrs.touch_range(0x7d0, 8)  # MOD0 - MOD7
        csrs.touch_addr(0xfc0)      # RND

        wsrs.touch_addr(0x0)        # MOD
        wsrs.touch_addr(0x1)        # RND
        wsrs.touch_addr(0x2)        # ACC

        # The current PC (the address of the next instruction that needs
        # generating)
        self.pc = reset_addr

    def copy(self) -> 'Model':
        '''Return a deep copy of the model'''
        ret = Model(self.dmem_size, self.pc, self.initial_fuel)
        ret.fuel = self.fuel
        ret._known_regs = {n: regs.copy()
                           for n, regs in self._known_regs.items()}
        ret._call_stack = self._call_stack.copy()
        ret._known_mem = {n: mem.copy()
                          for n, mem in self._known_mem.items()}
        return ret

    def merge(self, other: 'Model') -> None:
        '''Merge in values from another model'''
        assert self.initial_fuel == other.initial_fuel
        self.fuel = min(self.fuel, other.fuel)
        assert self.dmem_size == other.dmem_size

        reg_types = self._known_regs.keys() | other._known_regs.keys()
        for reg_type in reg_types:
            sregs = self._known_regs.get(reg_type)
            oregs = other._known_regs.get(reg_type)
            if sregs is None:
                # If sregs is None, we have no registers that are known to have
                # architectural values.
                continue
            if oregs is None:
                # If oregs is None, other has no registers with architectural
                # values. Thus the merged model shouldn't have any either.
                del self._known_regs[reg_type]
                continue

            # Both register files have at least some architectural values.
            # Build a new, merged version.
            merged = {}  # type: Dict[int, Optional[int]]
            for reg_name, svalue in sregs.items():
                ovalue = oregs.get(reg_name, 'missing')
                if ovalue == 'missing':
                    # The register is missing from oregs. This means it might
                    # not have an architectural value, so we should skip it
                    # from sregs too.
                    pass
                elif ovalue is None:
                    # The register has an architectural value in other, but not
                    # one we know. Make sure it's unknown here too.
                    merged[reg_name] = None
                else:
                    assert isinstance(ovalue, int)
                    if svalue is None:
                        # The register has an unknown architectural value in
                        # self and a known value in other. So we don't know its
                        # value (but it is still architecturally specified): no
                        # change.
                        merged[reg_name] = None
                    else:
                        # self and other both have a known value for the
                        # register. Do they match? If so, take that value.
                        # Otherwise, make it unknown.
                        merged[reg_name] = None if svalue != ovalue else svalue

            self._known_regs[reg_type] = merged

        self._call_stack.merge(other._call_stack)

        for mem_type, self_mem in self._known_mem.items():
            self_mem.merge(other._known_mem[mem_type])

        assert self.pc == other.pc

    def read_reg(self, reg_type: str, idx: int) -> None:
        '''Update the model for a read of the given register

        This is mostly ignored, but has an effect for x1, which pops from the
        call stack on a read.

        '''
        if reg_type == 'gpr' and idx == 1:
            self._call_stack.pop()

    def write_reg(self,
                  reg_type: str,
                  idx: int,
                  value: Optional[int],
                  update: bool) -> None:
        '''Mark a register as having an architectural value

        If value is not None, it is the actual value that the register has.
        Writes to the zeros register x0 are ignored.

        The update flag is normally False. If set, it means that other code has
        already updated the model with a write of a value to the register for
        this instruction, and we should replace that value with the given one,
        which refines the previous value. This is irrelevant for idempotent
        registers, but matters for x1.

        '''
        if reg_type == 'gpr':
            if idx == 0:
                # Ignore writes to x0
                return

            if idx == 1:
                # Special-case writes to x1
                self._call_stack.write(value, update)
                return

        self._known_regs.setdefault(reg_type, {})[idx] = value

    def get_reg(self, reg_type: str, idx: int) -> Optional[int]:
        '''Get a register value, if known.'''
        if reg_type == 'gpr' and idx == 1:
            return self._call_stack.peek()

        return self._known_regs.setdefault(reg_type, {}).get(idx)

    def touch_mem(self, mem_type: str, base: int, width: int) -> None:
        '''Mark {base .. base+width} as known for given memory type'''
        assert mem_type in self._known_mem
        self._known_mem[mem_type].touch_range(base, width)

    def pick_operand_value(self, op_type: OperandType) -> Optional[int]:
        '''Pick a random value for an operand

        The result will always be non-negative: if the operand is a signed
        immediate, this is encoded as 2s complement.

        '''
        if isinstance(op_type, RegOperandType):
            return self.pick_reg_operand_value(op_type)

        op_rng = op_type.get_op_val_range(self.pc)
        if op_rng is None:
            # If we don't know the width, the only immediate that we *know*
            # is going to be valid is 0.
            return 0

        if isinstance(op_type, ImmOperandType):
            shift = op_type.shift
        else:
            shift = 0

        align = 1 << shift

        lo, hi = op_rng
        sh_lo = (lo + align - 1) // align
        sh_hi = hi // align

        op_val = random.randint(sh_lo, sh_hi) << shift
        return op_type.op_val_to_enc_val(op_val, self.pc)

    def pick_reg_operand_value(self, op_type: RegOperandType) -> Optional[int]:
        '''Pick a random value for a register operand

        Returns None if there's no valid value possible.'''
        if op_type.is_src():
            # This operand needs an architectural value. Pick a register
            # from the indices in _known_regs[op_type.reg_type].
            known_regs = self._known_regs.get(op_type.reg_type)
            if not known_regs:
                return None

            known_list = list(known_regs)
            if op_type.reg_type == 'gpr':
                # Add x1 if to the list of known registers (if it has an
                # architectural value). This won't appear in known_regs,
                # because we don't track x1 there.
                assert 1 not in known_regs
                if not self._call_stack.empty():
                    known_list.append(1)

            return random.choice(known_list)

        # This operand isn't treated as a source. Pick any register, but "roll
        # again" if we pick x1 and the call stack is full.
        assert op_type.width is not None
        while True:
            idx = random.getrandbits(op_type.width)
            if ((idx == 1 and
                 op_type.reg_type == 'gpr' and
                 self._call_stack.full())):
                continue
            return idx

    def regs_with_known_vals(self, reg_type: str) -> List[Tuple[int, int]]:
        '''Find registers whose values are known

        Returns a list of pairs (idx, value) where idx is the register index
        and value is its value.

        '''
        ret = []
        known_regs = self._known_regs.setdefault(reg_type, {})
        for reg_idx, reg_val in known_regs.items():
            if reg_val is not None:
                ret.append((reg_idx, reg_val))

        # Handle x1, which has a known value iff the top of the call stack is
        # not None
        if reg_type == 'gpr':
            assert 1 not in known_regs
            if not self._call_stack.empty():
                x1 = self._call_stack.peek()
                if x1 is not None:
                    ret.append((1, x1))

        return ret

    def regs_with_architectural_vals(self, reg_type: str) -> List[int]:
        '''List registers that have an architectural value'''
        known_regs = self._known_regs.setdefault(reg_type, {})
        arch_regs = list(known_regs.keys())

        # Handle x1, which has an architectural (and known) value iff the call
        # stack is not empty.
        if reg_type == 'gpr':
            assert 1 not in arch_regs
            if not self._call_stack.empty():
                arch_regs.append(1)

        return arch_regs

    def pick_lsu_target(self,
                        mem_type: str,
                        loads_value: bool,
                        known_regs: Dict[str, List[Tuple[int, int]]],
                        imm_rng: Tuple[int, int],
                        imm_shift: int,
                        byte_width: int) -> Optional[Tuple[int,
                                                           int,
                                                           Dict[str, int]]]:
        '''Try to pick an address for a naturally-aligned LSU operation.

        mem_type is the type of memory (which must a key of self._known_mem).
        If loads_value, this address needs to have an architecturally defined
        value.

        known_regs is a map from operand name to a list of pairs (idx, value)
        with index and known value for this register operand. Any immediate
        operand will have a value in the range imm_rng (including endpoints)
        and a shift of imm_shift. byte_width is the number of contiguous
        addresses that the LSU operation touches.

        Returns None if we can't find an address. Otherwise, returns a tuple
        (addr, imm_val, reg_vals) where addr is the target address, imm_val is
        the value of any immediate operand and reg_vals is a map from operand
        name to the index picked for that register operand.

        '''
        assert mem_type in self._known_mem
        assert imm_rng[0] <= imm_rng[1]
        assert 0 <= imm_shift

        # A "general" solution to this needs constraint solving, but we expect
        # imm_rng to cover most of the address space most of the time. So we'll
        # do something much simpler: pick a value for each register, then pick
        # a target address that can be reached from the "sum so far" plus the
        # range of the immediate.
        reg_indices = {}
        reg_sum = 0

        # The base address should be aligned to base_align (see the logic in
        # KnownMem.pick_lsu_target), otherwise we'll fail to find anything.
        base_align = math.gcd(byte_width, 1 << imm_shift)

        for name, indices in known_regs.items():
            aligned_regs = [(idx, value)
                            for idx, value in indices
                            if value % base_align == 0]

            # If there are no known aligned indices for this operand, give up now.
            if not aligned_regs:
                return None

            # Otherwise, pick an index and value.
            idx, value = random.choice(aligned_regs)
            reg_sum += value
            reg_indices[name] = idx

        known_mem = self._known_mem[mem_type]
        addr = known_mem.pick_lsu_target(loads_value,
                                         reg_sum,
                                         imm_rng,
                                         1 << imm_shift,
                                         byte_width,
                                         byte_width)

        # If there was no address we could use, give up.
        if addr is None:
            return None

        return (addr, addr - reg_sum, reg_indices)

    def update_for_lui(self, prog_insn: ProgInsn) -> None:
        '''Update model state after a LUI

        A lui instruction looks like "lui x2, 80000" or similar. This operation
        is easy to understand, so we can actually update the model registers
        appropriately.

        '''
        insn = prog_insn.insn
        op_vals = prog_insn.operands
        assert insn.mnemonic == 'lui'
        assert len(insn.operands) == len(op_vals)

        exp_shape = (len(insn.operands) == 2 and
                     isinstance(insn.operands[0].op_type, RegOperandType) and
                     insn.operands[0].op_type.reg_type == 'gpr' and
                     insn.operands[0].op_type.is_dest() and
                     isinstance(insn.operands[1].op_type, ImmOperandType) and
                     not insn.operands[1].op_type.signed)
        if not exp_shape:
            raise RuntimeError('LUI instruction read from insns.yml is '
                               'not the shape expected by '
                               'Model.update_for_lui.')

        self._generic_update_for_insn(prog_insn)

        assert op_vals[1] >= 0
        self.write_reg('gpr', op_vals[0], op_vals[1] << 12, True)

    def update_for_addi(self, prog_insn: ProgInsn) -> None:
        '''Update model state after an ADDI

        If the source register happens to have a known value, we can do the
        addition and store the known result.

        '''
        insn = prog_insn.insn
        op_vals = prog_insn.operands
        assert insn.mnemonic == 'addi'
        assert len(insn.operands) == len(op_vals)

        exp_shape = (len(insn.operands) == 3 and
                     isinstance(insn.operands[0].op_type, RegOperandType) and
                     insn.operands[0].op_type.reg_type == 'gpr' and
                     insn.operands[0].op_type.is_dest() and
                     isinstance(insn.operands[1].op_type, RegOperandType) and
                     insn.operands[1].op_type.reg_type == 'gpr' and
                     not insn.operands[1].op_type.is_dest() and
                     isinstance(insn.operands[2].op_type, ImmOperandType) and
                     insn.operands[2].op_type.signed)
        if not exp_shape:
            raise RuntimeError('ADDI instruction read from insns.yml is '
                               'not the shape expected by '
                               'Model.update_for_addi.')

        src_val = self.get_reg('gpr', op_vals[1])
        if src_val is None:
            result = None
        else:
            # op_vals[2] is the immediate, but is already "encoded" as an unsigned
            # value. Turn it back into the signed operand that actually gets added.
            imm_op = insn.operands[2]
            imm_val = imm_op.op_type.enc_val_to_op_val(op_vals[2], self.pc)
            assert imm_val is not None
            result = (src_val + imm_val) & ((1 << 32) - 1)

        self._generic_update_for_insn(prog_insn)

        self.write_reg('gpr', op_vals[0], result, True)

    def _inc_gpr(self,
                 gpr: int,
                 gpr_val: Optional[int],
                 delta: int,
                 mask: int) -> None:
        '''Mark gpr as having a value and increment it if known

        This passes update=False to self.write_reg: it should be used for
        registers that haven't already been marked as updated by the
        instruction.

        '''
        new_val = (gpr_val + delta) & mask if gpr_val is not None else None
        self.write_reg('gpr', gpr, new_val, False)

    def update_for_bnlid(self, prog_insn: ProgInsn) -> None:
        '''Update model state after an BN.LID

        We need this special case code because of the indirect access to the
        wide-side register file.

        '''
        insn = prog_insn.insn
        op_vals = prog_insn.operands
        assert insn.mnemonic == 'bn.lid'
        assert len(insn.operands) == len(op_vals)

        grd_op, grs1_op, offset_op, grs1_inc_op, grd_inc_op = insn.operands
        exp_shape = (
            # grd
            isinstance(grd_op.op_type, RegOperandType) and
            grd_op.op_type.reg_type == 'gpr' and
            not grd_op.op_type.is_dest() and
            # grs1
            isinstance(grs1_op.op_type, RegOperandType) and
            grs1_op.op_type.reg_type == 'gpr' and
            not grs1_op.op_type.is_dest() and
            # offset
            isinstance(offset_op.op_type, ImmOperandType) and
            offset_op.op_type.signed and
            # grs1_inc
            isinstance(grs1_inc_op.op_type, OptionOperandType) and
            # grd_inc
            isinstance(grd_inc_op.op_type, OptionOperandType)
        )
        if not exp_shape:
            raise RuntimeError('Unexpected shape for bn.lid')

        grd, grs1, offset, grs1_inc, grd_inc = op_vals
        grd_val = self.get_reg('gpr', grd)
        grs1_val = self.get_reg('gpr', grs1)

        self._generic_update_for_insn(prog_insn)

        if grd_val is not None:
            self.write_reg('wdr', grd_val & 31, None, False)

        if grs1_inc:
            self._inc_gpr(grs1, grs1_val, 32, (1 << 32) - 1)
        elif grd_inc:
            self._inc_gpr(grd, grd_val, 1, 31)

    def update_for_bnsid(self, prog_insn: ProgInsn) -> None:
        '''Update model state after an BN.SID'''
        insn = prog_insn.insn
        op_vals = prog_insn.operands
        assert insn.mnemonic == 'bn.sid'
        assert len(insn.operands) == len(op_vals)

        grs1_op, grs2_op, offset_op, grs1_inc_op, grs2_inc_op = insn.operands
        exp_shape = (
            # grs1
            isinstance(grs1_op.op_type, RegOperandType) and
            grs1_op.op_type.reg_type == 'gpr' and
            not grs1_op.op_type.is_dest() and
            # grs2
            isinstance(grs2_op.op_type, RegOperandType) and
            grs2_op.op_type.reg_type == 'gpr' and
            not grs2_op.op_type.is_dest() and
            # offset
            isinstance(offset_op.op_type, ImmOperandType) and
            offset_op.op_type.signed and
            # grs1_inc
            isinstance(grs1_inc_op.op_type, OptionOperandType) and
            # grs2_inc
            isinstance(grs2_inc_op.op_type, OptionOperandType)
        )
        if not exp_shape:
            raise RuntimeError('Unexpected shape for bn.sid')

        grs1, grs2, offset, grs1_inc, grs2_inc = op_vals
        grs1_val = self.get_reg('gpr', grs1)
        grs2_val = self.get_reg('gpr', grs2)

        self._generic_update_for_insn(prog_insn)

        if grs1_inc:
            self._inc_gpr(grs1, grs1_val, 32, (1 << 32) - 1)
        elif grs2_inc:
            self._inc_gpr(grs2, grs2_val, 1, 31)

    def update_for_bnmovr(self, prog_insn: ProgInsn) -> None:
        '''Update model state after an BN.MOVR'''
        insn = prog_insn.insn
        op_vals = prog_insn.operands
        assert insn.mnemonic == 'bn.movr'
        assert len(insn.operands) == len(op_vals)

        grd_op, grs_op, grd_inc_op, grs_inc_op = insn.operands
        exp_shape = (
            # grd
            isinstance(grd_op.op_type, RegOperandType) and
            grd_op.op_type.reg_type == 'gpr' and
            not grd_op.op_type.is_dest() and
            # grs
            isinstance(grs_op.op_type, RegOperandType) and
            grs_op.op_type.reg_type == 'gpr' and
            not grs_op.op_type.is_dest() and
            # grd_inc
            isinstance(grd_inc_op.op_type, OptionOperandType) and
            # grs_inc
            isinstance(grs_inc_op.op_type, OptionOperandType)
        )
        if not exp_shape:
            raise RuntimeError('Unexpected shape for bn.movr')

        grd, grs, grd_inc, grs_inc = op_vals
        grd_val = self.get_reg('gpr', grd)
        grs_val = self.get_reg('gpr', grs)

        self._generic_update_for_insn(prog_insn)

        if grd_val is not None:
            self.write_reg('wdr', grd_val & 31, None, False)

        if grd_inc:
            self._inc_gpr(grd, grd_val, 1, 31)
        elif grs_inc:
            self._inc_gpr(grs, grs_val, 1, 31)

    def _generic_update_for_insn(self, prog_insn: ProgInsn) -> None:
        '''Update registers and memory for prog_insn

        Apply side-effecting reads (relevant for x1) then mark any destination
        operand as having an architectural value. Finally, apply any memory
        changes.

        This is called by update_for_insn, either by the specialized updater if
        there is one or on its own if there's none.

        '''
        seen_writes = []  # type: List[Tuple[str, int]]
        seen_reads = set()  # type: Set[Tuple[str, int]]
        insn = prog_insn.insn
        assert len(insn.operands) == len(prog_insn.operands)
        for operand, op_val in zip(insn.operands, prog_insn.operands):
            op_type = operand.op_type
            if isinstance(op_type, RegOperandType):
                if op_type.is_dest():
                    seen_writes.append((op_type.reg_type, op_val))
                else:
                    seen_reads.add((op_type.reg_type, op_val))
        for op_reg_type, op_val in seen_reads:
            self.read_reg(op_reg_type, op_val)
        for reg_type, op_val in seen_writes:
            self.write_reg(reg_type, op_val, None, False)

        # If this is an LSU operation, we've either loaded a value (in which
        # case, the memory hopefully had a value already) or we've stored
        # something. In either case, we mark the memory as having a value now.
        if prog_insn.lsu_info is not None:
            assert insn.lsu is not None
            mem_type, addr = prog_insn.lsu_info
            self.touch_mem(mem_type, addr, insn.lsu.idx_width)

    def consume_fuel(self) -> None:
        '''Consume one item of fuel, but bottom out at fuel == 1'''
        self.fuel = max(1, self.fuel - 1)

    def update_for_insn(self, prog_insn: ProgInsn) -> None:
        # If this is a sufficiently simple operation that we understand the
        # result, or a complicated instruction where we have to do something
        # clever, actually set the destination register with a value.
        updaters = {
            'lui': self.update_for_lui,
            'addi': self.update_for_addi,
            'bn.lid': self.update_for_bnlid,
            'bn.sid': self.update_for_bnsid,
            'bn.movr': self.update_for_bnmovr
        }
        updater = updaters.get(prog_insn.insn.mnemonic)
        if updater is not None:
            updater(prog_insn)
        else:
            self._generic_update_for_insn(prog_insn)

        self.consume_fuel()
