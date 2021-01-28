# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
from typing import List, Optional, Tuple


def _extended_euclidean_algorithm(a: int, b: int) -> Tuple[int, int, int]:
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


def _intersect_ranges(a: List[Tuple[int, int]],
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
        self.known_ranges = _intersect_ranges(self.known_ranges,
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
        gcd, x0, y0 = _extended_euclidean_algorithm(-offset_align, addr_align)
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
