#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""This script generates sparse FSM encodings that fulfill a minimum
Hamming distance requirement. It uses a heuristic that incrementally
draws random state encodings until a solution has been found.

Depending on the parameterization, the script may not find a solution right
away. In such cases, the script should be rerun after tweaking the d/m/n
parameters. E.g. in order to increase the chances for success, the state
space can be made more sparse by increasing n, or the Hamming distance
threshold d can be lowered.

Note however that the Hamming distance d should be set to 3 at minimum.
It is recommended to set this value to 4-5 for security critical FSMs.

The custom seed s can be used to make subsequent runs of the script
deterministic. If not specified, the script randomly picks a seed.

"""
import argparse
import logging as log
import math
import random
import sys

from lib.common import get_hd, hd_histogram, wrapped_docstring

MAX_DRAWS = 10000
MAX_RESTARTS = 10000

SV_INSTRUCTIONS = """
------------------------------------------------------
| COPY PASTE THE CODE TEMPLATE BELOW INTO YOUR RTL   |
| IMPLEMENTATION, INLUDING THE COMMENT AND PRIM_FLOP |
| IN ORDER TO EASE AUDITABILITY AND REPRODUCIBILITY. |
------------------------------------------------------
"""

C_INSTRUCTIONS = """
------------------------------------------------
| COPY PASTE THE CODE TEMPLATE BELOW INTO YOUR |
| C HEADER, INLUDING THE COMMENT IN ORDER TO   |
| EASE AUDITABILITY AND REPRODUCIBILITY.       |
------------------------------------------------
"""

RUST_INSTRUCTIONS = """
------------------------------------------------
| COPY PASTE THE CODE TEMPLATE BELOW INTO YOUR |
| RUST FILE, INLUDING THE COMMENT IN ORDER TO  |
| EASE AUDITABILITY AND REPRODUCIBILITY.       |
------------------------------------------------
"""


class EncodingGenerator:

    def __init__(self, min_hd: int, num_states: int, encoding_len: int,
                 seed: int, language: str,
                 avoid_zero: bool) -> "EncodingGenerator":
        self.encodings = []
        self.num_states = num_states
        self.encoding_len = encoding_len
        self.seed = seed
        self.avoid_zero = avoid_zero
        self.language = language
        self.min_hd = min_hd
        self.min_popcnt = min_hd if self.avoid_zero else 1

    def _check_candidate(self, cand: str) -> bool:
        """Check that a candidate integer satisfies the requirements."""
        # disallow all-zero and all-one states
        pop_cnt = cand.count('1')
        if pop_cnt >= self.encoding_len or pop_cnt < self.min_popcnt:
            return False
        for k in self.encodings:
            # disallow candidates that are the complement of other states
            # The ~ operator cannot be used here as it returns a 2's complement
            # result. XOR with 1's instead to invert the bits.
            if int(cand, 2) ^ ((1 << self.encoding_len) - 1) == int(k, 2):
                return False
            # disallow candidates that are too close to other states
            if get_hd(cand, k) < self.min_hd:
                return False
        return True

    def generate(self) -> None:
        """Generate encodings satisfying the desired constraints.

        This is a heuristic that opportunistically draws random state encodings
        and check whether they fulfill the minimum Hamming distance constraint.
        Other solutions that use a brute-force approach would be possible as
        well (see e.g. https://math.stackexchange.com/
        questions/891528/generating-a-binary-code-with-maximized-hamming-distance).
        However, due to the sparse nature of the state space, this
        probabilistic heuristic works pretty well for most practical cases, and
        it scales favorably to large N.
        """
        num_draws = 0
        num_restarts = 0

        rand = random.Random()
        rand.seed(self.seed)
        rnd = rand.getrandbits(self.encoding_len)

        while len(self.encodings) < self.num_states:
            # if we iterate for too long, start over.
            if num_draws >= MAX_DRAWS:
                num_draws = 0
                num_restarts += 1
                rnd = rand.getrandbits(self.encoding_len)
                self.encodings = []
            # if we restarted for too many times, abort.
            if num_restarts >= MAX_RESTARTS:
                log.error(
                    f'Did not find a solution after restarting {num_restarts} times. '
                    'This is an indicator that not many (or even no) solutions exist for '
                    'the current parameterization. Rerun the script and/or adjust '
                    'the d/m/n parameters. E.g. make the state space more sparse by '
                    'increasing n, or lower the minimum Hamming distance threshold d.'
                )
                sys.exit(1)
            num_draws += 1
            # draw a candidate and check whether it fulfills the minimum
            # distance requirement with respect to other encodings.
            rnd = rand.getrandbits(self.encoding_len)
            cand = format(rnd, '0' + str(self.encoding_len) + 'b')
            if self._check_candidate(cand):
                self.encodings.append(cand)

        # Get Hamming distance statistics.
        self.stats = hd_histogram(self.encodings)

    def _print_comment(self):
        if self.language == "c":
            comment = " *"
            print(C_INSTRUCTIONS)
            print("/*")
        elif self.language == "sv":
            comment = "//"
            print(SV_INSTRUCTIONS)
        elif self.language == "rust":
            comment = "///"
            print(RUST_INSTRUCTIONS)
            print("///```text")
        else:
            raise ValueError(f"Unsupported language: {self.lanugage}")

        print(
            f"{comment} Encoding generated with:\n"
            f"{comment} $ ./util/design/sparse-fsm-encode.py -d {self.min_hd} -m {self.num_states} -n {self.encoding_len} \\\n"  # noqa: E501
            f"{comment}     -s {self.seed} --language={self.language}\n"
            f"{comment}\n"
            f"{comment} Hamming distance histogram:\n"
            f"{comment}")
        for hist_bar in self.stats['bars']:
            print(f"{comment} " + hist_bar)
        print(f"{comment}\n"
              f"{comment} Minimum Hamming distance: {self.stats['min_hd']}\n"
              f"{comment} Maximum Hamming distance: {self.stats['max_hd']}\n"
              f"{comment} Minimum Hamming weight: {self.stats['min_hw']}\n"
              f"{comment} Maximum Hamming weight: {self.stats['max_hw']}")

        # Print comment footer
        if self.language == "c":
            print(" */")
        elif self.language == "rust":
            print("///```")
        elif self.language == "sv":
            print("//")

    def _print_sv(self):
        print(f"localparam int StateWidth = {self.encoding_len};\n"
              "typedef enum logic [StateWidth-1:0] {")
        fmt_str = "  State{} {}= {}'b{}"
        state_str = ""
        for j, k in enumerate(self.encodings):
            pad = " " * (len(str(self.num_states)) - len(str(j)))
            comma = "," if j < len(self.encodings) - 1 else ""
            print(fmt_str.format(j, pad, self.encoding_len, k) + comma)
            state_str += f"    State{j}: ;\n"

        # print FSM template
        print(
            "} state_e;\n"
            "\n"
            "state_e state_d, state_q;\n\n"
            "always_comb begin : p_fsm\n"
            "  // Default assignments\n"
            "  state_d = state_q;\n"
            "\n"
            "  unique case (state_q)\n"
            f"{state_str}    default: ; // Consider triggering an error or alert in this case.\n"
            "  endcase\n"
            "end\n"
            "\n"
            "`PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, state_e, State0)"
        )

    def _print_c(self):
        print("typedef enum my_state {")
        fmt_str = "  kMyState{0:} {1:}= 0x{3:0" + str(
            math.ceil(self.encoding_len / 4)) + "x},"
        for j, k in enumerate(self.encodings):
            pad = " " * (len(str(self.num_states)) - len(str(j)))
            print(fmt_str.format(j, pad, self.encoding_len, int(k, 2)))

        # print FSM template
        print("} my_state_t;")

    def _print_rust(self):
        print("#[derive(Clone,Copy,Eq,PartialEq,Ord,ParitalOrd,Hash,Debug)]\n"
              "#[repr(transparent)]\n"
              f"struct MyState(u{self.encoding_len});\n"
              "\n"
              "impl MyState {")
        fmt_str = "  const MY_STATE{0:}: MyState {1:}= MyState(0x{3:0" + str(
            math.ceil(self.encoding_len / 4)) + "x});"
        for j, k in enumerate(self.encodings):
            pad = " " * (len(str(self.num_states)) - len(str(j)))
            print(fmt_str.format(j, pad, self.encoding_len, int(k, 2)))
        print("}")

    def print_code(self):
        self._print_comment()
        if self.language == "sv":
            self._print_sv()
        elif self.language == "c":
            self._print_c()
        elif self.language == 'rust':
            self._print_rust()


def main():
    log.basicConfig(level=log.INFO, format="%(levelname)s: %(message)s")

    parser = argparse.ArgumentParser(
        prog="sparse-fsm-encode",
        description=wrapped_docstring(),
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument(
        '-d',
        type=int,
        default=5,
        metavar='<minimum HD>',
        help='Minimum Hamming distance between encoded states.')
    parser.add_argument('-m',
                        type=int,
                        default=7,
                        metavar='<#states>',
                        help='Number of states to encode.')
    parser.add_argument('-n',
                        type=int,
                        default=10,
                        metavar='<#nbits>',
                        help='Encoding length [bit].')
    parser.add_argument('-s',
                        type=int,
                        metavar='<seed>',
                        help='Custom seed for RNG.')
    parser.add_argument('--language',
                        choices=['sv', 'c', 'rust'],
                        default='sv',
                        help='Choose the language of the generated enum.')
    parser.add_argument('--avoid-zero',
                        action='store_true',
                        help=('Also enforce a minimum hamming '
                              'distance from the zero word.'))

    args = parser.parse_args()

    if args.language in ['c', 'rust']:
        if args.n not in [8, 16, 32]:
            log.error("When using C or Rust, widths must be a power-of-two "
                      f"at least a byte (8 bits) wide. You chose {args.n}.")
            sys.exit(1)

    if args.m < 2:
        log.error('Number of states (m) must be at least 2.')
        sys.exit(1)

    if args.m > 2**args.n:
        log.error(
            f'Statespace 2^{args.n} not large enough to accommodate {args.m} states.'
        )
        sys.exit(1)

    if (args.d >= args.n) and not (args.d == args.n and args.m == 2):
        log.error(
            f'State is only {args.n} bits wide, which is not enough to fulfill a '
            f'minimum Hamming distance constraint of {args.d}.')
        sys.exit(1)

    if args.d <= 0:
        log.error('Hamming distance must be > 0.')
        sys.exit(1)

    if args.d < 3:
        log.warning(
            'A value of 4-5 is recommended for the minimum Hamming distance '
            'constraint. At a minimum, this should be set to 3.')

    # If no seed has been provided, we choose a seed and print it
    # into the generated output later on such that this run can be
    # reproduced.
    if args.s is None:
        random.seed()
        args.s = random.getrandbits(32)

    generator = EncodingGenerator(min_hd=args.d,
                                  num_states=args.m,
                                  encoding_len=args.n,
                                  seed=args.s,
                                  language=args.language,
                                  avoid_zero=args.avoid_zero)
    generator.generate()
    generator.print_code()


if __name__ == "__main__":
    main()
