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


def main():
    log.basicConfig(level=log.INFO,
                    format="%(levelname)s: %(message)s")

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

    args = parser.parse_args()

    if args.language in ['c', 'rust']:
        if args.n not in [8, 16, 32]:
            log.error(
                "When using C or Rust, widths must be a power-of-two "
                "at least a byte (8 bits) wide. You chose %d." % (args.n, ))
            sys.exit(1)

    if args.m < 2:
        log.error(
            'Number of states %d must be at least 2.' % (args.m))
        sys.exit(1)

    if args.m > 2**args.n:
        log.error(
            'Statespace 2^%d not large enough to accommodate %d states.' %
            (args.n, args.m))
        sys.exit(1)

    if (args.d >= args.n) and not(args.d == args.n and args.m == 2):
        log.error(
            'State is only %d bits wide, which is not enough to fulfill a '
            'minimum Hamming distance constraint of %d. ' % (args.n, args.d))
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

    random.seed(args.s)

    # This is a heuristic that opportunistically draws random
    # state encodings and check whether they fulfill the minimum
    # Hamming distance constraint.
    # Other solutions that use a brute-force approach would be
    # possible as well (see e.g. https://math.stackexchange.com/
    # questions/891528/generating-a-binary-code-with-maximized-hamming-distance).
    # However, due to the sparse nature of the state space, this
    # probabilistic heuristic works pretty well for most practical
    # cases, and it scales favorably to large N.
    num_draws = 0
    num_restarts = 0
    rnd = random.getrandbits(args.n)
    encodings = [format(rnd, '0' + str(args.n) + 'b')]
    while len(encodings) < args.m:
        # if we iterate for too long, start over.
        if num_draws >= MAX_DRAWS:
            num_draws = 0
            num_restarts += 1
            rnd = random.getrandbits(args.n)
            encodings = [format(rnd, '0' + str(args.n) + 'b')]
        # if we restarted for too many times, abort.
        if num_restarts >= MAX_RESTARTS:
            log.error(
                'Did not find a solution after restarting {} times. This is '
                'an indicator that not many (or even no) solutions exist for '
                'the current parameterization. Rerun the script and/or adjust '
                'the d/m/n parameters. E.g. make the state space more sparse by '
                'increasing n, or lower the minimum Hamming distance threshold d.'
                .format(num_restarts))
            sys.exit(1)
        num_draws += 1
        # draw a candidate and check whether it fulfills the minimum
        # distance requirement with respect to other encodings.
        rnd = random.getrandbits(args.n)
        cand = format(rnd, '0' + str(args.n) + 'b')
        # disallow all-zero and all-one states
        pop_cnt = cand.count('1')
        if pop_cnt < args.n and pop_cnt > 0:
            for k in encodings:
                # disallow candidates that are the complement of other states
                if int(cand, 2) == ~int(k, 2):
                    break
                # disallow candidates that are too close to other states
                if get_hd(cand, k) < args.d:
                    break
            else:
                encodings.append(cand)

    # Get Hamming distance statistics.
    stats = hd_histogram(encodings)

    if args.language == "sv":
        print(SV_INSTRUCTIONS)
        print("// Encoding generated with:\n"
              "// $ ./util/design/sparse-fsm-encode.py -d {} -m {} -n {} \\\n"
              "//      -s {} --language=sv\n"
              "//\n"
              "// Hamming distance histogram:\n"
              "//".format(args.d, args.m, args.n, args.s))
        for bar in stats['bars']:
            print('// ' + bar)
        print("//\n"
              "// Minimum Hamming distance: {}\n"
              "// Maximum Hamming distance: {}\n"
              "// Minimum Hamming weight: {}\n"
              "// Maximum Hamming weight: {}\n"
              "//\n"
              "localparam int StateWidth = {};\n"
              "typedef enum logic [StateWidth-1:0] {{".format(
                  stats['min_hd'], stats['max_hd'], stats['min_hw'],
                  stats['max_hw'], args.n))
        fmt_str = "  State{} {}= {}'b{}"
        state_str = ""
        for j, k in enumerate(encodings):
            pad = ""
            for i in range(len(str(args.m)) - len(str(j))):
                pad += " "
            comma = "," if j < len(encodings) - 1 else ""
            print(fmt_str.format(j, pad, args.n, k) + comma)
            state_str += "    State{}: ;\n".format(j)

        # print FSM template
        print('''}} state_e;

state_e state_d, state_q;

always_comb begin : p_fsm
  // Default assignments
  state_d = state_q;

  unique case (state_q)
{}    default: ; // Consider triggering an error or alert in this case.
  endcase
end

// This primitive is used to place a size-only constraint on the
// flops in order to prevent FSM state encoding optimizations.
logic [StateWidth-1:0] state_raw_q;
assign state_q = state_e'(state_raw_q);
prim_flop #(
  .Width(StateWidth),
  .ResetValue(StateWidth'(State0))
) u_state_regs (
  .clk_i,
  .rst_ni,
  .d_i ( state_d     ),
  .q_o ( state_raw_q )
);
'''.format(state_str))

    elif args.language == "c":
        print(C_INSTRUCTIONS)
        print("/*\n"
              " * Encoding generated with\n"
              " * $ ./util/design/sparse-fsm-encode.py -d {} -m {} -n {} \\\n"
              " *     -s {} --language=c\n"
              " *\n"
              " * Hamming distance histogram:\n"
              " *".format(args.d, args.m, args.n, args.s))
        for hist_bar in stats['bars']:
            print(" * " + hist_bar)
        print(" *\n"
              " * Minimum Hamming distance: {}\n"
              " * Maximum Hamming distance: {}\n"
              " * Minimum Hamming weight: {}\n"
              " * Maximum Hamming weight: {}\n"
              " */\n"
              "typedef enum my_state {{".format(stats['min_hd'],
                                                stats['max_hd'],
                                                stats['min_hw'],
                                                stats['max_hw']))
        fmt_str = "  kMyState{0:} {1:}= 0x{3:0" + str(math.ceil(
            args.n / 4)) + "x}"
        for j, k in enumerate(encodings):
            pad = ""
            for i in range(len(str(args.m)) - len(str(j))):
                pad += " "
            print(fmt_str.format(j, pad, args.n, int(k, 2)) + ",")

        # print FSM template
        print("} my_state_t;")
    elif args.language == 'rust':
        print(RUST_INSTRUCTIONS)
        print("///```text\n"
              "/// Encoding generated with\n"
              "/// $ ./util/design/sparse-fsm-encode.py -d {} -m {} -n {} \\\n"
              "///     -s {} --language=rust\n"
              "///\n"
              "/// Hamming distance histogram:\n"
              "///".format(args.d, args.m, args.n, args.s))
        for hist_bar in stats['bars']:
            print("/// " + hist_bar)
        print("///\n"
              "/// Minimum Hamming distance: {}\n"
              "/// Maximum Hamming distance: {}\n"
              "/// Minimum Hamming weight: {}\n"
              "/// Maximum Hamming weight: {}\n"
              "///```\n"
              "#[derive(Clone,Copy,Eq,PartialEq,Ord,ParitalOrd,Hash,Debug)]\n"
              "#[repr(transparent)]\n"
              "struct MyState(u{});\n"
              "\n"
              "impl MyState {{".format(stats['min_hd'], stats['max_hd'],
                                       stats['min_hw'], stats['max_hw'],
                                       args.n))
        fmt_str = "  const MY_STATE{0:}: MyState {1:}= MyState(0x{3:0" + str(
            math.ceil(args.n / 4)) + "x})"
        for j, k in enumerate(encodings):
            pad = ""
            for i in range(len(str(args.m)) - len(str(j))):
                pad += " "
            print(fmt_str.format(j, pad, args.n, int(k, 2)) + ";")
        print("}")


if __name__ == "__main__":
    main()
