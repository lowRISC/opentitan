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

from lib.common import hd_histogram, wrapped_docstring

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


def hw(x: int):
    '''calculate Hamming weight'''
    hw = 0
    while x != 0:
        hw += x & 1
        x >>= 1
    return hw


def minhd_method(bits: int, count: int, min_hd: int):
    '''Generates `count` `bits`-bit hardended enum constants.

    This method draws new enum candidates at random and checks whether the
    candidate fulfills the Hamming distance constraints with respect to all
    other enum values.

    Other solutions that use a brute-force approach would be possible as well
    (see e.g. https://math.stackexchange.com/
    questions/891528/generating-a-binary-code-with-maximized-hamming-distance).
    However, due to the sparse nature of the state space, this probabilistic
    heuristic works pretty well for most practical cases, and it scales
    favorably to large N.

    This method produces an asymmetric distribution due to the one-sided
    pruning. However, it may be a bit easier to parameterize for low
    bitwidths that need a guaranteed minimum Hamming distance (e.g. for
    hardware FSMs up to 16bit).
    '''
    max_val = (1 << bits) - 1
    num_draws = 0
    num_restarts = 0
    enum = []
    while len(enum) < count:
        # if we iterate for too long, start over.
        if num_draws >= MAX_DRAWS:
            num_draws = 0
            num_restarts += 1
            enum = []
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
        # draw a candidate and check whether it fulfills the minimum
        # distance requirement with respect to other enum.
        e1 = random.getrandbits(bits)
        num_draws += 1
        # disallow all-zero and all-one states
        if e1 == 0 or e1 == max_val:
            continue
        for e2 in enum:
            # disallow candidates that are the complement of other states
            if e1 == ~e2:
                break
            # disallow candidates that are too close to other states
            if hw(e1 ^ e2) < min_hd:
                break
        else:
            enum.append(e1)
    return enum


def avghd_method(bits: int, count: int, avg_hd: int, max_dev: int):
    '''Generates `count` `bits`-bit hardended enum constants.

    This method constructs new candidates by drawing a random bitmask with
    Hamming weight `avg_hd` and XOR'ing that mask onto a common seed value.
    The constructed candidates are then tested against the Hamming distance
    constraints.

    This method is similar to the minhd method, but due to the way the
    candidates are constructed and pruned, this method produces a symmetric
    distribution around the average Hamming distance midpoint.

    This method may be preferrable to create software constants with large
    bitwidths (e.g. 16 or 32bit) where a symmetric distribution is desired.
    '''
    max_val = (1 << bits) - 1
    num_draws = 0
    max_draws = MAX_DRAWS * MAX_RESTARTS
    seed = random.getrandbits(bits)
    enum = [seed]
    indices = list(range(0, bits))
    for _ in range(1, count):
        while True:
            # if we restarted for too many times, abort.
            if num_draws >= max_draws:
                log.error(
                    'Did not find a solution after drawing {} times. This is '
                    'an indicator that not many (or even no) solutions exist for '
                    'the current parameterization. Rerun the script and/or adjust '
                    'the d/m/n parameters. E.g. make the state space more sparse by '
                    'increasing n, or lower the minimum Hamming distance threshold d.'
                    .format(num_draws))
                sys.exit(1)

            random.shuffle(indices)
            num_draws += 1
            mask = 0
            for i in indices[:avg_hd]:
                mask |= 1 << i
            e1 = seed ^ mask
            # disallow all-zero and all-one states
            if e1 == 0 or e1 == max_val:
                continue
            for e2 in enum:
                # disallow candidates that are the complement of other states
                if e1 == ~e2:
                    break
                # constrain HD to be within a certain range around the average
                if max_dev and abs(hw(e1 ^ e2) - avg_hd) > max_dev:
                    break
            else:
                enum.append(e1)
                break
    return enum


def main():
    log.basicConfig(level=log.INFO,
                    format="%(levelname)s: %(message)s")

    parser = argparse.ArgumentParser(
        prog="sparse-fsm-encode",
        description=wrapped_docstring(),
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--count', '-m',
                        type=int,
                        default=7,
                        help='Number of states to encode.')
    parser.add_argument('--bits', '-n',
                        type=int,
                        default=10,
                        help='Encoding length [bit].')
    parser.add_argument('--seed', '-s',
                        type=int,
                        help='Custom seed for PRNG.')
    parser.add_argument('--min-hd', '-d',
                        type=int,
                        default=5,
                        help='Minimum Hamming distance constraint for the minhd method.')
    parser.add_argument('--avg-hd',
                        type=int,
                        help='''
                        Average Hamming distance constraint for the avghd method.
                        Defaults to bits/2.''')
    parser.add_argument('--max-dev',
                        type=int,
                        help='''
                        Maximum deviation from average Hamming distance for the avghd method.
                        ''')
    parser.add_argument('--method',
                        choices=['minhd', 'avghd'],
                        default='minhd',
                        help='Choose the method to generate the enum.')
    parser.add_argument('--language',
                        choices=['sv', 'c', 'rust'],
                        default='sv',
                        help='Choose the language of the generated enum.')

    args = parser.parse_args()

    if args.language in ['c', 'rust']:
        if args.bits not in [8, 16, 32]:
            log.error(
                "When using C or Rust, widths must be a power-of-two "
                "at least a byte (8 bits) wide. You chose %d." % (args.bits, ))
            sys.exit(1)

    if args.count < 2:
        log.error(
            'Number of states %d must be at least 2.' % (args.count))
        sys.exit(1)

    if args.count > 2**args.bits:
        log.error(
            'Statespace 2^%d not large enough to accommodate %d states.' %
            (args.bits, args.count))
        sys.exit(1)

    # If no seed has been provided, we choose a seed and print it
    # into the generated output later on such that this run can be
    # reproduced.
    if args.seed is None:
        random.seed()
        args.seed = random.getrandbits(32)

    random.seed(args.seed)

    # Select method to use and perform some more argument checking.
    if args.method == 'minhd':
        if args.min_hd < 3:
            log.warning(
                'A value of 4-5 is recommended for the minimum Hamming distance '
                'constraint. At a minimum, this should be set to 3.')
        if (args.min_hd >= args.bits) and not(args.min_hd == args.bits and args.count == 2):
            log.error(
                'State is only %d bits wide, which is not enough to fulfill a '
                'minimum Hamming distance constraint of %d. ' % (args.bits, args.min_hd))
            sys.exit(1)
        if args.min_hd <= 0:
            log.error('Hamming distance must be > 0.')
            sys.exit(1)

        # This is used in the templates below.
        argstring = f"--min-hd {args.min_hd}"

        enum = minhd_method(args.bits, args.count, args.min_hd)

    elif args.method == 'avghd':
        args.avg_hd = args.avg_hd or (args.bits // 2)

        if (args.avg_hd >= args.bits) and not(args.avg_hd == args.bits and args.count == 2):
            log.error(
                'State is only %d bits wide, which is not enough to fulfill a '
                'Hamming distance constraint of %d. ' % (args.bits, args.avg_hd))
            sys.exit(1)
        if args.avg_hd <= 0:
            log.error('Hamming distance must be > 0.')
            sys.exit(1)

        # This is used in the templates below.
        argstring = f"--avg-hd {args.avg_hd}"
        if args.max_dev is not None:
            argstring += f" --max-dev {args.max_dev}"

        enum = avghd_method(args.bits, args.count, args.avg_hd, args.max_dev)
    else:
        assert(False)

    # Convert to binary strings and get Hamming distance statistics.
    encodings = [f'{x:0{args.bits}b}' for x in enum]
    stats = hd_histogram(encodings)

    if args.language == "sv":
        print(SV_INSTRUCTIONS)
        print("// Encoding generated with:\n"
              "// $ ./util/design/sparse-fsm-encode.py --count {} --bits {} \\\n"
              "//     {} --method {} --seed {} --language=sv\n"
              "//\n"
              "// Hamming distance histogram:\n"
              "//".format(args.count, args.bits, argstring, args.method, args.seed))
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
                  stats['max_hw'], args.bits))
        fmt_str = "  State{} {}= {}'b{}"
        state_str = ""
        for j, k in enumerate(encodings):
            pad = ""
            for i in range(len(str(args.count)) - len(str(j))):
                pad += " "
            comma = "," if j < len(encodings) - 1 else ""
            print(fmt_str.format(j, pad, args.bits, k) + comma)
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
              " * $ ./util/design/sparse-fsm-encode.py --count {} --bits {} \\\n"
              " *     {} --method {} --seed {} --language=c\n"
              " *\n"
              " * Hamming distance histogram:\n"
              " *".format(args.count, args.bits, argstring, args.method, args.seed))
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
            args.bits / 4)) + "x}"
        for j, k in enumerate(encodings):
            pad = ""
            for i in range(len(str(args.count)) - len(str(j))):
                pad += " "
            print(fmt_str.format(j, pad, args.bits, int(k, 2)) + ",")

        # print FSM template
        print("} my_state_t;")
    elif args.language == 'rust':
        print(RUST_INSTRUCTIONS)
        print("///```text\n"
              "/// Encoding generated with\n"
              "/// $ ./util/design/sparse-fsm-encode.py --count {} --bits {} \\\n"
              "///     {} --method {} --seed {} --language=rust\n"
              "///\n"
              "/// Hamming distance histogram:\n"
              "///".format(args.count, args.bits, argstring, args.method, args.seed))
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
                                       args.bits))
        fmt_str = "  const MY_STATE{0:}: MyState {1:}= MyState(0x{3:0" + str(
            math.ceil(args.bits / 4)) + "x})"
        for j, k in enumerate(encodings):
            pad = ""
            for i in range(len(str(args.count)) - len(str(j))):
                pad += " "
            print(fmt_str.format(j, pad, args.bits, int(k, 2)) + ";")
        print("}")


if __name__ == "__main__":
    main()
