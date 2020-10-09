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
import logging
import random
import textwrap
import sys

MAX_DRAWS = 10000
MAX_RESTARTS = 10000
USAGE = "./sparse-fsm-encode -m <#states> -n <#bits> -d <minimum HD> -s <seed>"


def wrapped_docstring():
    '''Return a text-wrapped version of the module docstring'''
    paras = []
    para = []
    for line in __doc__.strip().split('\n'):
        line = line.strip()
        if not line:
            if para:
                paras.append('\n'.join(para))
                para = []
        else:
            para.append(line)
    if para:
        paras.append('\n'.join(para))

    return '\n\n'.join(textwrap.fill(p) for p in paras)


def main():
    logging.basicConfig(level=logging.INFO,
                        format="%(asctime)s - %(message)s",
                        datefmt="%Y-%m-%d %H:%M")

    parser = argparse.ArgumentParser(
        prog="sparse-fsm-encode",
        description=wrapped_docstring(),
        usage=USAGE,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('-d',
                        type=int,
                        default=5,
                        help='Minimum Hamming distance between encoded states.')
    parser.add_argument('-m',
                        type=int,
                        default=7,
                        help='Number of states to encode.')
    parser.add_argument('-n',
                        type=int,
                        default=10,
                        help='Encoding length [bit].')
    parser.add_argument('-s',
                        type=int,
                        help='Custom seed for RNG.')

    args = parser.parse_args()

    if args.m > 2**args.n:
        logging.error(
            'Statespace 2^%d not large enough to accommodate %d states.' %
            (args.n, args.m))
        sys.exit(1)

    if args.d >= args.n:
        logging.error(
            'State is only %d bits wide, which is not enough to fulfill a '
            'minimum Hamming distance constraint of %d. ' %
            (args.n, args.d))
        sys.exit(1)

    if args.d <= 0:
        logging.error(
            'Hamming distance must be > 0.')
        sys.exit(1)

    if args.d < 3:
        logging.warning(
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
    encodings = [random.getrandbits(args.n)]
    while len(encodings) < args.m:
        # if we iterate for too long, start over.
        if num_draws >= MAX_DRAWS:
            num_draws = 0
            num_restarts += 1
            encodings = [random.getrandbits(args.n)]
        # if we restarted for too many times, abort.
        if num_restarts >= MAX_RESTARTS:
            logging.error(
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
        c = random.getrandbits(args.n)
        # disallow all-zero and all-one states
        pop_cnt = bin(c).count('1')
        if pop_cnt < args.n and pop_cnt > 0:
            for k in encodings:
                if bin(c ^ k).count('1') < args.d:
                    break
            else:
                encodings.append(c)

    # build Hamming distance histogram
    minimum = args.n
    maximum = 0
    hist = [0] * (args.n + 1)
    for i, j in enumerate(encodings):
        if i < len(encodings) - 1:
            for k in encodings[i + 1:]:
                dist = bin(j ^ k).count('1')
                hist[dist] += 1
                minimum = min(dist, minimum)
                maximum = max(dist, maximum)

    print("------------------------------------------------------\n"
          "| COPY PASTE THE CODE TEMPLATE BELOW INTO YOUR RTL   |\n"
          "| IMPLEMENTATION, INLUDING THE COMMENT AND PRIM_FLOP |\n"
          "| IN ORDER TO EASE AUDITABILITY AND REPRODUCIBILITY. |\n"
          "------------------------------------------------------\n\n"
          "// Encoding generated with ./sparse-fsm-encode.py -d {} -m {} -n {} -s {}\n"
          "// Hamming distance histogram:\n"
          "//".format(args.d, args.m, args.n, args.s))
    for i, j in enumerate(hist):
        hist_bar = "// {}: ".format(i)
        for k in range(len(str(args.m)) - len(str(i))):
            hist_bar += " "
        for k in range(j * 20 // max(hist)):
            hist_bar += "|"
        hist_bar += " ({:.2f}%)".format(100.0 * j / sum(hist)) if j else "--"
        print(hist_bar)
    print("//\n"
          "// Minimum Hamming distance: {}\n"
          "// Maximum Hamming distance: {}\n"
          "//\n"
          "localparam int StateWidth = {};\n"
          "typedef enum logic [StateWidth-1:0] {{".format(minimum, maximum, args.n))
    fmt_str = "  State{0:} {1:}= {2:}'b{3:0" + str(args.n) + "b}"
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
prim_flop #(
  .Width(StateWidth),
  .ResetValue(StateWidth'(State0))
) u_state_regs (
  .clk_i,
  .rst_ni,
  .d_i ( state_d ),
  .q_o ( state_q )
);
'''.format(state_str))


if __name__ == "__main__":
    main()
