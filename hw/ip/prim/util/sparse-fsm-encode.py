#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Script for generating sparse FSM encodings that fulfill a minimum
Hamming distance requirement.
"""
import argparse
import logging
import random
import sys

MAX_DRAWS = 10000
MAX_RESTARTS = 10000
USAGE = '''
  ./sparse-fsm-encode -d <minimum HD> -m <#states> -n <#bits>
'''


def main():
    logging.basicConfig(level=logging.INFO,
                        format="%(asctime)s - %(message)s",
                        datefmt="%Y-%m-%d %H:%M")

    parser = argparse.ArgumentParser(
        prog="sparse-fsm-encode",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        usage=USAGE)
    parser.add_argument('-d',
                        type=int,
                        default=2,
                        help='Minimum Hamming distance between encoded states.')
    parser.add_argument('-m',
                        type=int,
                        default=12,
                        help='Number of states.')
    parser.add_argument('-n',
                        type=int,
                        default=8,
                        help='Encoding length [bit].')

    args = parser.parse_args()

    if args.m > 2**args.n:
        logging.error(
            'Statespace 2^%d not large enough to accommodate %d states.' %
            (args.n, args.m))
        sys.exit(1)

    random.seed()

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
                'the D/M/N parameters. E.g. make the state space more sparse by '
                'increasing N, or lower the minimum Hamming distance threshold D.'
                .format(num_restarts))
            sys.exit(1)
        num_draws += 1
        # draw a candidate and check whether it fulfills the minimum
        # distance requirement with respect to other encodings.
        c = random.getrandbits(args.n)
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

    print("// Encoding generated with ./sparse-fsm-encode -d {} -m {} -n {}".format(args.d, args.m, args.n))
    print("// Hamming distance histogram:")
    print("// ")
    for i, j in enumerate(hist):
        hist_bar = "// {}: ".format(i)
        for k in range(len(str(args.m)) - len(str(i))):
            hist_bar += " "
        for k in range(j * 20 // max(hist)):
            hist_bar += "|"
        hist_bar += " ({:.2f}%)".format(100.0 * j / sum(hist)) if j else "--"
        print(hist_bar)
    print("// ")

    print("// Minimum Hamming distance: {}".format(minimum))
    print("// Maximum Hamming distance: {}".format(maximum))

    print("//")
    print('typedef enum logic [{}:0]'.format(args.n - 1) + ' {')
    fmt_str = "  State{0:} {1:}= {2:}'b{3:0" + str(args.n) + "b}"
    for j, k in enumerate(encodings):
        pad = ""
        for i in range(len(str(args.m)) - len(str(j))):
            pad += " "
        comma = "," if j < len(encodings) - 1 else ""
        print(fmt_str.format(j, pad, args.n, k) + comma)
    print('} state_e;')


if __name__ == "__main__":
    main()
