#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Command-line tool to parse and process testplan Hjson

"""
import argparse
import sys

import Testplan


def main():
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('testplan',
                        metavar='<hjson-file>',
                        help='input testplan file (testplan.hjson)')
    parser.add_argument('-s',
                        '--sim_results',
                        metavar='<hjson-file>',
                        help='''input simulation results file
                        (sim_results.hjson)''')
    parser.add_argument('--outfile',
                        '-o',
                        type=argparse.FileType('w'),
                        default=sys.stdout,
                        help='output markdown file')
    args = parser.parse_args()
    outfile = args.outfile

    with outfile:
        testplan = Testplan.Testplan(args.testplan)
        if args.sim_results:
            outfile.write(
                testplan.get_sim_results(args.sim_results, fmt="html"))
        else:
            testplan.write_testplan_doc(outfile)

        outfile.write('\n')


if __name__ == '__main__':
    main()
