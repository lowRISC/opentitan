#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Note: this script relies on numpy and matplotlib, which both currently are
# not standard python requirements of OpenTitan. If you wish to use this script,
# make sure you install them with "pip3 install --user numpy matplotlib"

import argparse
import re
import sys
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np

USAGE = """
This script parses reports generated with the sweep.tcl DC synthesis
script and creates an AT-plot with that data.

usage: ./at-plot.py ./REPORTS/<dut1_basename> ./REPORTS/<dut2_basename> ...

In order to get convert area into gate equivalents (GE) the size of a GE
can be supplied using the -g switch.

The script currently supports plotting up to 10 different result series in
one plot.
"""


def main():
    parser = argparse.ArgumentParser(prog="")
    parser.add_argument('result_series',
                        type=str,
                        nargs='+',
                        help="Path and basename of result series.")

    parser.add_argument(
        '-g',
        '--gate_equivalent',
        type=float,
        default=1.0,
        help="Gate equivalent in square micrometre. Defaults to 1.0.")
    parser.add_argument('-o',
                        '--output',
                        type=str,
                        default="at-plot.png",
                        help='Filename of at plot. Defaults to "at-plot.png"')
    parser.add_argument('-t',
                        '--title',
                        type=str,
                        default="AT Plot",
                        help='Title of AT plot.')
    parser.add_argument('-l',
                        '--labels',
                        type=str,
                        default="",
                        help='Comma separated labels for plots.')
    parser.add_argument('--semilogy',
                        action='store_true',
                        help='semilogy plot.')

    l = 0
    labels = []

    # line style and color setup
    linestyles = ['--', '--', '--', '--', '--', '--', '--', '--', '--', '--']
    markers = ['^', 'd', '.', '*', '>', '<', 'v', 's', 'h', 'o']
    cmap = plt.get_cmap("Set1")

    args = parser.parse_args()

    if len(args.result_series) > 10:
        print("Only up to ten result series can be plottet at once")
        sys.exit(1)

    print("Gate Equivalent is %.2f square micrometre" % args.gate_equivalent)

    for basename in args.result_series:
        report_filebase = Path(basename)

        print("%s" % (report_filebase.name))

        results = np.array([[]])

        for rpt_area in report_filebase.parent.rglob(report_filebase.name +
                                                     '_*_area.rpt'):
            tmp_period = Path(rpt_area).name.split('_area')
            tmp_period = tmp_period[0].split(report_filebase.name + '_')
            row = np.array([[float(tmp_period[1]), 0.0, 0.0]])
            if np.any(results):
                results = np.append(results, row, axis=0)
            else:
                results = row
            try:
                with open(rpt_area, 'r') as f:
                    full_file = f.read()
                    tmp_area = re.findall(r"^Total cell area:.*",
                                          full_file,
                                          flags=re.MULTILINE)
                    if tmp_area:
                        tmp_area = tmp_area[0].split("Total cell area:")
                        results[-1, 1] = float(
                            tmp_area[1]) / args.gate_equivalent
                    else:
                        print("Error, could not find total cell area in %s" %
                              (report_area))
                        sys.exit(1)

            except IOError as e:
                print(str(e))
                sys.exit(1)

            try:
                rpt_timing = rpt_area.parent.joinpath(
                    rpt_area.name.replace('_area', '_timing'))
                with open(rpt_timing, 'r') as f:
                    full_file = f.read()
                    tmp_slack = re.findall(r"^  slack \(.*",
                                           full_file,
                                           flags=re.MULTILINE)
                    if tmp_slack:
                        tmp_slack = tmp_slack[0].split(")")
                        # adjust period with slack
                        results[-1, 2] = results[-1][0] - float(tmp_slack[1])
                    else:
                        print("Error, could not find slack in %s" %
                              (rpt_timing))
                        sys.exit(1)

            except IOError as e:
                print(str(e))
                sys.exit(1)

        if np.any(results):

            results = results[np.argsort(results[:, 0])]

            if args.gate_equivalent == 1.0:
                print("constraint [ns], achieved [ns], complexity [GE]")
            else:
                print("constraint [ns], achieved [ns], complexity [um^2]")

            for k in range(len(results)):
                print("%.2f, %.2f, %.2f" %
                      (results[k][0], results[k][2], results[k][1]))
            if args.semilogy:
                plt.semilogy(results[:, 2],
                             results[:, 1],
                             color=cmap(l),
                             linestyle=linestyles[l],
                             marker=markers[l],
                             linewidth=1.5,
                             markersize=6,
                             markeredgecolor='k')
            else:
                plt.plot(results[:, 2],
                         results[:, 1],
                         color=cmap(l),
                         linestyle=linestyles[l],
                         marker=markers[l],
                         linewidth=1.5,
                         markersize=6,
                         markeredgecolor='k')

            l += 1
            labels += [report_filebase.name]

    print("Parsed %d result series" % l)

    plt.xlabel('Period [ns]')
    if args.gate_equivalent == 1.0:
        plt.ylabel('Complexity [um^2]')
    else:
        plt.ylabel('Complexity [GE]')
    plt.grid(which='both')
    if args.labels:
        plt.legend(args.labels.split(','))
    else:
        plt.legend(labels)
    plt.title(args.title)
    plt.savefig(args.output)
    plt.show()


if __name__ == '__main__':
    main()
