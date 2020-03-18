#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Parses JasperGold FPV logfile and coverage and dump filtered messages in csv format.
"""
import argparse
import os
import re
from collections import OrderedDict


def get_results(resdir):
    """
    Parse FPV log file and extract each property's verification status
    """
    results = OrderedDict()
    try:
        # check the log file for flow errors and warnings
        with open(os.path.join(resdir, "fpv.log")) as f:
            result_parse = 0
            pattern = r'\[\d+\]'
            lines = f.readlines()
            for line in lines:
                if line == "RESULTS\n":
                    result_parse = 1
                if result_parse and re.match(pattern, line):
                    split_str = line.split()
                    results[split_str[1]] = split_str[2]

    except IOError as err:
        print(err)
        results["errors"] = ["IOError: %s" % err]

    return results


def get_cov_results(resdir):
    """
    Parse FPV coverage HTML file and extract the total coverage percentage
    """
    cov_results = OrderedDict()
    cov_title = ["Stimuli", "COI", "Proof"]
    try:
        with open(os.path.join(resdir, "formal-icarus", "cover.html"),
                  "r") as f:
            lines = f.readlines()
            result_parse = 0
            percentage = re.compile(r'\d+\.\d+%')
            for line in lines:
                if result_parse:
                    value = percentage.search(line)
                    if value is not None:
                        cov_results[cov_title[result_parse - 1]] = value.group()
                        result_parse += 1
                if line == '<tr id="table1_0">\n':
                    result_parse = 1
                if result_parse == 4:
                    break

    except IOError as err:
        print(err)
        cov_results["errors"] = ["IOError: %s" % err]

    return cov_results


def main():

    parser = argparse.ArgumentParser(
        description=
        """This script parses The JasperGold FPV log and coverage files,
        The result contains each property's name and status in a CSV format.
            property1,proven
            preperty2,covered
            ...
        The coverage is extracted into a CSV summary as well.
            stimuli,100%
            COI,96%
            Proof,90%""")
    parser.add_argument('--repdir',
                        type=str,
                        default="./",
                        help="""The script searches the 'fpv.log' and
                        'cov.html' in this directory. Defaults to './'""")

    parser.add_argument(
        '--outdir',
        type=str,
        default="./",
        help="""Output directory for the 'results.csv' and 'cov.csv' files. Defaults to './'""")

    args = parser.parse_args()

    results = get_results(args.repdir)
    with open(os.path.join(args.outdir, "results.csv"), "w") as results_file:
        for key in results.keys():
            results_file.write("%s,%s\n" % (key, results[key]))

    has_cov = os.path.exists(os.path.join(args.repdir, "formal-icarus", "cover.html"))
    if has_cov:
        cov_results = get_cov_results(args.repdir)
        with open(os.path.join(args.outdir, "cov.csv"), "w") as results_file:
            for key in cov_results.keys():
                results_file.write("%s,%s\n" % (key, cov_results[key]))


if __name__ == "__main__":
    main()
