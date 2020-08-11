#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Parses lint report and dump filtered messages in hjson format.
"""
import argparse
import logging as log
import re
import sys
from pathlib import Path
from collections import OrderedDict

import hjson


def extract_messages(str_buffer, patterns):
    '''Extract messages matching patterns from str_buffer as a dictionary.

    The patterns argument is a list of pairs, (key, pattern). Each pattern is a regex
    and all matches in str_buffer are stored in a dictionary under the paired key.
    '''
    results = OrderedDict()
    for key, pattern in patterns:
        val = results.setdefault(key, [])
        val += re.findall(pattern, str_buffer, flags=re.MULTILINE)

    return results


def parse_lint_log(str_buffer):
    '''Parse error, warnings, and failed properties from the log file'''
    err_warn_patterns = {
        # The lint failed error can be ignored, since
        # Fusesoc will always return this error if lint warnings have
        # been found. We have a way of capturing the lint warnings
        # explicitly in this parsing script, hence this error is redundant
        # and we decided not to report it in the dashboard.
        ("errors",
         r"^(?!ERROR: Failed to build .* 'make' exited with an error code)ERROR: .*"),
        ("errors",
        # This is a redundant Verilator error that we ignore for the same reason as above.
         r"^(?!%Error: Exiting due to .* warning.*)%Error: .*"),
        # TODO(https://github.com/olofk/edalize/issues/90):
        # this is a workaround until we actually have native Edalize
        # support for JasperGold and "formal" targets
        ("warnings",
         r"^(?!WARNING: Unknown item formal in section Target)WARNING: .*"
         # TODO(https://github.com/lowRISC/ibex/issues/1033):
         # remove once this has been fixed in Edalize or in the corefile.
         r"^(?!WARNING: Unknown item symbiyosis in section Target)WARNING: .*"
         ),
        ("warnings", r"^%Warning: .* "),
        ("lint_errors", r"^%Error-.*"),
        ("lint_warnings", r"^%Warning-.*"),
    }
    return extract_messages(str_buffer, err_warn_patterns)


def get_results(logpath):
    '''Parse Lint log file and extract info to a dictionary'''
    results = {
        "tool": "verilator",
        "errors": [],
        "warnings": [],
        "lint_errors": [],
        "lint_warnings": [],
        "lint_infos": []
    }
    try:
        with Path(logpath).open() as f:
            str_buffer = f.read()
            results = parse_lint_log(str_buffer)
    except IOError as err:
        results["errors"] += ["IOError: %s" % err]

    return results


def main():
    parser = argparse.ArgumentParser(
        description="""This script parses verible lint log files from
        a lint run, filters the messages and creates an aggregated result
        .hjson file with the following fields:

           {"tool": "verilator",
            "errors" : [],
            "warnings" : [],
            "lint_errors" : [],
            "lint_warnings" : [],
            "lint_infos" : []}

        The fields 'errors' and 'warnings' contain file IO messages or
        messages output by the tool itself, whereas the fields prefixed with
        'lint_' contain lint-related messages.

        The script returns nonzero status if any warnings or errors are present.
        """)
    parser.add_argument('--logpath',
                        type=str,
                        default="lint.log",
                        help=('FPV log file path. Defaults to `lint.log` '
                              'under the current script directory.'))

    parser.add_argument('--reppath',
                        type=str,
                        default="results.hjson",
                        help=('Parsed output hjson file path. Defaults to '
                              '`results.hjson` under the current script directory.'))

    args = parser.parse_args()

    results = get_results(args.logpath)

    with Path(args.reppath).open("w") as results_file:
        hjson.dump(results,
                   results_file,
                   ensure_ascii=False,
                   for_json=True,
                   use_decimal=True)

    # return nonzero status if any warnings or errors are present
    # lint infos do not count as failures
    n_errors = len(results["errors"]) + len(results["lint_errors"])
    n_warnings = len(results["warnings"]) + len(results["lint_warnings"])
    if n_errors > 0 or n_warnings > 0:
        log.info("Found %d lint errors and %d lint warnings", n_errors, n_warnings)
        sys.exit(1)

    log.info("Lint logfile parsed succesfully")
    sys.exit(0)


if __name__ == "__main__":
    main()
