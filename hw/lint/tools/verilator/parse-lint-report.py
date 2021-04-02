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
from collections import OrderedDict
from pathlib import Path

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
        # If lint warnings have been found, the lint tool will exit
        # with a nonzero status code and fusesoc will always spit out
        # an error like
        #
        #    ERROR: Failed to build ip:core:name:0.1 : 'make' exited with an error code
        #
        # If we found any other warnings or errors, there's no point in
        # listing this too. BUT we want to make sure we *do* see this
        # error if there are no other errors or warnings, since that
        # shows something has come unstuck. (Probably the lint tool
        # spat out a warning that we don't understand)
        ("fusesoc-error",
         r"^ERROR: Failed to build .* 'make' exited with an error code"),
        ("errors",
         r"^(?!ERROR: Failed to build .* 'make' exited with an error code)ERROR: .*"
         ),
        ("errors",
         # This is a redundant Verilator error that we ignore, since we
         # already parse out each individual error.
         r"^(?!%Error: Exiting due to .* warning.*)%Error: .*"),
        # TODO(https://github.com/olofk/edalize/issues/90):
        # this is a workaround until we actually have native Edalize
        # support for JasperGold and "formal" targets
        ("warnings",
         r"^(?!WARNING: Unknown item formal in section Target)WARNING: .*"),
        ("warnings", r"^%Warning: .* "),
        ("lint_errors", r"^%Error-.*"),
        ("lint_warnings", r"^%Warning-.*"),
    }
    return extract_messages(str_buffer, err_warn_patterns)


def get_results(logpath):
    '''Parse Lint log file and extract info to a dictionary'''
    results = {
        "tool": "verilator",
        "fusesoc-error": [],
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

    # If there are no errors or warnings, add the "fusesoc-error" field to
    # "errors" (which will be reported as tooling errors). Remove the
    # "fusesoc-error" field either way.
    if not (results['errors'] or results['warnings']):
        results['errors'] = results['fusesoc-error']
    del results['fusesoc-error']

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
                        default="verilator.log",
                        help=('FPV log file path. Defaults to `lint.log` '
                              'under the current script directory.'))

    parser.add_argument(
        '--reppath',
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
        log.info("Found %d lint errors and %d lint warnings", n_errors,
                 n_warnings)
        sys.exit(1)

    log.info("Lint logfile parsed succesfully")
    sys.exit(0)


if __name__ == "__main__":
    main()
