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

import hjson


def extract_messages(full_file, patterns, results):
    """
    This extracts messages from the sting buffer full_file.
    The argument patterns needs to be a list of tuples with
    (<error_severity>, <pattern_to_match_for>).
    """
    for severity, pattern in patterns:
        results[severity] += re.findall(pattern, full_file, flags=re.MULTILINE)

    return results


def get_results(resdir):
    """
    Parse report and corresponding logfiles and extract error, warning
    and info messages for each IP present in the result folder
    """
    results = {
        "tool": "ascentlint",
        "fusesoc-error": [],
        "errors": [],
        "warnings": [],
        "lint_errors": [],
        "lint_warnings": [],
        "lint_infos": []
    }

    log_files = [
        'ascentlint.log', 'lint-ascentlint/ascentlint.log',
        'lint-ascentlint/ascentlint.rpt'
    ]
    log_file_contents = []
    # Open all log files
    for name in log_files:
        try:
            with Path(resdir).joinpath(name).open() as f:
                log_file_contents.append(f.read())
        except IOError as err:
            results["errors"] += ["IOError: %s" % err]

    # Define warning/error patterns for each logfile
    err_warn_patterns = []

    # Patterns for lint.log
    err_warn_patterns.append([
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
         r"^ERROR: Failed to build .* : 'make' exited with an error code")
    ])

    # Patterns for ascentlint.log
    err_warn_patterns.append([
        ("errors", r"^FlexNet Licensing error.*"),
        ("errors", r"^Error: .*"),
        ("errors", r"^ERROR.*"),
        ("errors", r"^  ERR .*"),
        ("warnings", r"^Warning: .*"),
        # TODO: struct assignment labels within concatenation
        # not supported. check with newer ascentlint version.
        ("warnings", r"^  (?!WARN \[#39024\])WARN .*")
    ])

    # Patterns for ascentlint.rpt
    err_warn_patterns.append([("lint_errors", r"^E  .*"),
                              ("lint_warnings", r"^W  .*"),
                              ("lint_infos", r"^I  .*")])

    # Go parse the logs
    for patterns, logs in zip(err_warn_patterns, log_file_contents):
        extract_messages(logs, patterns, results)

    # If there are no errors or warnings, add the "fusesoc-error" field to
    # "errors" (which will be reported as tooling errors). Remove the
    # "fusesoc-error" field either way.
    if not (results['errors'] or results['warnings']):
        results['errors'] = results['fusesoc-error']
    del results['fusesoc-error']

    return results


def main():

    parser = argparse.ArgumentParser(
        description="""This script parses AscentLint log and report files from
        a lint run, filters the messages and creates an aggregated result
        .hjson file with the following fields:

           {"tool": "ascentlint",
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
    parser.add_argument('--repdir',
                        type=str,
                        default="./",
                        help="""The script searches the 'ascentlint.log' and
                        'ascentlint.rpt' files in this directory.
                        Defaults to './'""")

    parser.add_argument('--outdir',
                        type=str,
                        default="./",
                        help="""Output directory for the 'results.hjson' file.
                        Defaults to './'""")

    args = parser.parse_args()
    results = get_results(args.repdir)

    with Path(args.outdir).joinpath("results.hjson").open("w") as results_file:
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
