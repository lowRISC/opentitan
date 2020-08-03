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
        "tool": "veriblelint",
        "errors": [],
        "warnings": [],
        "lint_errors": [],
        "lint_warnings": [],
        "lint_infos": []
    }
    try:
        # check the report file for lint INFO, WARNING and ERRORs
        with Path(resdir).joinpath('lint.log').open() as f:
            full_file = f.read()
            err_warn_patterns = {
                # The lint failed error can be ignored, since
                # Fusesoc will always return this error if lint warnings have
                # been found. We have a way of capturing the lint warnings
                # explicitly in this parsing script, hence this error is redundant
                # and we decided not to report it in the dashboard.
                ("errors",
                 r"^(?!ERROR: Failed to run .* Lint failed)ERROR: .*"),
                ("errors", r"^Error: .*"),
                ("errors", r"^E .*"),
                ("errors", r"^F .*"),
                # TODO(https://github.com/olofk/edalize/issues/90):
                # this is a workaround until we actually have native Edalize
                # support for JasperGold and "formal" targets
                ("warnings",
                 r"^(?!WARNING: Unknown item formal in section Target)WARNING: .*"
                 # TODO(https://github.com/lowRISC/ibex/issues/1033):
                 # remove once this has been fixed in Edalize or in the corefile.
                 r"^(?!WARNING: Unknown item symbiyosis in section Target)WARNING: .*"
                 ),
                ("warnings", r"^Warning: .* "),
                ("warnings", r"^W .*"),
                ("lint_warnings", r"^.*\[Style:.*")
            }
            extract_messages(full_file, err_warn_patterns, results)
    except IOError as err:
        results["errors"] += ["IOError: %s" % err]

    return results


def main():

    parser = argparse.ArgumentParser(
        description="""This script parses verible lint log files from
        a lint run, filters the messages and creates an aggregated result
        .hjson file with the following fields:

           {"tool": "veriblelint",
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
                        help="""The script searches the 'lint.log'
                        files in this directory.
                        Defaults to './'""")

    parser.add_argument('--outdir',
                        type=str,
                        default="./",
                        help="""
                        Output directory for the 'results.hjson' file.
                        Defaults to '%(default)s'""")

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
        log.info("Found %d lint errors and %d lint warnings", n_errors, n_warnings)
        sys.exit(1)

    log.info("Lint logfile parsed succesfully")
    sys.exit(0)


if __name__ == "__main__":
    main()
