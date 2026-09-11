#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Parses slang lint report and dumps filtered messages in hjson format."""
import argparse
import logging as log
import sys

from pathlib import Path
from LintParser import LintParser

# TODO(#9079): this script will be removed long term once the
# parser has been merged with the Dvsim core code.


def main():
    parser = argparse.ArgumentParser(
        description="""This script parses Slang lint log and report files
        from a lint run, filters the messages and creates an aggregated result
        .hjson file with lint messages and their severities.

        The script returns nonzero status if any warnings or errors are
        present.
        """)
    parser.add_argument('--repfile',
                        type=lambda p: Path(p).resolve(),
                        default="./slang.log",
                        help="""The script searches the log file provided.
                        Defaults to './slang.log'""")

    parser.add_argument('--outfile',
                        type=lambda p: Path(p).resolve(),
                        default="./results.hjson",
                        help="""Path to the results Hjson file.
                        Defaults to './results.hjson'""")
    args = parser.parse_args()

    # Define warning/error patterns for the slang log file.
    # Slang diagnostic format: <file>:<line>:<col>: <severity>: <message> [<code>]
    parser_args = {
        args.repfile: [
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
            ("flow_error",
             r"^(?!ERROR: Failed to build .* 'make' exited with an error code)ERROR: .*"),
            # Tool-level errors emitted by slang itself (e.g. bad flags, missing files).
            ("flow_error",
             r"^slang: error: .*"),
            # Generic error lines without a file location (e.g. elaboration failures).
            ("flow_error",
             r"^(?!.*:\d+:\d+:)error: .*"),
            # Per-location diagnostics mapped to lint severities.
            ("lint_error",
             r"^.*:\d+:\d+: error: .*"),
            ("lint_warning",
             r"^.*:\d+:\d+: warning: .*"),
            ("lint_info",
             r"^.*:\d+:\d+: note: .*"),
        ]
    }

    # Parse logs
    parser = LintParser()
    num_messages = parser.get_results(parser_args)

    # Write out results file
    parser.write_results_as_hjson(args.outfile)

    # Return nonzero status if any warnings or errors are present.
    # lint infos do not count as failures.
    if num_messages['error'] > 0 or num_messages['warning'] > 0:
        log.info("Found %d lint errors and %d lint warnings",
                 num_messages['error'],
                 num_messages['warning'])
        sys.exit(1)

    log.info("Lint logfile parsed successfully")
    sys.exit(0)


if __name__ == "__main__":
    main()
