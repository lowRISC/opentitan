#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Parses cdc report and dump filtered messages in hjson format.
"""
import argparse
import logging as log
import re
import sys
import os
import hjson

from pathlib import Path
from LintParser import LintParser


def extract_rule_patterns(file_path: Path):
    '''
    This parses the CDC summary table to get the message totals,
    rule names and corresponding severities.
    '''

    rule_patterns = []
    full_file = ''
    try:
        with Path(file_path).open() as f:
            full_file = f.read()
    except IOError:
        # We will attempt read this file again in a second pass to parse out
        # the details, this error will get caught and reported.
        pass

    category = ''
    severity = ''
    known_rule_names = {}
    total_msgs = 0
    # extract the summary table
    m = re.findall(
        r'^Summary of Policy: ALL((?:.|\n|\r\n)*)Rule Details of Policy: ALL',
        full_file, flags=re.MULTILINE)
    if m:
        # step through the table and identify rule names and their
        # category and severity
        for line in m[0].split('\n'):
            if re.match(r'^POLICY\s+ALL', line):
                total = re.findall(r'^POLICY\s+ALL\s+([0-9]+)', line)
                total_msgs = int(total[0])
            elif re.match(r'^ GROUP\s+SDC_ENV_LINT', line):
                category = 'sdc'
            elif re.match(r'^ GROUP\s+VCDC_SETUP_CHECKS', line):
                category = 'setup'
            elif re.match(r'^ GROUP\s+VCDC_ANALYSIS_CHECKS', line):
                category = 'cdc'
            elif re.match(r'^ GROUP\s+ERROR', line):
                severity = 'error'
            elif re.match(r'^ GROUP\s+WARNING', line):
                severity = 'warning'
            elif re.match(r'^ GROUP\s+INFO', line):
                severity = 'info'
            elif re.match(r'^ GROUP\s+REVIEW', line):
                severity = 'review'
            elif re.match(r'^  INSTANCE', line):
                # we've found a new rule. convert it to a known rule pattern
                # with the correct category and severity
                rule = re.findall(
                    r'^  INSTANCE\s+([a-zA-Z0-9\_]+)\s+([0-9\_]+)', line)
                name = rule[0][0]
                count = int(rule[0][1])
                # a few rules produce messages with different severities but
                # the same rule labels. for simplicity, we promote messages
                # from lower severity buckets to the severity bucket where
                # this rule name has first been encountered. since higher
                # severity messages are listed first in this summary table, it
                # is straightforward to check whether the rule name has
                # already appeared in a higher severity bucket.
                if name in known_rule_names:
                    msg_group = known_rule_names[name]
                    log.warning('Rule {} is reported in multiple severity '
                                'classes. All messages of this rule are '
                                'promoted to {}'.format(name, msg_group))

                else:
                    msg_group = category + '_' + severity
                    known_rule_names.update({name: msg_group})
                    rule_patterns.append((msg_group, r'^{}:.*'.format(name)))

    return rule_patterns


# Reuse the lint parser, but add more buckets.
class CdcParser(LintParser):

    def __init__(self) -> None:
        self.buckets = {
            'flow_info': [],
            'flow_warning': [],
            'flow_error': [],
            'sdc_info': [],
            'sdc_review': [],
            'sdc_warning': [],
            'sdc_error': [],
            'setup_info': [],
            'setup_review': [],
            'setup_warning': [],
            'setup_error': [],
            'cdc_info': [],
            'cdc_review': [],
            'cdc_warning': [],
            'cdc_error': [],
            # this bucket is temporary and will be removed at the end of the
            # parsing pass.
            'fusesoc-error': []
        }
        self.severities = {
            'flow_info': 'info',
            'flow_warning': 'warning',
            'flow_error': 'error',
            'sdc_info': 'info',
            'sdc_review': 'warning',
            'sdc_warning': 'warning',
            'sdc_error': 'error',
            'setup_info': 'info',
            'setup_review': 'warning',
            'setup_warning': 'warning',
            'setup_error': 'error',
            'cdc_info': 'info',
            'cdc_review': 'warning',
            'cdc_warning': 'warning',
            'cdc_error': 'error'
        }


# TODO(#9079): this script will be removed long term once the
# parser has been merged with the Dvsim core code.
def main():
    parser = argparse.ArgumentParser(
        description="""This script parses AscentLint log and report files from
        a lint run, filters the messages and creates an aggregated result
        .hjson file with lint messages and their severities.

        The script returns nonzero status if any warnings or errors are
        present.
        """)
    parser.add_argument('--repdir',
                        type=lambda p: Path(p).resolve(),
                        default="./",
                        help="""The script searches the 'vcdc.log' and
                        'vcdc.rpt' files in this directory.
                        Defaults to './'""")

    parser.add_argument('--outfile',
                        type=lambda p: Path(p).resolve(),
                        default="./results.hjson",
                        help="""Path to the results Hjson file.
                        Defaults to './results.hjson'""")

    args = parser.parse_args()

    # Define warning/error patterns for each logfile
    parser_args = {}

    # Patterns for lint.log
    parser_args.update({
        args.repdir.joinpath('build.log'): [
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
        ]
    })

    # Patterns for vcdc.log
    parser_args.update({
        args.repdir.joinpath('syn-icarus/vcdc.log'): [
            ("flow_error", r"^FlexNet Licensing error.*"),
            ("flow_error", r"^Error: .*"),
            ("flow_error", r"^ERROR.*"),
            ("flow_error", r"^  ERR .*"),
            ("flow_warning", r"^Warning: .*"),
            # We ignore several messages here:
            # #25010: unused signals
            # #25011: unused signals
            # #25012: unused port
            # #25013: unused signals
            # #26038: unused or RTL constant
            # #39035: parameter becomes local
            # #39122: non-positive repeat
            # #39491: parameter in package
            ("flow_warning", r"^  "
                             "(?!WARN \[#25010\])"
                             "(?!WARN \[#25011\])"
                             "(?!WARN \[#25012\])"
                             "(?!WARN \[#25013\])"
                             "(?!WARN \[#26038\])"
                             "(?!WARN \[#39035\])"
                             "(?!WARN \[#39122\])"
                             "(?!WARN \[#39491\])"
                             "WARN .*"),
            ("flow_info", r"^  INFO .*")
        ]
    })

    # The CDC messages are a bit more involved to parse out, since we
    # need to know the names and associated severities to do this.
    # The tool prints out an overview table in the report, which we are
    # going to parse first in order to get this information.
    # This is then used to construct the regex patterns to look for
    # in a second pass to get the actual CDC messages.
    cdc_rule_patterns = extract_rule_patterns(
        args.repdir.joinpath('syn-icarus/vcdc.rpt'))

    # Patterns for vcdc.rpt
    parser_args.update({
        args.repdir.joinpath('syn-icarus/vcdc.rpt'): cdc_rule_patterns
    })

    # Parse logs
    parser = CdcParser()
    num_messages = parser.get_results(parser_args)

    # Write out results file
    parser.write_results_as_hjson(args.outfile)

    # return nonzero status if any warnings or errors are present
    # lint infos do not count as failures
    if num_messages['error'] > 0 or num_messages['warning'] > 0:
        log.info("Found %d lint errors and %d lint warnings",
                 num_messages['error'],
                 num_messages['warning'])
        sys.exit(1)

    log.info("Lint logfile parsed succesfully")
    sys.exit(0)


if __name__ == "__main__":
    main()
