#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Helper class for parsing lint reports into a generic hjson format.
"""
import re
import hjson

from pathlib import Path
from typing import List, Dict, Tuple


# TODO(#9079): this class will be refactored so that it can be integrated into
# the Dvsim core code.
class LintParser():

    def __init__(self) -> None:
        self.buckets = {
            'flow_info': [],
            'flow_warning': [],
            'flow_error': [],
            'lint_info': [],
            'lint_warning': [],
            'lint_error': [],
            # this bucket is temporary and will be removed at the end of the
            # parsing pass.
            'fusesoc-error': []
        }
        self.severities = {
            'flow_info': 'info',
            'flow_warning': 'warning',
            'flow_error': 'error',
            'lint_info': 'info',
            'lint_warning': 'warning',
            'lint_error': 'error',
        }

    def extract_messages(self, log_content: str, patterns: List[str]) -> None:
        """Extract messages from the string buffer log_content.

        The argument patterns needs to be a list of tuples with
        (<error_severity>, <pattern_to_match_for>).

        A substring that matches two different patterns will be stored in the
        bucket associated with the first pattern that matches.
        """
        # Iterate through all the patterns in reverse order and store hits
        # against the index of their first character. Doing this in reverse
        # order means that patterns earlier in the list "win": if two different
        # patterns match a particular substring, only the bucket of the first
        # one will end up in the found dict.
        found = {}
        for bucket, pattern in reversed(patterns):
            for m in re.finditer(pattern, log_content, flags=re.MULTILINE):
                found[m.pos] = (bucket, m.group(0))

        # Now that we've ignored duplicate hits, flatten things out into
        # self.buckets.
        for bucket, hit in found.values():
            self.buckets[bucket].append(hit)

    def get_results(self, args: Dict[Path, List[Tuple]]) -> Dict[str, int]:
        """
        Parse report and corresponding logfiles and extract error, warning
        and info messages for each IP present in the result folder
        """

        # Open all log files
        for path, patterns in args.items():
            try:
                with path.open() as f:
                    log_content = f.read()
                    self.extract_messages(log_content, patterns)
            except IOError as err:
                self.buckets['flow_error'] += \
                    ["IOError: %s" % err]

        # If there are no errors or warnings, add the "fusesoc-error" field to
        # "errors" (which will be reported as tooling errors). Remove the
        # "fusesoc-error" field either way.
        num_messages = {
            'info': 0,
            'warning': 0,
            'error': 0
        }
        for key, sev in self.severities.items():
            num_messages[sev] += len(self.buckets[key])
        if num_messages['error'] == 0 and num_messages['warning'] == 0:
            self.buckets['flow_error'] = self.buckets['fusesoc-error']
        del self.buckets['fusesoc-error']

        return num_messages

    def write_results_as_hjson(self, outpath: Path) -> None:
        with outpath.open("w") as results_file:
            # Construct results dict for Hjson file.
            hjson.dump(self.buckets,
                       results_file,
                       ensure_ascii=False,
                       for_json=True,
                       use_decimal=True)
