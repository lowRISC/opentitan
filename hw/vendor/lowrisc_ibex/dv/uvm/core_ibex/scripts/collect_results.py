#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import sys
import io
import pathlib3x as pathlib
import dataclasses
from metadata import RegressionMetadata, LockedMetadata
from test_run_result import TestRunResult, Failure_Modes
import scripts_lib as ibex_lib
from typing import List, TextIO, Dict

from report_lib.util import create_test_summary_dict, create_cov_summary_dict
from report_lib.text import output_results_text, gen_summary_line
from report_lib.html import output_results_html
from report_lib.junit_xml import output_run_results_junit_xml
from report_lib.dvsim_json import output_results_dvsim_json

try:
    # SVG requires python 3.7 and above, for environments that don't have python
    # 3.7 (e.g. CentOS 7) detect failure to import and just skip any svg
    # generation.
    import svg
    from report_lib.svg import output_results_svg
    SVG_MODULE_PRESENT = True
except ImportError:
    SVG_MODULE_PRESENT = False

def main() -> int:
    """Collect all test results into summary files.

    Locate all the individual test results, and combine them into higher level
    summaries, while parsing for errors and other salient information.
    """
    parser = argparse.ArgumentParser()
    parser.add_argument('--dir-metadata',
                        type=pathlib.Path, required=True)

    args = parser.parse_args()

    with LockedMetadata(args.dir_metadata, __file__) as md:
        summary_dict = {}
        passing_tests = []
        failing_tests = []
        for f in md.tests_pickle_files:
            try:
                trr = TestRunResult.construct_from_pickle(f)
                summary_dict[f"{trr.testname}.{trr.seed}"] = \
                    ('PASS' if trr.passed else
                     'FAILED' + (" {T}" if (trr.failure_mode == Failure_Modes.TIMEOUT) else ""))
                if trr.passed:
                    passing_tests.append(trr)
                else:
                    failing_tests.append(trr)
            except RuntimeError as e:
                failing_tests.append(
                    TestRunResult(
                        name='broken_test',
                        failure_message=str(e)
                    ))

        md.regr_log = md.dir_run/'regr.log'
        md.regr_log_junit = md.dir_run/'regr_junit.xml'
        md.regr_log_junit_merged = md.dir_run/'regr_junit_merged.xml'

        #  Write results as junit_xml
        with open(md.regr_log_junit,
                  'w',
                  encoding='UTF-8') as junit_xml,\
             open(md.regr_log_junit_merged,
                  'w',
                  encoding='UTF-8') as junit_merged_xml:
            output_run_results_junit_xml(passing_tests, failing_tests,
                                         junit_xml,
                                         junit_merged_xml)

        with open(md.regr_log, 'w', encoding='UTF-8') as outfile:
            #  Write results as regr.log (custom logfile format)
            output_results_text(passing_tests, failing_tests, summary_dict,
                                outfile)

        test_summary_dict = create_test_summary_dict(passing_tests +
                failing_tests)

        cov_summary_dict = {}
        if md.simulator == "xlm":
            cov_summary_dict = create_cov_summary_dict(md)
        else:
            print("Warning: Not generating coverage summary, unsupported " \
                    f"simulator {md.simulator}")

        html_report_filename = md.dir_run/'report.html'
        with open(html_report_filename, 'w') as outfile:
            output_results_html(md, passing_tests + failing_tests,
                    test_summary_dict, cov_summary_dict, outfile)

        json_report_filename = md.dir_run/'report.json'
        with open(json_report_filename, 'w') as json_report_file:
            output_results_dvsim_json(md, test_summary_dict, cov_summary_dict,
                                      json_report_file)

        if SVG_MODULE_PRESENT:
            svg_summary_filename = md.dir_run/'summary.svg'
            with open(svg_summary_filename, 'w') as svg_summary_file:
                output_results_svg(test_summary_dict, cov_summary_dict,
                        svg_summary_file)
        else:
            print('WARNING: svg module not available, skipping SVG results output')

        # Print a summary line to the terminal
        print(gen_summary_line(passing_tests, failing_tests))

    # Succeed if no tests failed
    return 1 if failing_tests else 0


if __name__ == '__main__':
    sys.exit(main())
