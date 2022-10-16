#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import junit_xml
import sys
import io
import pathlib3x as pathlib
import dataclasses
from metadata import RegressionMetadata, LockedMetadata
from test_run_result import TestRunResult, Failure_Modes
import scripts_lib as ibex_lib
from typing import List, TextIO


import logging
logger = logging.getLogger(__name__)


def box_comment(line: str) -> str:
    hr = '#' * 80
    return hr + '\n# ' + line + '\n' + hr


def gen_summary_line(passing_tests: List[TestRunResult], failing_tests:
                     List[TestRunResult]) -> str:
    '''Generate a string summarising test results'''
    total_tests = len(passing_tests) + len(failing_tests)
    pass_pct = (len(passing_tests) / total_tests) * 100

    return f'{pass_pct:0.2f}% PASS {len(passing_tests)} PASSED, ' \
           f'{len(failing_tests)} FAILED'


def gen_test_run_result_text(trr: TestRunResult) -> str:
    '''Generate a string describing a TestRunResult.

    The string includes details of logs, binary run and the failure message if
    the test did not pass.'''
    test_name_idx = f'{trr.testname}.{trr.seed}'
    test_underline = '-' * len(test_name_idx)
    info_lines: List[str] = [test_name_idx, test_underline]

    #  Filter out relevant fields, and print as relative to the dir_test for readability
    lesskeys = {k: str(v.relative_to(trr.dir_test))  # Improve readability
                for k, v in dataclasses.asdict(trr).items()
                if k in ['binary', 'rtl_log', 'rtl_trace', 'iss_cosim_trace']}
    strdict = ibex_lib.format_dict_to_printable_dict(lesskeys)

    trr_yaml = io.StringIO()
    ibex_lib.pprint_dict(strdict, trr_yaml)
    trr_yaml.seek(0)
    for line in trr_yaml.readlines():
        info_lines.append(line.strip('\n'))

    if (trr.passed):
        info_lines.append('\n[PASSED]')
    else:
        info_lines.append(str(trr.failure_message))

    return '\n' + '\n'.join(info_lines) + '\n'


def output_results_text(passing_tests: List[TestRunResult],
                        failing_tests: List[TestRunResult],
                        dest: TextIO):
    '''Write results in text form to dest'''

    print(box_comment('Details of failing tests'), file=dest)
    if not bool(failing_tests):
        print("No failing tests. Nice job!", file=dest)
    for trr in failing_tests:
        print(gen_test_run_result_text(trr), file=dest)

    print(box_comment('Details of passing tests'), file=dest)
    if not bool(passing_tests):
        print("No passing tests. Hmmmm...", file=dest)
    for trr in passing_tests:
        print(gen_test_run_result_text(trr), file=dest)


def output_run_results_junit_xml(passing_tests: List[TestRunResult],
                                 failing_tests: List[TestRunResult],
                                 junit_dest: TextIO,
                                 junit_merged_dest: TextIO):
    '''Write results to JUnit XML

    Two versions are produced: a normal version and a merged version. In the
    normal version there is a test suite per unique test name with a different
    test case per seed run. In the merged version there is a single test case
    under the test suite with information for the individual runs merged
    together. This is to aid use of the Azure Pipelines JUnit dashboard, which
    doesn't neatly handle the test suite/test case hierarchy
    '''

    all_tests = passing_tests + failing_tests

    test_suite_info = {}
    for trr in all_tests:
        # test_case_info contains a tuple per unique test name. The first
        # element is a list of junit_xml.TestCase, one per test run with that
        # name. The other merges together all of the test outputs to produce
        # the merged output.
        unmerged, merged = \
            test_suite_info.setdefault(trr.testname, ([], {'stdout': '',
                                                           'failures': ''}))
        result_text = gen_test_run_result_text(trr)

        # Create a test case for the TestRunResult. stdout holds the text
        # describing the run. Add the same text to failures if the test failed.
        test_case = junit_xml.TestCase(f'{trr.testname}.{trr.seed}')
        test_case.stdout = result_text

        merged['stdout'] += result_text + '\n'

        if not trr.passed:
            test_case.add_failure_info(output=result_text)
            merged['failures'] += result_text

        unmerged.append(test_case)

    # Output the normal JUnit XML
    test_suites = [junit_xml.TestSuite(name, test_cases) for
                   name, (test_cases, _) in test_suite_info.items()]

    junit_dest.write(junit_xml.to_xml_report_string(test_suites))

    # Output the merged version of the JUnit XML
    merged_test_suites = []

    for name, (_, merged_test_info) in test_suite_info.items():
        test_case = junit_xml.TestCase(name)
        test_case.stdout = merged_test_info['stdout']
        test_case.add_failure_info(output=merged_test_info['failures'])

        merged_test_suites.append(junit_xml.TestSuite(name, [test_case]))

    junit_merged_dest.write(junit_xml.to_xml_report_string(merged_test_suites))


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
                    if (trr.failure_mode == Failure_Modes.TIMEOUT):
                        trr.failure_message = f"[FAILURE] Simulation timed-out [{md.run_rtl_timeout_s}s].\n"
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

        #  Write results as regr.log (custom logfile format)
        with open(md.regr_log, 'w', encoding='UTF-8') as outfile:
            # Print a summary line right at the top of the file
            outfile.write(gen_summary_line(passing_tests, failing_tests))
            outfile.write('\n')
            # Print a short TEST.SEED   PASS/FAILED summary
            summary_yaml = io.StringIO()
            ibex_lib.pprint_dict(summary_dict, summary_yaml)
            summary_yaml.seek(0)
            outfile.write(summary_yaml.getvalue())
            outfile.write('\n')
            # Print a longer summary with some more information
            output_results_text(passing_tests, failing_tests, outfile)

        # Print a summary line to the terminal
        print(gen_summary_line(passing_tests, failing_tests))

    # Succeed if no tests failed
    return 1 if failing_tests else 0


if __name__ == '__main__':
    sys.exit(main())
