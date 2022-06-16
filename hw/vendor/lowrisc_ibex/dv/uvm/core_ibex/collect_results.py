#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import junit_xml
import os.path
import sys
import yaml
from scripts.test_run_result import (TestRunResult, test_run_result_fields,
                                     check_test_run_result)
from typing import List, TextIO


def parse_test_run_result(path: str) -> TestRunResult:
    try:
        with open(path) as yaml_file:
            test_run_result_dict = yaml.load(yaml_file, Loader=yaml.SafeLoader)
            loaded_fields = test_run_result_dict.keys()
            if set(loaded_fields) != set(test_run_result_fields):
                raise RuntimeError(f'Error loading YAML at {path}: does not '
                                   'contain the correct set of fields')

            trr = TestRunResult(**test_run_result_dict)
            try:
                check_test_run_result(trr)
            except AssertionError:
                raise RuntimeError(f'Error loading YAML at path {path}: '
                                   'field types were incorrect')
            return trr
    except (IOError, yaml.YAMLError) as e:
        raise RuntimeError(f'Error loading YAML at path {path}: {e}')


def build_broken_test_run_result(err: str) -> TestRunResult:
    return TestRunResult(
            name='unknown',
            idx=0,
            seed=0,
            binary=None,
            uvm_log=None,
            rtl_trace=None,
            rtl_trace_csv=None,
            iss_trace=None,
            iss_trace_csv=None,
            comparison_log=None,
            passed=False,
            failure_message=err
    )


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


def gen_test_run_result_text(test_run_result: TestRunResult) -> str:
    '''Generate a string describing a TestRunResult.

    The string includes details of logs, binary run and the failure message if
    the test did not pass.'''
    test_name_idx = f'{test_run_result.name}.{test_run_result.seed}'
    test_underline = '-' * len(test_name_idx)
    info_lines = [test_name_idx, test_underline]

    if (test_run_result.binary):
        info_lines.append(f'Test binary: {test_run_result.binary}')

    if (test_run_result.uvm_log):
        info_lines.append(f'UVM log: {test_run_result.uvm_log}')

    if (test_run_result.rtl_trace):
        info_lines.append(f'RTL trace: {test_run_result.rtl_trace}')

    if (test_run_result.iss_trace):
        info_lines.append(f'ISS trace: {test_run_result.iss_trace}')

    if (test_run_result.cosim_trace):
        info_lines.append(f'cosim trace: {test_run_result.cosim_trace}')

    if (test_run_result.comparison_log):
        info_lines.append(f'Comparison log: {test_run_result.comparison_log}')

    if (test_run_result.passed):
        info_lines.append('')
        info_lines.append('[PASSED]')
    else:
        info_lines.append('')
        info_lines.append(test_run_result.failure_message)

    return '\n'.join(info_lines) + '\n'


def output_results_text(passing_tests: List[TestRunResult], failing_tests:
                        List[TestRunResult], dest: TextIO):
    '''Write results in text form to dest'''

    if failing_tests:
        print(box_comment('Details of failing tests'), file=dest)
        for trr in failing_tests:
            print(gen_test_run_result_text(trr), file=dest)

    if passing_tests:
        print(box_comment('Details of passing tests'), file=dest)
        for trr in passing_tests:
            print(gen_test_run_result_text(trr), file=dest)

    dest.write('\n')

    print(gen_summary_line(passing_tests, failing_tests), file=dest)


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
            test_suite_info.setdefault(trr.name, ([], {'stdout': '',
                                                       'failures': ''}))
        result_text = gen_test_run_result_text(trr)

        # Create a test case for the TestRunResult. stdout holds the text
        # describing the run. Add the same text to failures if the test failed.
        test_case = junit_xml.TestCase(f'{trr.name}.{trr.seed}')
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
    parser = argparse.ArgumentParser()
    parser.add_argument('--output_dir', '-o', required=True)
    parser.add_argument('test_run_result', nargs='*')

    args = parser.parse_args()

    passing_tests = []
    failing_tests = []
    for test_run_result_path in args.test_run_result:
        try:
            test_run_result = parse_test_run_result(test_run_result_path)
            if test_run_result.passed:
                passing_tests.append(test_run_result)
            else:
                failing_tests.append(test_run_result)
        except RuntimeError as e:
            failing_tests.append(build_broken_test_run_result(str(e)))

    regr_log_path = os.path.join(args.output_dir, 'regr.log')
    junit_xml_path = os.path.join(args.output_dir, 'regr_junit.xml')
    junit_xml_merged_path = os.path.join(args.output_dir,
                                         'regr_junit_merged.xml')

    with open(regr_log_path, 'w', encoding='UTF-8') as outfile:
        output_results_text(passing_tests, failing_tests, outfile)

    with open(junit_xml_path, 'w', encoding='UTF-8') as junit_xml, \
         open(junit_xml_merged_path, 'w', encoding='UTF-8') as \
            junit_merged_xml:
        output_run_results_junit_xml(passing_tests, failing_tests, junit_xml,
                                     junit_merged_xml)

    print(gen_summary_line(passing_tests, failing_tests))

    # Succeed if no tests failed
    return 1 if failing_tests else 0


if __name__ == '__main__':
    sys.exit(main())
