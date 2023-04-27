# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import junit_xml
from typing import List, TextIO
from test_run_result import TestRunResult
from .util import gen_test_run_result_text

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
