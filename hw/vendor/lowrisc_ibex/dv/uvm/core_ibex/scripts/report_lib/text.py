# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List, TextIO, Dict
from .util import gen_test_run_result_text
from test_run_result import TestRunResult

import io
import scripts_lib as ibex_lib

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


def output_results_text(passing_tests: List[TestRunResult],
                        failing_tests: List[TestRunResult],
                        summary_dict: Dict[str, str],
                        report_file: TextIO):
    '''Write results in text form to dest'''

    # Print a summary line right at the top of the file
    report_file.write(gen_summary_line(passing_tests, failing_tests))
    report_file.write('\n')
    # Print a short TEST.SEED   PASS/FAILED summary
    summary_yaml = io.StringIO()
    ibex_lib.pprint_dict(summary_dict, summary_yaml)
    summary_yaml.seek(0)
    report_file.write(summary_yaml.getvalue())
    report_file.write('\n')
    # Print a longer summary with some more information

    print('\n'+box_comment('Details of failing tests'), file=report_file)
    if not bool(failing_tests):
        print("No failing tests. Nice job!", file=report_file)
    for trr in failing_tests:
        print(gen_test_run_result_text(trr), file=report_file)

    print('\n'+box_comment('Details of passing tests'), file=report_file)
    if not bool(passing_tests):
        print("No passing tests. Hmmmm...", file=report_file)
    for trr in passing_tests:
        print(gen_test_run_result_text(trr), file=report_file)
