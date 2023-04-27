# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List, TextIO, Dict
from test_run_result import TestRunResult
from metadata import RegressionMetadata

import mako.template
import os.path
from datetime import datetime, timezone
from functools import reduce
from .util import gen_test_run_result_text, css_red_green_gradient

def pct_str(pct_val: float) -> str:
    return f'{pct_val * 100:.1f}%'

def pct_style(pct_val: float) -> str:
    return f'background-color: {css_red_green_gradient(pct_val)};'

def output_results_html(md: RegressionMetadata,
                        all_tests: List[TestRunResult],
                        test_summary_dict: Dict[str, Dict[str, int]],
                        cov_summary_dict: Dict[str, float],
                        dest: TextIO) -> None:
    '''Write HTML report for given test and coverage results to dest.'''
    total_tests_acc = 0
    passing_tests_acc = 0

    test_dict = {}
    test_summaries = []

    for test_name, test_info in test_summary_dict.items():
        total_tests = test_info['passing'] + test_info['failing'];
        pass_rate = test_info['passing'] / total_tests

        test_summaries.append({
                'name': test_name,
                'passing': test_info['passing'],
                'total_tests': total_tests,
                'pass_rate': pass_rate
        })

        total_tests_acc += total_tests
        passing_tests_acc += test_info['passing']

    pass_rate_acc = passing_tests_acc / total_tests_acc

    report_template_filename = os.path.join(os.path.dirname(__file__),
            'regression_report.tpl.html')

    report_template = \
        mako.template.Template(filename=report_template_filename)

    dest.write(report_template.render(
        run_datetime = md.creation_datetime,
        sha1 = md.git_commit,
        test_summaries = test_summaries,
        cov_summary = cov_summary_dict,
        passing_tests_acc = passing_tests_acc,
        total_tests_acc = total_tests_acc,
        pass_rate_acc = pass_rate_acc,
        all_tests = all_tests,
        gen_test_run_result_text = gen_test_run_result_text,
        pct_str = pct_str,
        pct_style = pct_style)
    )
