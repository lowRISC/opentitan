# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from test_run_result import TestRunResult
from metadata import RegressionMetadata
from typing import List, TextIO, Dict
import dataclasses
import scripts_lib as ibex_lib

import re
import os.path
import io

CSS_RG_GRADIENT_YELLOW_POINT = 0.7

def css_red_green_gradient(value: float) -> str:
    '''Outputs a CSS compatible colour value from a point on a red-yellow-green
       gradient'''
    if value < CSS_RG_GRADIENT_YELLOW_POINT:
        red = 1.0
        green = value / CSS_RG_GRADIENT_YELLOW_POINT
    else:
        red = (1.0 - value) / (1.0 - CSS_RG_GRADIENT_YELLOW_POINT)
        green = 1.0

    red = int(red * 255)
    green = int(green * 255)

    return f'rgb({red},{green},0)'

def gen_test_run_result_text(trr: TestRunResult) -> str:
    '''Generate a string describing a TestRunResult.

    The string includes details of logs, binary run and the failure message if
    the test did not pass.'''
    test_name_idx = f'{trr.testname}.{trr.seed}'
    test_underline = '-' * len(test_name_idx)
    info_lines: List[str] = [test_name_idx, test_underline]

    # Filter out relevant fields, and print as relative to the dir_test for
    # readability.
    lesskeys = \
            {k: str(v.relative_to(trr.dir_test) if v is not None else 'MISSING')
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

XLM_TABLE_HEADER_RE = re.compile(r'(\w+)\*?\s+((?:average)|(?:covered))')
XLM_TABLE_COVERAGE_RE = re.compile(r'\((\d+)/(\d+).*\)')
XLM_TABLE_AVERAGE_RE = re.compile(r'(\d+(?:.\d+)?)%')

IBEX_COVERAGE_METRICS = ['block', 'branch', 'statement', 'expression', 'toggle',
        'fsm', 'assertion']
COVERGROUP_IGNORE = ['push_pull_agent_pkg']

def parse_xcelium_cov_report(cov_report: str) -> Dict[str, Dict[str, Dict[str, int]]]:
    '''Produces a dictionary of coverage results from an xlm test report

    Sample output:
        {'ibex_top':
            {'block': {'covered': 123, 'total': 321},
             'covergroup': {'average': 78.s}}
        }

    The top-level dictionary gives per-module info. For each module coverage is
    seperated into a number of metrics. Each metric can be one of two types:
    1. covered - Two integers, 'total' giving total number of things to cover
       and 'covered' giving the number that are covered.
    2. average - Single integer, 'average' giving the average coverage
       percentage (0 - 100) for that metric.

    '''
    cov_report_lines = cov_report.splitlines()
    cov_summary_dict = {}
    metrics_start_line = -1
    metric_info = []

    for line_no, line in enumerate(cov_report_lines):
        if "name" in line:
            line_elements = line.lower().split()[1:]
            reduced_line = ' '.join(line_elements)

            for metric_info_match in XLM_TABLE_HEADER_RE.finditer(reduced_line):
                metric_info.append((metric_info_match.group(1),
                    metric_info_match.group(2)))

            # Skip header separator line
            metrics_start_line = line_no + 2

    if metrics_start_line == -1:
        raise RuntimeError('Could not read xcelium coverage report')

    for line in cov_report_lines[metrics_start_line:]:
        line = re.sub(r'%\s+\(', '%(', line)
        values = line.strip().split()

        module_name = ''

        for i, value in enumerate(values):
            value = value.strip()

            if i == 0:
                module_name = value
                cov_summary_dict[module_name] = {}
                continue

            metric_type = metric_info[i - 1][1]
            metric_name = metric_info[i - 1][0] + '-' + metric_type

            if metric_type == 'covered':
                m = XLM_TABLE_COVERAGE_RE.search(value)
                if m:
                    cov_summary_dict[module_name][metric_name] = {
                            'covered' : int(m.group(1)),
                            'total' : int(m.group(2))
                    }
            else:
                m = XLM_TABLE_AVERAGE_RE.search(value)
                if m:
                    cov_summary_dict[module_name][metric_name] = {
                            'average' : float(m.group(1))
                    }

    return cov_summary_dict

def create_test_summary_dict(tests: List[TestRunResult]) -> Dict[str, Dict[str, int]]:
    '''From a list of tests produce a dictionary of passing and failing runs per
       test.

       Sample output:
       {'test_name_1' : {'passing': 34, 'failing': 57},
        'test_name_2' : {'passing': 29, 'failing': 89}}
    '''
    test_summary_dict = {}

    for test in tests:
        if test.testname not in test_summary_dict:
            test_summary_dict[test.testname] = {'passing': 0, 'failing': 0}

        if test.passed:
            test_summary_dict[test.testname]['passing'] += 1
        else:
            test_summary_dict[test.testname]['failing'] += 1

    return test_summary_dict

def add_cov_to_summary(metric_name: str, metric_data: Dict[str, Dict[str, int]],
        cov_summary_dict: Dict[str, int]) -> None:
    '''Calculates coverage percentage for particular coverage metric and add it
       coverage summary dictionary.

       This is a helper function used by create_cov_summary_dict
    '''
    if (f'{metric_name}-covered' in metric_data):
        cov_pct = (metric_data[f'{metric_name}-covered']['covered'] /
            metric_data[f'{metric_name}-covered']['total'])

        cov_summary_dict[metric_name] = cov_pct

def calc_cg_average(cg_report_dict: Dict[str, Dict[str, Dict[str, int]]]) -> float:
    '''Calculate average covergroup coverage across multiple modules.

       This is a helper function used by create_cov_summary_dict.
    '''
    cg_average_total = 0
    num_modules = 0

    for module, metric_data in cg_report_dict.items():
        if module in COVERGROUP_IGNORE:
            continue

        if 'covergroup-average' not in metric_data:
            continue

        cg_average_total += metric_data['covergroup-average']['average']
        num_modules += 1

    if num_modules > 0:
        return (cg_average_total / 100) / num_modules

    return None

def create_cov_summary_dict(metadata: RegressionMetadata) -> Dict[str, int]:
    '''Read coverage reports to produce a summary dictionary.

       Sample output:
       {'block': 0.78,
        'statement': 0.48}
    '''
    if not metadata.cov_report_log:
        return None

    cov_report_dir = os.path.join(os.path.dirname(metadata.cov_report_log),
            "report")

    cov_report_filename = os.path.join(cov_report_dir, "cov_report.txt")
    cg_report_filename = os.path.join(cov_report_dir, "cov_report_cg.txt")

    cov_report_dict = {}
    cg_report_dict = {}

    with open(cov_report_filename, 'r') as cov_report_file:
        cov_report_dict = parse_xcelium_cov_report(cov_report_file.read())

    with open(cg_report_filename, 'r') as cg_report_file:
        cg_report_dict = parse_xcelium_cov_report(cg_report_file.read())

    cov_summary_dict = {}

    if 'ibex_top' in cov_report_dict:
        for metric_name in IBEX_COVERAGE_METRICS:
            add_cov_to_summary(metric_name, cov_report_dict['ibex_top'],
                    cov_summary_dict)

    cov_summary_dict['covergroup'] = calc_cg_average(cg_report_dict)

    return cov_summary_dict
