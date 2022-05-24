#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''
A script to compare an ISS and RTL run to make sure nothing has diverged.
'''

import argparse
import os
import re
import sys
from typing import Dict, Optional, TextIO, Tuple, Union

from test_entry import TestEntry, get_test_entry
from test_run_result import TestRunResult

_CORE_IBEX = os.path.normpath(os.path.join(os.path.dirname(__file__)))
_IBEX_ROOT = os.path.normpath(os.path.join(_CORE_IBEX, '../../..'))
_RISCV_DV_ROOT = os.path.join(_IBEX_ROOT, 'vendor/google_riscv-dv')
_OLD_SYS_PATH = sys.path

# Import riscv_trace_csv and lib from _DV_SCRIPTS before putting sys.path back
# as it started.
try:
    sys.path = ([os.path.join(_CORE_IBEX, 'riscv_dv_extension'),
                 os.path.join(_RISCV_DV_ROOT, 'scripts')] +
                sys.path)

    from spike_log_to_trace_csv import process_spike_sim_log  # type: ignore
    from ovpsim_log_to_trace_csv import process_ovpsim_sim_log  # type: ignore
    from instr_trace_compare import compare_trace_csv  # type: ignore

    from ibex_log_to_trace_csv import (process_ibex_sim_log,  # type: ignore
                                       check_ibex_uvm_log)
finally:
    sys.path = _OLD_SYS_PATH


_TestAndSeed = Tuple[str, int]
_CompareResult = Tuple[bool, Optional[str], Dict[str, str]]


def read_test_dot_seed(arg: str) -> _TestAndSeed:
    '''Read a value for --test-dot-seed'''

    match = re.match(r'([^.]+)\.([0-9]+)$', arg)
    if match is None:
        raise argparse.ArgumentTypeError('Bad --test-dot-seed ({}): '
                                         'should be of the form TEST.SEED.'
                                         .format(arg))

    return (match.group(1), int(match.group(2), 10))


def compare_test_run(test: TestEntry,
                     idx: int,
                     seed: int,
                     rtl_log_dir: str,
                     iss: str,
                     iss_log_dir: str,
                     instr_gen_bin_dir: str) -> TestRunResult:
    '''Compare results for a single run of a single test

    Here, test is a dictionary describing the test (read from the testlist YAML
    file). idx is the iteration index and seed is the corresponding seed. iss
    is the chosen instruction set simulator (currently supported: spike and
    ovpsim).

    rtl_log_dir is the directory containing log output from the RTL simulation.
    iss_log_dir is the directory that contains logs for ISS runs.

    Returns a _CompareResult with a pass/fail flag, together with some
    information about the run (to be written to the log file).

    '''
    test_name = test['test']
    assert isinstance(test_name, str)
    uvm_log = os.path.join(rtl_log_dir, 'sim.log')
    elf = os.path.join(instr_gen_bin_dir, '{}_{}.o'.format(test_name, idx))

    rtl_trace = os.path.join(rtl_log_dir, 'trace_core_00000000.log')

    kv_data = {
        'name': test_name,
        'idx': idx,
        'seed': seed,
        'binary': elf,
        'uvm_log': uvm_log,
        'rtl_trace': rtl_trace,
        'rtl_trace_csv': None,
        'iss_trace': None,
        'iss_trace_csv': None,
        'comparison_log': None,
        'passed': False,
        'failure_message': None
    }

    # Have a look at the UVM log. Report a failure if an issue is seen in the
    # log.
    try:
        uvm_pass, uvm_log_lines = check_ibex_uvm_log(uvm_log)
    except IOError as e:
        kv_data['failure_message'] = str(e)
        kv_data['failure_message'] += \
            '\n[FAILED] Could not open simulation log'
        return TestRunResult(**kv_data)

    if not uvm_pass:
        kv_data['failure_message'] = '\n'.join(uvm_log_lines)
        kv_data['failure_message'] += '\n[FAILED]: sim error seen'
        return TestRunResult(**kv_data)

    rtl_trace_csv = os.path.join(rtl_log_dir, 'trace_core_00000000.csv')

    kv_data['rtl_trace_csv'] = rtl_trace_csv
    try:
        # Convert the RTL log file to a trace CSV.
        process_ibex_sim_log(rtl_trace, rtl_trace_csv, 1)
    except (OSError, RuntimeError) as e:
        kv_data['failure_message'] = \
            '[FAILED]: Log processing failed: {}'.format(e)
        return TestRunResult(**kv_data)

    no_post_compare = test.get('no_post_compare', False)
    assert isinstance(no_post_compare, bool)

    # no_post_compare skips the final ISS v RTL log check, so if we've reached
    # here we're done when no_post_compare is set.
    if no_post_compare:
        kv_data['passed'] = True
        return TestRunResult(**kv_data)

    # There were no UVM errors. Process the log file from the ISS.
    iss_log = os.path.join(iss_log_dir, '{}.{}.log'.format(test_name, idx))
    iss_csv = os.path.join(iss_log_dir, '{}.{}.csv'.format(test_name, idx))

    kv_data['iss_trace'] = iss_log
    kv_data['iss_trace_csv'] = iss_csv
    try:
        if iss == "spike":
            process_spike_sim_log(iss_log, iss_csv)
        else:
            assert iss == 'ovpsim'  # (should be checked by argparse)
            process_ovpsim_sim_log(iss_log, iss_csv)
    except (OSError, RuntimeError) as e:
        kv_data['failure_message'] = \
            '[FAILED]: Log processing failed: {}'.format(e)
        return TestRunResult(**kv_data)

    compare_log = os.path.join(rtl_log_dir, 'compare.log')
    kv_data['comparison_log'] = compare_log

    # Delete any existing file at compare_log (the compare_trace_csv function
    # would append to it, which is rather confusing).
    try:
        os.remove(compare_log)
    except FileNotFoundError:
        pass

    compare_result = \
        compare_trace_csv(rtl_trace_csv, iss_csv, "ibex", iss, compare_log,
                          **test.get('compare_opts', {}))

    try:
        compare_log_file = open(compare_log)
        compare_log_contents = compare_log_file.read()
        compare_log_file.close()
    except IOError as e:
        kv_data['failure_message'] = \
            '[FAILED]: Could not read compare log: {}'.format(e)
        return TestRunResult(**kv_data)

    # Rather oddly, compare_result is a string. The comparison passed if it
    # starts with '[PASSED]' and failed otherwise.
    compare_passed = compare_result.startswith('[PASSED]: ')
    if not compare_passed:
        assert compare_result.startswith('[FAILED]: ')
        kv_data['failure_message'] = ('RTL / ISS trace comparison failed\n' +
                                      compare_log_contents)
        return TestRunResult(**kv_data)

    kv_data['passed'] = True
    return TestRunResult(**kv_data)


# If any of these characters are present in a string output it in multi-line
# mode. This will either be because the string contains newlines or other
# characters that would otherwise need escaping
_YAML_MULTILINE_CHARS = ['[', ']', ':', "'", '"', '\n']


def yaml_format(val: Union[int, str, bool]) -> str:
    '''Format a value for yaml output.

    For int, str and bool value can just be converted to str with special
    handling for some string
    '''

    # If val is a multi-line string
    if isinstance(val, str) and any(c in val for c in _YAML_MULTILINE_CHARS):
        # Split into individual lines and output them after a suitable yaml
        # multi-line string indicator ('|-') indenting each line.
        lines = val.split('\n')
        return '|-\n' + '\n'.join([f'  {line}' for line in lines])

    if val is None:
        return ''

    return str(val)


def on_result(result: TestRunResult, output: TextIO) -> None:
    kv_data = result._asdict()

    klen = 1
    for k in kv_data:
        klen = max(klen, len(k))

    for k, v in kv_data.items():
        kpad = ' ' * (klen - len(k))
        output.write(f'{k}:{kpad} {yaml_format(v)}\n')


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--instr-gen-bin-dir', required=True)
    parser.add_argument('--iss', required=True, choices=['spike', 'ovpsim'])
    parser.add_argument('--iss-log-dir', required=True)
    parser.add_argument('--start-seed', type=int, required=True)
    parser.add_argument('--test-dot-seed',
                        type=read_test_dot_seed,
                        required=True)
    parser.add_argument('--rtl-log-dir', required=True)
    parser.add_argument('--output', required=True)

    args = parser.parse_args()
    if args.start_seed < 0:
        raise RuntimeError('Invalid start seed: {}'.format(args.start_seed))

    testname, seed = args.test_dot_seed
    if seed < args.start_seed:
        raise RuntimeError('Start seed is greater than test seed '
                           f'({args.start_seed} > {seed}).')

    iteration = seed - args.start_seed

    entry = get_test_entry(testname)

    result = compare_test_run(entry, iteration, seed,
                              args.rtl_log_dir, args.iss, args.iss_log_dir,
                              args.instr_gen_bin_dir)
    with open(args.output, 'w', encoding='UTF-8') as outfile:
        on_result(result, outfile)

    # Always return 0 (success), even if the test failed. We've successfully
    # generated a comparison log either way and we don't want to stop Make from
    # gathering them all up for us.
    return 0


if __name__ == '__main__':
    sys.exit(main())
