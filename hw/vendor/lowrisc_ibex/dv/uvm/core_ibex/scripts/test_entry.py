# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import re
import logging
from typing import Dict, List, Tuple

# Import riscv_trace_csv and lib from _DV_SCRIPTS before putting sys.path back
# as it started.
from setup_imports import _CORE_IBEX_RISCV_DV_EXTENSION, _RISCV_DV
import lib as riscvdv_lib  # type: ignore


TestEntry = Dict[str, object]
TestEntries = List[TestEntry]
TestAndSeed = Tuple[str, int]


def read_test_dot_seed(arg: str) -> TestAndSeed:
    '''Read a value for --test-dot-seed'''

    match = re.match(r'([^.]+)\.([0-9]+)$', arg)
    if match is None:
        raise argparse.ArgumentTypeError('Bad --test-dot-seed ({}): '
                                         'should be of the form TEST.SEED.'
                                         .format(arg))

    return (match.group(1), int(match.group(2), 10))


def get_test_entry(testname: str) -> TestEntry:
    matched_list = []  # type: TestEntries
    testlist = _CORE_IBEX_RISCV_DV_EXTENSION/'testlist.yaml'

    riscvdv_lib.process_regression_list(testlist, 'all', 0, matched_list, _RISCV_DV)

    for entry in matched_list:
        if entry['test'] == testname:
            return entry
    raise RuntimeError('No matching test entry for {!r}'.format(testname))
