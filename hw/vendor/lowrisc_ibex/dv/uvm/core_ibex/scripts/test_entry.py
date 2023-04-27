# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import re
from typing import Dict, List, Tuple
import pathlib3x as pathlib

import scripts_lib

import logging
logger = logging.getLogger(__name__)


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


def get_test_entry(testname: str, testlist: pathlib.Path) -> TestEntry:

    yaml_data = scripts_lib.read_yaml(testlist)

    for entry in yaml_data:
        if entry.get('test') == testname:
            return entry

    raise RuntimeError('No matching test entry for {!r}'.format(testname))
