#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import os
import sys
from typing import Dict, List

_CORE_IBEX = os.path.normpath(os.path.join(os.path.dirname(__file__)))
_IBEX_ROOT = os.path.normpath(os.path.join(_CORE_IBEX, '../../..'))
_RISCV_DV_ROOT = os.path.join(_IBEX_ROOT, 'vendor/google_riscv-dv')
_OLD_SYS_PATH = sys.path

# Import riscv_trace_csv and lib from _DV_SCRIPTS before putting sys.path back
# as it started.
try:
    sys.path = ([os.path.join(_CORE_IBEX, 'riscv_dv_extension'),
                 os.path.join(_IBEX_ROOT, 'util'),
                 os.path.join(_RISCV_DV_ROOT, 'scripts')] +
                sys.path)
    from lib import process_regression_list  # type: ignore
    from ibex_config import parse_config  # type: ignore
finally:
    sys.path = _OLD_SYS_PATH

_TestEntry = Dict[str, object]
_TestEntries = List[_TestEntry]


def filter_tests_by_config(cfg: str, test_list: _TestEntries) -> _TestEntries:
    '''Filter out any unsupported tests from being executed.

    This function will parse the set of RTL parameters required by a given
    test (if any) and ensure that those parameters are supported by the
    selected core config.

    Doing this allows the run flow to be smarter about running regressions
    with different configs (useful for CI flows).

    Arguments:

        cfg: string name of the ibex config being tested, should match a
             config name from ibex_configs.yaml.

        test_list: list of test entry objects parsed from the YAML testlist

    Returns:

        filtered_test_list: a list of test entry objects, filtered such that
                            all tests incompatible with the specified ibex
                            config have been removed.

                            e.g. if the "small" config has been specified, this
                            function will filter out all tests that require
                            B-extension and PMP parameters
    '''
    filtered_test_list = []
    config = parse_config(cfg, os.path.join(_IBEX_ROOT, "ibex_configs.yaml"))

    for test in test_list:
        good = True
        if "rtl_params" in test:
            param_dict = test['rtl_params']
            assert isinstance(param_dict, dict)
            for p, p_val in param_dict.items():
                config_val = config.get(p, None)
                # Throw an error if required RTL parameters in the testlist
                # have been formatted incorrectly (typos, wrong parameters,
                # etc)
                if config_val is None:
                    raise ValueError('Parameter {} not found in config {}'
                                     .format(p, cfg))

                # Ibex has some enum parameters, so as a result some tests are
                # able to run with several of these parameter values (like
                # bitmanipulation tests). If this is the case, the testlist
                # will specify all legal enum values, check if any of them
                # match the config.
                if isinstance(p_val, list):
                    good = (config_val in p_val)
                else:
                    good = (p_val == config_val)

                # If there is any parameter mismatch, we can terminate
                # immediately and exclude the test from being executed
                if not good:
                    break

        if good:
            filtered_test_list.append(test)

    return filtered_test_list


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--start_seed', type=int, default=1)
    parser.add_argument('--test', required=True)
    parser.add_argument('--iterations', type=int, default=0)
    parser.add_argument('--ibex-config', required=True)

    args = parser.parse_args()
    if args.iterations < 0:
        raise RuntimeError('Bad --iterations argument: must be non-negative')
    if args.start_seed < 0:
        raise RuntimeError('Bad --start_seed argument: must be non-negative')

    # Get all the tests that match --test, scaling as necessary with the
    # --iterations argument.
    matched_list = []  # type: _TestEntries
    testlist = os.path.join(_CORE_IBEX, 'riscv_dv_extension', 'testlist.yaml')
    process_regression_list(testlist, args.test, args.iterations,
                            matched_list, _RISCV_DV_ROOT)
    if not matched_list:
        raise RuntimeError("Cannot find {} in {}".format(args.test, testlist))

    # Filter tests by the chosen configuration
    matched_list = filter_tests_by_config(args.ibex_config, matched_list)

    # Print the tests crossed by seeds, one to a line, in the format TEST.SEED.
    for test in matched_list:
        name = test['test']
        iterations = test['iterations']
        assert isinstance(name, str) and isinstance(iterations, int)
        assert iterations > 0
        for iteration in range(iterations):
            print('{}.{}'.format(name, args.start_seed + iteration))

    return 0


if __name__ == '__main__':
    sys.exit(main())
