# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import collections

# test_name, test_idx, seed and passed must never be None. Other fields can be
# None.
test_run_result_fields = [
         'name',  # Name of test
         'idx',  # Index of test
         'seed',  # Seed of test
         'binary',  # Path to test binary
         'uvm_log',  # Path to UVM DV simulation log
         'rtl_trace',  # Path to RTL ibex trace output
         'rtl_trace_csv',  # Path to RTL ibex trace CSV
         'iss_trace',  # Path to spike trace
         'iss_trace_csv',  # Path to spike trac.
         'comparison_log',  # Path to trace comparison log
         'passed',  # True if test passed
         'failure_message'  # Message describing failure, includes a
                            # '[FAILED]: XXXX' line at the end. Must not be
                            # None if passed is False
        ]

TestRunResult = collections.namedtuple('TestRunResult', test_run_result_fields)


def check_test_run_result(trr: TestRunResult):
    assert (trr.name is not None and isinstance(trr.name, str))
    assert (trr.idx is not None and isinstance(trr.idx, int))
    assert (trr.seed is not None and isinstance(trr.seed, int))
    assert (trr.binary is None or isinstance(trr.binary, str))
    assert (trr.uvm_log is None or isinstance(trr.uvm_log, str))
    assert (trr.rtl_trace is None or isinstance(trr.rtl_trace, str))
    assert (trr.rtl_trace_csv is None or isinstance(trr.rtl_trace_csv, str))
    assert (trr.iss_trace is None or isinstance(trr.iss_trace, str))
    assert (trr.iss_trace_csv is None or isinstance(trr.iss_trace_csv, str))
    assert (trr.comparison_log is None or isinstance(trr.comparison_log, str))
    assert (isinstance(trr.passed, bool))
    assert (trr.passed or isinstance(trr.failure_message, str))
