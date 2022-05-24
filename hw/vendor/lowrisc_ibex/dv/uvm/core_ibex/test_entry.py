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
                 os.path.join(_RISCV_DV_ROOT, 'scripts')] +
                sys.path)
    from lib import process_regression_list  # type: ignore
finally:
    sys.path = _OLD_SYS_PATH


TestEntry = Dict[str, object]
TestEntries = List[TestEntry]


def get_test_entry(testname: str) -> TestEntry:
    matched_list = []  # type: TestEntries
    testlist = os.path.join(_CORE_IBEX, 'riscv_dv_extension', 'testlist.yaml')
    process_regression_list(testlist, 'all', 0, matched_list, _RISCV_DV_ROOT)

    for entry in matched_list:
        if entry['test'] == testname:
            return entry
    raise RuntimeError('No matching test entry for {!r}'.format(testname))
