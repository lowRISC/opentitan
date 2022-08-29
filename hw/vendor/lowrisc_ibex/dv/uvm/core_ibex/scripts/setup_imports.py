#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import sys
import pathlib3x as pathlib


def get_project_root() -> pathlib.Path:
    """Get the project root directory."""
    return pathlib.Path(__file__).resolve().parents[4]


root = get_project_root()
_IBEX_ROOT = root
_IBEX_UTIL = root/'util'
_CORE_IBEX = root/'dv'/'uvm'/'core_ibex'
_CORE_IBEX_SCRIPTS = _CORE_IBEX/'scripts'
_CORE_IBEX_RISCV_DV_EXTENSION = _CORE_IBEX/'riscv_dv_extension'
_CORE_IBEX_YAML = _CORE_IBEX/'yaml'
_RISCV_DV = root/'vendor'/'google_riscv-dv'
_RISCV_DV_SCRIPTS = _RISCV_DV/'scripts'
_OT_LOWRISC_IP = root/'vendor'/'lowrisc_ip'



def get_pythonpath() -> None:
    """Create a string to be exported as PYTHONPATH.

    Setting this environment variable appropriately
    (from the top of the buildsystem) will then allow all
    python scripts to import all modules as needed.
    """
    pythonpath = ':'.join([
        str(_IBEX_ROOT),
        str(_IBEX_UTIL),
        # str(_CORE_IBEX),
        str(_CORE_IBEX_SCRIPTS),
        str(_CORE_IBEX_RISCV_DV_EXTENSION),
        str(_CORE_IBEX_YAML),
        # str(_RISCV_DV),
        str(_RISCV_DV_SCRIPTS)
    ])
    print(pythonpath)  # This is the output (captured by the shell)


if __name__ == '__main__':
    sys.exit(get_pythonpath())
