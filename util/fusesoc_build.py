#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Command-line tool to add the calling interpreter to fusesoc's PATH, so it
is used for generators.
"""


import os
import sys
from fusesoc.main import main

if __name__ == "__main__":
    # First, ensure the calling interpreter is on the PATH first, so any
    # generators asking /usr/bin/env for python3 will use the same version.
    path_env = os.environ["PATH"]
    if path_env is not None:
        path_env = ":" + path_env
    path_env = os.path.dirname(sys.executable) + path_env
    os.environ["PATH"] = path_env

    # Start fusesoc
    rc = main()
    sys.exit(rc)
