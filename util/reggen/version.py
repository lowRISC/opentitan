# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Standard version printing
"""
import os
import subprocess
import sys
from typing import List

from importlib.metadata import version


def show_and_exit(clitool: str, packages: List[str]) -> None:
    util_path = os.path.dirname(os.path.realpath(clitool))
    os.chdir(util_path)
    ver = subprocess.run(
        ["git", "describe", "--always", "--dirty", "--broken"],
        stdout=subprocess.PIPE).stdout.strip().decode('ascii')
    if (ver == ''):
        ver = 'not found (not in Git repository?)'
    sys.stderr.write(clitool + " Git version " + ver + '\n')
    for p in packages:
        sys.stderr.write(p + ' ' + version(p) + '\n')
    exit(0)
