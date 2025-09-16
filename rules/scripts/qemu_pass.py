#!/usr/bin/env python
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Run QEMU test, checking for `PASS!`.

This script executes QEMU (as provided by Bazel runfiles) and checks for
`PASS!` to be printed from the UART. If QEMU also exited successfully, this
script will exit with `0`.
"""

import subprocess
import sys

from python.runfiles import Runfiles


def _main() -> int:
    r = Runfiles.Create()
    qemu_bin = r.Rlocation("qemu_opentitan/build/qemu-system-riscv32")

    # Run the process streaming (echoing) `stdout` and `stderr`.
    proc = subprocess.Popen(  # noqa: S603 (trust that the command is valid).
        " ".join([qemu_bin] + sys.argv[1:]),
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        bufsize=1,
        shell=True,
        text=True,
    )
    for line in proc.stdout:
        sys.stdout.write(line)
        sys.stdout.flush()
        if "PASS!" in line:
            return proc.wait()
    returncode = proc.wait()
    if returncode == 0:
        # QEMU exited successfully but we didn't see `PASS!`, fail instead.
        return 1
    return returncode


if __name__ == "__main__":
    sys.exit(_main())
