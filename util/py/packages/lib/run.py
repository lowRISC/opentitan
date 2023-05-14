# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import os
import subprocess

from util.py.packages.lib.ot_logging import log


def run(*args: str) -> list[str]:
    """Run the given command in a subprocess.

    Args:
        args: Command (the first parameter) and arguments (remaining arguments).

    Returns:
        Stdout lines in a list. Empty lines are filtered out.
    """
    log.debug(f"command: {' '.join(args)}")
    try:
        res = subprocess.run(args,
                             env=os.environ.copy(),
                             stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE,
                             encoding='ascii',
                             errors='ignore',
                             check=True)
    except subprocess.CalledProcessError as e:
        log.error(f"stdout: {e.stdout if e.stdout else '(empty)'}")
        log.error(f"stderr: {e.stderr if e.stderr else '(empty)'}")
        raise
    log.debug(f"stdout: {res.stdout if res.stdout else '(empty)'}")
    log.debug(f"stderr: {res.stderr if res.stderr else '(empty)'}")
    return [line for line in res.stdout.splitlines() if line]
