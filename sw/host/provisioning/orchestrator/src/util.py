# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging
import os
import shlex
import subprocess

from python.runfiles import Runfiles


def parse_hexstring_to_int(x):
    """Accepts hexstrings with and without the 0x."""
    return int(x, 16)


def parse_str_to_ascii_bytes(s):
    return bytes(s, encoding="ascii")


def bytes_to_int(b):
    return int.from_bytes(b, byteorder="little")


def format_hex(n, width=8):
    """format_hex(5, width=4) -> '0x0005'"""
    return format(n, f"#0{width + 2}x")  # + 2 to account for 0x chars


def bcd_decode(x: int) -> int:
    """Convert a BCD int to an int.

    For example, `0x46` hex represents `46` decimal.
    This encoding is a manufacturing equipment constraint.
    """
    return int(hex(x)[2:])


def bcd_encode(x: int) -> int:
    """Converts an int to a BCD int.

    For example, `46` decimal is encoded as `0x46`.
    """
    return int(str(x), 16)


def confirm():
    """Get user confirmation to continue."""
    confirm = input("Type confirm to continue: ")
    if confirm != "confirm":
        logging.info("Did not receive confirmation from user. Aborting.")
        exit(1)


def run(cmd, stdout_logfile, stderr_logfile):
    out_tee = subprocess.Popen(['/usr/bin/tee', stdout_logfile],
                               stdin=subprocess.PIPE)
    err_tee = subprocess.Popen(['/usr/bin/tee', stderr_logfile],
                               stdin=subprocess.PIPE)

    cmd_list = shlex.split(cmd)
    res = subprocess.run(cmd_list,
                         text=True,
                         stdout=out_tee.stdin,
                         stderr=err_tee.stdin)
    out_tee.stdin.close()
    err_tee.stdin.close()
    return res


_runfiles = Runfiles.Create()


def resolve_runfile(path):
    """Resolves path to runfile.

    Relative paths specified as external/<repo>/... will be resolved relative to
    the external repository @<repo>. Otherwise, relative paths will be resolved
    relative to the main workspace. Absolute paths are returned as-is.

    Raises a ValueError if the path does not exist on the filesystem.
    """

    # orchestrator.py assumes the "old" style of runfiles tree, where paths to
    # files within the main workspace do not include the repo name and external
    # deps prepend external/.
    #
    # The old scheme does not work within a zipped py_binary, so this logic is a
    # hack to fix up the supplied path.
    #
    # See https://docs.google.com/document/d/1skNx5o-8k5-YXUAyEETvr39eKoh9fecJbGUquPh5iy8/edit.
    REPO = "lowrisc_opentitan"
    if path.startswith("external/"):
        corrected_path = path[len("external/"):]
    else:
        corrected_path = os.path.join(REPO, path)

    resolved = _runfiles.Rlocation(corrected_path)
    if resolved is None or not os.path.exists(resolved):
        raise ValueError(f"Could not find runfile: {path}")
    return resolved
