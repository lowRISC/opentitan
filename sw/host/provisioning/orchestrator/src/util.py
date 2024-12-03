# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging
import shlex
import subprocess


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


def read_int_as_decimal_str(x: int) -> int:
    """Interpret a number by reading its hexadecimal representation as a decimal number.

    For example, `70` in hex is `0x46` and should be read as the decimal value 46.
    This encoding is a manufacturing equipment constraint.
    """
    return int(hex(x)[2:])


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
