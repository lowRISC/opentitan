# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Shared subfunctions.
"""
import logging as log
import textwrap


def wrapped_docstring():
    '''Return a text-wrapped version of the module docstring'''
    paras = []
    para = []
    for line in __doc__.strip().split('\n'):
        line = line.strip()
        if not line:
            if para:
                paras.append('\n'.join(para))
                para = []
        else:
            para.append(line)
    if para:
        paras.append('\n'.join(para))

    return '\n\n'.join(textwrap.fill(p) for p in paras)


def check_bool(x):
    """check_bool checks if input 'x' either a bool or
       one of the following strings: ["true", "false"]

        It returns value as Bool type.
    """
    if isinstance(x, bool):
        return x
    if not x.lower() in ["true", "false"]:
        log.error("{} is not a boolean value.".format(x))
        exit(1)
    else:
        return (x.lower() == "true")


def check_int(x):
    """check_int checks if input 'x' is decimal integer.

        It returns value as an int type.
    """
    if isinstance(x, int):
        return x
    if not x.isdecimal():
        log.error("{} is not a decimal number".format(x))
        exit(1)
    return int(x)
