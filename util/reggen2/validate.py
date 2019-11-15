# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Register json validation
"""

import logging as log
import sys


# Routine that can be used for hjson object_pairs_hook
# The baseline is dict(pairs) i.e. construct a dictonary from pairs
# The usual is OrderedDict(pairs) which is redundant in latest python
# Both of these silently allow repeated keys, which this version detects
def checking_dict(pairs):
    d = {}
    for x in pairs:
        if x[0] in d:
            repkey = 'Repeated' + x[0]
            log.warn("Repeated key " + x[0] + " added as " + repkey)
            d[repkey] = x[1]
        else:
            d[x[0]] = x[1]
    return d


# validating version of int(x, 0)
# returns int value, error flag
# if error flag is True value will be zero
def check_int(x, err_prefix):
    if isinstance(x, int):
        return x, False
    if x[0] == '0' and len(x) > 2:
        if x[1] in 'bB':
            validch = '01'
        elif x[1] in 'oO':
            validch = '01234567'
        elif x[1] in 'xX':
            validch = '0123456789abcdefABCDEF'
        else:
            log.error(err_prefix +
                      ": int must start digit, 0b, 0B, 0o, 0O, 0x or 0X")
            return 0, True
        for c in x[2:]:
            if not c in validch:
                log.error(err_prefix + ": Bad character " + c + " in " + x)
                return 0, True
    else:
        if not x.isdecimal():
            log.error(err_prefix + ": Number not valid int " + x)
            return 0, 1
    return int(x, 0), False


def check_bits(x, err_prefix):
    """Return bit slice
    """
    msb, lsb = 0, 0
    split_x = x.split(':')
    msb, error = check_int(split_x[0], err_prefix)
    if len(split_x) != 1:
        # Can be split by ':'
        lsb, error = check_int(split_x[1], err_prefix)
    else:
        lsb = msb

    return msb, lsb


def validate(block, **kwargs):
    if "params" in kwargs:
        params = kwargs["params"]
    else:
        params = []

    if not 'name' in block:
        log.error("Component has no name. Aborting.")
        return 1

    # Check name and convert to lowercase
    component = block['name'].lower()
    if component != block['name']:
        log.warning(f"Block name {block['name']} is changed to lowercase.")
        block['name'] = component

    if 'api' in block and block['api'] != '2':
        log.error("This tool supports only Version 2 API")
        raise SystemExit("This tool supports only Version 2 API")

    # TODO: Validate Param

    # TODO: Validate Register format block['registers']

    return 0  # no error
