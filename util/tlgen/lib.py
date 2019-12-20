# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import math
import logging as log


def is_pow2(v):
    """Return true if value is power of two
    """
    if not isinstance(v, int):
        log.warning("is_pow2 received non-integer value {}".format(v))
        return False
    t = 1
    while t <= v:
        if t == v:
            return True
        t = t * 2

    return False
