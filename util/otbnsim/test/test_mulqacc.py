# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import pytest
from run import run_w04


def run(code, a, b, expected, verbose=False):
    rdata = run_w04(code, [a, b, 0, 0], verbose=verbose)
    result = rdata[3] << 256 | rdata[2]
    assert result == expected, "Failed for {:x},{:x}".format(a, b)


testdata = [[0, 0], [1, 1], [4, 4], [2**64 - 1, 2], [2**64 - 1, 2**64 - 1],
            [2**64, 2**64]]


@pytest.mark.parametrize("a,b", testdata)
def test_mulqacc0(a, b, modelverbose):
    insns = """
    bn.mulqacc.wo.z w2.l, w0.0, w1.0, 0
    """

    rdata = run(insns, a, b,
                (a & 0xffffffffffffffff) * (b & 0xffffffffffffffff))
