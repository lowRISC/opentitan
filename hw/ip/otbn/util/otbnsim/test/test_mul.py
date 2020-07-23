# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from random import getrandbits

from programs import code_mul_256x256
import pytest

from run import run_w04


def run(a, b, verbose=False):
    rdata = run_w04(code_mul_256x256, [a, b, 0, 0], verbose=verbose)
    expected = a * b
    result = rdata[3] << 256 | rdata[2]
    assert result == expected, "Failed for {:x},{:x}".format(a, b)


testdata = [[0, 0], [1, 1], [16253673, 9988176667], [1 << 64, 1 << 64],
            [1 << 127, 1 << 127], [1 << 128, 1 << 128], [1 << 128, 1 << 192],
            [1 << 192, 1 << 192], [1 << 256 - 1, 1 << 256 - 1],
            [
                214070112180406960094838604134999454453,
                214070112180406960094838604134999454453
            ]]


@pytest.mark.parametrize("a,b", testdata)
def test_simple(a, b, modelverbose):
    run(a, b, verbose=modelverbose)


def test_mulrandom(modelverbose):
    run(getrandbits(256), getrandbits(256), verbose=modelverbose)
