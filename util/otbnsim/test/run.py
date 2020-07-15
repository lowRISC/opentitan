# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from data import pack_list, unpack_list

from otbnsim.standalone import run
from otbnsim.asm import parse

from programs import w04_epilog, w04_prolog


def run_w04(asm, data, *, verbose=False):
    test = w04_prolog + asm + w04_epilog

    data = pack_list(data)

    rdata = run(parse(test), data, verbose=verbose)

    rdata = unpack_list(rdata)

    return rdata
