#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Converts mubi mako templates
"""
from mako.template import Template

MUBI_PKG_TPL_PATH = "util/design/data/prim_mubi_pkg.sv.tpl"
MUBI_CORE_TPL_PATH = "util/design/data/prim_mubi.core.tpl"
MUBI_SENDER_TPL_PATH = "util/design/data/prim_mubi_sender.sv.tpl"
MUBI_SYNC_TPL_PATH = "util/design/data/prim_mubi_sync.sv.tpl"
MUBI_DEC_TPL_PATH = "util/design/data/prim_mubi_dec.sv.tpl"

MUBI_PKG_OUT_PATH = "hw/ip/prim/rtl/prim_mubi_pkg.sv"
MUBI_CORE_OUT_PATH = "hw/ip/prim/prim_mubi.core"
MUBI_SENDER_OUT_PATH = "hw/ip/prim/rtl/prim_mubi{}_sender.sv"
MUBI_SYNC_OUT_PATH = "hw/ip/prim/rtl/prim_mubi{}_sync.sv"
MUBI_DEC_OUT_PATH = "hw/ip/prim/rtl/prim_mubi{}_dec.sv"

N_MAX_NIBBLES = 4


def is_width_valid(width):
    return width % 4 == 0


def mubi_value(sel: bool, width: int):

    if is_width_valid(width):
        nibble = int(width / 4)
    else:
        raise ValueError(f'mubi does not support width of {width}')

    true_val = ''
    false_val = ''

    for k in range(1, nibble + 1):
        true_val = ('A' if (k % 2) else '5') + true_val
        false_val = ('5' if (k % 2) else 'A') + false_val

    return true_val if sel else false_val


def main():

    tpls = [
        (MUBI_PKG_TPL_PATH, MUBI_PKG_OUT_PATH),
        (MUBI_CORE_TPL_PATH, MUBI_CORE_OUT_PATH),
    ]
    for tpl, out in tpls:
        with open(tpl) as inf:
            reg_tpl = Template(inf.read())
            with open(out, 'w') as outf:
                outf.write(reg_tpl.render(n_max_nibbles=N_MAX_NIBBLES))

    tpls = [
        (MUBI_SENDER_TPL_PATH, MUBI_SENDER_OUT_PATH),
        (MUBI_SYNC_TPL_PATH, MUBI_SYNC_OUT_PATH),
        (MUBI_DEC_TPL_PATH, MUBI_DEC_OUT_PATH)
    ]
    for tpl, out in tpls:
        with open(tpl) as inf:
            reg_tpl = Template(inf.read())
            for n in range(1, N_MAX_NIBBLES + 1):
                n_bits = n * 4
                with open(out.format(n_bits), 'w') as outf:
                    outf.write(reg_tpl.render(n_bits=n_bits))


if __name__ == "__main__":
    main()
