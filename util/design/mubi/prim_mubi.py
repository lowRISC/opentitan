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
MUBI_SW_TPL_PATH = "util/design/data/multibits.h.tpl"
MUBI_SW_ASM_TPL_PATH = "util/design/data/multibits_asm.h.tpl"

MUBI_PKG_OUT_PATH = "hw/ip/prim/rtl/prim_mubi_pkg.sv"
MUBI_CORE_OUT_PATH = "hw/ip/prim/prim_mubi.core"
MUBI_SENDER_OUT_PATH = "hw/ip/prim/rtl/prim_mubi{}_sender.sv"
MUBI_SYNC_OUT_PATH = "hw/ip/prim/rtl/prim_mubi{}_sync.sv"
MUBI_DEC_OUT_PATH = "hw/ip/prim/rtl/prim_mubi{}_dec.sv"
MUBI_SW_OUT_PATH = "sw/device/lib/base/multibits.h"
MUBI_SW_ASM_OUT_PATH = "sw/device/lib/base/multibits_asm.h"

N_MAX_NIBBLES = 4


def is_width_valid(width):
    return (width % 4 == 0) and (width // 4 <= N_MAX_NIBBLES) and (width > 0)


def mubi_value_as_hexstr(sel: bool, width: int):

    if is_width_valid(width):
        nibble = int(width / 4)
    else:
        raise ValueError(f'mubi does not support width of {width}')

    true_val = ''
    false_val = ''

    # Note that changing this encoding has implications on isolation cell
    # values in RTL. Do not change this unless absolutely needed.
    for k in range(1, nibble + 1):
        true_val = ('6' if (k % 2) else '9') + true_val
        false_val = ('9' if (k % 2) else '6') + false_val

    return true_val if sel else false_val


def mubi_value_as_int(sel: bool, width: int):
    return int(mubi_value_as_hexstr(sel, width), 16)


def get_c_path():
    return MUBI_SW_OUT_PATH


def gen():

    tpls = [
        (MUBI_PKG_TPL_PATH, MUBI_PKG_OUT_PATH),
        (MUBI_CORE_TPL_PATH, MUBI_CORE_OUT_PATH),
        (MUBI_SW_TPL_PATH, MUBI_SW_OUT_PATH),
        (MUBI_SW_ASM_TPL_PATH, MUBI_SW_ASM_OUT_PATH),
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
