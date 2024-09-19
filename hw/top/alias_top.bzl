# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

def alias_top(name, earlgrey):
    native.alias(
        name = name,
        actual = select({
            "//conditions:default": earlgrey,
        }),
    )

def alias_ip_sw(name, earlgrey):
    for suffix in ["c_regs", "rust_regs"]:
        alias_top(
            name = "{}_{}".format(name, suffix),
            earlgrey = "{}_{}".format(earlgrey, suffix),
        )
