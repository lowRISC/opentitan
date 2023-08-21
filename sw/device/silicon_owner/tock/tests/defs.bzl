# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# TODO(opentitan#19493): These aliases are required because of a defect in the
# implementation of the opentitan_functest rule.  Remove them after fixing the
# opentitan_functest rule.
def tock_functest_setup(name):
    native.alias(
        name = name + "_fpga_cw310",
        actual = ":" + name,
    )
    native.alias(
        name = name + "_fpga_cw310_bin",
        actual = ":" + name,
    )
