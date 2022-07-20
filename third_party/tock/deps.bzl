# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//third_party/tock/crates:crates.bzl", "raze_fetch_remote_crates")

def tock_deps(tock=None, libtock=None):
    raze_fetch_remote_crates(
        capsules__0_1_0=tock,
        components__0_1_0=tock,
        earlgrey__0_1_0=tock,
        earlgrey_cw310__0_1_0=tock,
        enum_primitive__0_1_0=tock,
        kernel__0_1_0=tock,
        lowrisc__0_1_0=tock,
        riscv__0_1_0=tock,
        riscv_csr__0_1_0=tock,
        rv32i__0_1_0=tock,
        tickv__1_0_0=tock,
        tock_cells__0_1_0=tock,
        tock_registers__0_7_0=tock,
        tock_tbf__0_1_0=tock,

        libtock2__0_1_0=libtock,
        libtock_buttons__0_1_0=libtock,
        libtock_console__0_1_0=libtock,
        libtock_debug_panic__0_1_0=libtock,
        libtock_leds__0_1_0=libtock,
        libtock_low_level_debug__0_1_0=libtock,
        libtock_platform__0_1_0=libtock,
        libtock_runtime__0_1_0=libtock,
    )
