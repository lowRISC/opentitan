# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

py_binary(
    name = "otpconv",
    srcs = ["@qemu-ot//:scripts/opentitan/otpconv.py"],
)

py_binary(
    name = "flashgen",
    srcs = ["@qemu-ot//:scripts/opentitan/flashgen.py"],
)

alias(
    name = "qemu_system_riscv32",
    actual = "@qemu-ot//:build/qemu-system-riscv32",
)

alias(
    name = "qemu_img",
    actual = "@qemu-ot//:build/qemu-img",
)
