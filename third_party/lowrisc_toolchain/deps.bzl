# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "@bazel_embedded//toolchains/lowrisc_toolchain_rv32imc:lowrisc_toolchain_rv32imc.bzl",
    "register_lowrisc_toolchain_rv32imc_toolchain",
)

def lowrisc_toolchain_deps():
    register_lowrisc_toolchain_rv32imc_toolchain()
