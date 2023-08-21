# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary")
load("//rules:tock.bzl", "tock_elf2tab", "tock_image")
load("//rules:opentitan_test.bzl", "cw310_params", "opentitan_functest")
load("//sw/device/silicon_owner/tock/tests:defs.bzl", "tock_functest_setup")
load("//rules:opentitan.bzl", "OPENTITAN_CPU")

package(default_visibility = ["//visibility:public"])

rust_binary(
    name = "basic",
    srcs = [
        "src/basic.rs",
    ],
    # We specifically restrict our build target to the OpenTitan
    # CPU because libtock does not support an x86_64 target.
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/silicon_owner/tock/apps:single_app_layout",
        "@libtock",
    ],
)

tock_elf2tab(
    name = "tab",
    src = ":basic",
    arch = "rv32imc",
)

tock_image(
    name = "image",
    app_flash_start = 0x20040000,
    apps = [":tab"],
    kernel = "//sw/device/silicon_owner/tock/tests:test_kernel",
)

# This macro creates aliases to meet the naming conventions assumed by opentitan_functest.
tock_functest_setup(
    name = "image",
)

opentitan_functest(
    name = "basic_test",
    # TODO(tock#3639, opentitan#19479): Tock needs to update the earlgrey chip
    # config to use the new fpga_cw310 clock frequencies.
    cw310 = cw310_params(
        tags = ["broken"],
    ),
    ot_flash_binary = ":image",
    signed = False,
    targets = [
        # For now, this only runs on the FPGA.  The verilator target requires
        # a vmem file, which is currently expected to be created by the rule
        # supplying the binary.  Since we don't do that yet, the verilator
        # target is not supported.
        "cw310_test_rom",
    ],
)
