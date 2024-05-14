# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//lib:dicts.bzl", "dicts")
load("@rules_rust//rust:defs.bzl", "rust_binary")
load("//rules:signing.bzl", "sign_bin")
load("//rules:tock.bzl", "tock_elf2tab", "tock_image")
load("//rules/opentitan:defs.bzl", "EARLGREY_SILICON_OWNER_ROM_EXT_ENVS", "OPENTITAN_CPU", "cw310_params", "opentitan_test", "silicon_params")

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
    flash_start = 0x20040000,
)

tock_image(
    name = "image",
    apps = [":tab"],
    exec_env = "//hw/top_earlgrey:silicon_owner_sival_rom_ext",
    kernel = "//sw/device/silicon_owner/tock/tests:test_kernel",
)

opentitan_test(
    name = "basic_test",
    # Note: tock_image currently create a sival_rom_ext-only image.
    exec_env = {"//hw/top_earlgrey:silicon_owner_sival_rom_ext": None},
    silicon = silicon_params(
        binaries = {":image": "firmware"},
    ),
)
