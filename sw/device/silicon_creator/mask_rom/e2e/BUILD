# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "OPENTITAN_CPU", "opentitan_flash_binary")
load(
    "//rules:opentitan_test.bzl",
    "cw310_params",
    "opentitan_functest",
    "verilator_params",
)

package(default_visibility = ["//visibility:public"])

BOOT_FAILURE_MSG = "BFV:[0-9a-f]{8}"

BOOT_SUCCESS_MSG = "PASS!"

opentitan_functest(
    name = "e2e_bootup_success",
    srcs = ["empty_test.c"],
    cw310 = cw310_params(
        bitstream = "//hw/bitstream:mask_rom",
        exit_failure = BOOT_FAILURE_MSG,
        exit_success = BOOT_SUCCESS_MSG,
    ),
    manifest = "//sw/device/silicon_creator/rom_ext:manifest_standard",
    signed = True,
    verilator = verilator_params(
        exit_failure = BOOT_FAILURE_MSG,
        exit_success = BOOT_SUCCESS_MSG,
        rom = "//sw/device/silicon_creator/mask_rom",
        # Note: Leaving as broken since this test takes a long time and
        # we don't really need it as long as the CI runs the FPGA version.
        tags = [
            "broken",
        ],
    ),
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

# Same as `:e2e_bootup_success`, but the Dev OTP image is spliced into the
# bitstream before it's sent to the CW310 FPGA.
opentitan_functest(
    name = "e2e_bootup_success_otp_dev",
    srcs = ["empty_test.c"],
    cw310 = cw310_params(
        bitstream = "//hw/bitstream:mask_rom_otp_dev",
        exit_failure = BOOT_FAILURE_MSG,
        exit_success = BOOT_SUCCESS_MSG,
        # TODO(lowRISC/opentitan#13603): Remove this "manual" tag when the
        # bitstream target can fetch pre-spliced bitstream from GCP.
        tags = ["manual"],
    ),
    manifest = "//sw/device/silicon_creator/rom_ext:manifest_standard",
    signed = True,
    targets = ["cw310"],
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "e2e_bootup_no_rom_ext_signature",
    srcs = ["empty_test.c"],
    cw310 = cw310_params(
        bitstream = "//hw/bitstream:mask_rom",
        exit_failure = BOOT_SUCCESS_MSG,
        exit_success = BOOT_FAILURE_MSG,
    ),
    signed = False,
    verilator = verilator_params(
        exit_failure = BOOT_SUCCESS_MSG,
        exit_success = BOOT_FAILURE_MSG,
        rom = "//sw/device/silicon_creator/mask_rom",
    ),
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "e2e_bootup_bad_rom_ext_signature",
    srcs = ["empty_test.c"],
    args = [],
    cw310 = cw310_params(
        args = [
            "--bitstream=\"$(location //hw/bitstream:mask_rom)\"",
            "--rom-kind=maskrom",
            "--rom-ext=\"$(location {flash})\"",
        ],
        bitstream = "//hw/bitstream:mask_rom",
    ),
    signed = True,
    targets = ["cw310"],
    test_harness = "//sw/host/tests/mask_rom/e2e_bootup_bad_rom_ext_signature",
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)
