# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:opentitan_test.bzl",
    "DEFAULT_TEST_FAILURE_MSG",
    "DEFAULT_TEST_SUCCESS_MSG",
    "cw310_params",
    "dv_params",
    "opentitan_functest",
    "verilator_params",
)

package(default_visibility = ["//visibility:public"])

opentitan_functest(
    name = "rom_e2e_shutdown_exception_c",
    srcs = ["rom_e2e_shutdown_exception_c_test.c"],
    cw310 = cw310_params(
        bitstream = "//hw/bitstream:rom",
        # Note: This test never prints a failure message so it will fail only
        # when it times out.
        exit_failure = "NO_FAILURE_MESSAGE",
        exit_success = "BFV:01495202(?s:.*)BFV:01495202",
    ),
    manifest = "//sw/device/silicon_creator/rom_ext:manifest_standard",
    signed = True,
    targets = [
        "cw310",
        "verilator",
    ],
    verilator = verilator_params(
        timeout = "eternal",
        exit_failure = "NO_FAILURE_MESSAGE",
        exit_success = "BFV:01495202(?s:.*)BFV:01495202",
        rom = "//sw/device/silicon_creator/rom",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/silicon_creator/lib:manifest_def",
        "//sw/device/silicon_creator/lib/base:static_critical_boot_measurements",
        "//sw/device/silicon_creator/lib/base:static_critical_sec_mmio",
        "//sw/device/silicon_creator/rom_ext:ld_slot_a",
    ],
)

opentitan_functest(
    name = "e2e_bootup_success",
    srcs = ["empty_test.c"],
    cw310 = cw310_params(
        bitstream = "//hw/bitstream:rom",
    ),
    dv = dv_params(
        rom = "//sw/device/silicon_creator/rom",
    ),
    manifest = "//sw/device/silicon_creator/rom_ext:manifest_standard",
    signed = True,
    verilator = verilator_params(
        timeout = "eternal",
        rom = "//sw/device/silicon_creator/rom",
    ),
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "rom_e2e_static_critical",
    srcs = ["rom_e2e_static_critical_test.c"],
    cw310 = cw310_params(
        bitstream = "//hw/bitstream:rom",
    ),
    manifest = "//sw/device/silicon_creator/rom_ext:manifest_standard",
    signed = True,
    targets = [
        "cw310",
        "verilator",
    ],
    verilator = verilator_params(
        timeout = "eternal",
        rom = "//sw/device/silicon_creator/rom",
    ),
    deps = [
        "//sw/device/lib/dif:hmac",
        "//sw/device/lib/testing:hmac_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
    ],
)

# Same as `:e2e_bootup_success`, but the Dev OTP image is spliced into the
# bitstream before it's sent to the CW310 FPGA.
opentitan_functest(
    name = "e2e_bootup_success_otp_dev",
    srcs = ["empty_test.c"],
    cw310 = cw310_params(
        bitstream = "//hw/bitstream:rom_otp_dev",
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
        bitstream = "//hw/bitstream:rom",
        exit_failure = DEFAULT_TEST_SUCCESS_MSG,
        exit_success = DEFAULT_TEST_FAILURE_MSG,
    ),
    signed = False,
    verilator = verilator_params(
        exit_failure = DEFAULT_TEST_SUCCESS_MSG,
        exit_success = DEFAULT_TEST_FAILURE_MSG,
        rom = "//sw/device/silicon_creator/rom",
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
        bitstream = "//hw/bitstream:rom",
        test_cmds = [
            "--bitstream=\"$(location //hw/bitstream:rom)\"",
            "--rom-kind=rom",
            "--rom-ext=\"$(location {flash})\"",
        ],
    ),
    manifest = "//sw/device/silicon_creator/rom_ext:manifest_standard",
    signed = True,
    targets = ["cw310"],
    test_harness = "//sw/host/tests/rom/e2e_bootup_bad_rom_ext_signature",
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "e2e_bootstrap_entry",
    srcs = ["empty_test.c"],
    cw310 = cw310_params(
        bitstream = "//hw/bitstream:rom",
        test_cmds = [
            "--rom-kind=rom",
            "--bitstream=\"$(location //hw/bitstream:rom)\"",
            "--bootstrap=\"$(location {flash})\"",
        ],
    ),
    manifest = "//sw/device/silicon_creator/rom_ext:manifest_standard",
    # We don't want the `empty_test` to run, but we _also_ don't want some
    # leftover flash image from a previous test to run.  So, bootstrap an
    # unsigned image to force a boot failure.
    signed = False,
    targets = ["cw310"],
    test_harness = "//sw/host/tests/rom/e2e_bootstrap_entry",
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "e2e_chip_specific_startup",
    srcs = ["chip_specific_startup.c"],
    args = [],
    cw310 = cw310_params(
        bitstream = "//hw/bitstream:rom",
        test_cmds = [
            "--bitstream=\"$(location //hw/bitstream:rom)\"",
            "--rom-kind=rom",
            "--bootstrap=\"$(location {flash})\"",
        ],
    ),
    manifest = "//sw/device/silicon_creator/rom_ext:manifest_standard",
    signed = True,
    targets = ["cw310"],
    test_harness = "//sw/host/tests/rom/e2e_chip_specific_startup",
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:sram_ctrl",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/silicon_creator/rom/e2e/json:chip_specific_startup",
        "//sw/device/silicon_creator/rom/e2e/json:command",
    ],
)
