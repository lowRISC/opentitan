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
load(
    "//rules:opentitan.bzl",
    "opentitan_multislot_flash_binary",
)

package(default_visibility = ["//visibility:public"])

MSG_STARTING_ROM_EXT = "Starting ROM_EXT"

MSG_BOOT_FAULT = "BFV:"

MSG_STORE_ACCESS_FAULT = "BFV:07495202(?s:.*)BFV:07495202"

MSG_ILLEGAL_INSTRUCTION_FAULT = "BFV:02495202(?s:.*)BFV:02495202"

MSG_PASS = "PASS!"

MSG_BAD_KEY = "BFV:02535603(?s:.*)BFV:02535603"

SLOT_A_OFFSET = "0x0"

SLOT_B_OFFSET = "0x80000"

FLASH_SIZE = "0x100000"

opentitan_functest(
    name = "rom_e2e_shutdown_exception_c",
    srcs = ["rom_e2e_shutdown_exception_c_test.c"],
    cw310 = cw310_params(
        # Note: This test never prints a failure message so it will fail only
        # when it times out.
        exit_failure = "NO_FAILURE_MESSAGE",
        exit_success = "BFV:01495202(?s:.*)BFV:01495202",
    ),
    dv = dv_params(
        rom = "//sw/device/silicon_creator/rom",
    ),
    signed = True,
    targets = [
        "dv",
        "cw310_rom",
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
        "//sw/device/silicon_creator/lib/base:static_critical_epmp_state",
        "//sw/device/silicon_creator/lib/base:static_critical_sec_mmio",
    ],
)

opentitan_functest(
    name = "rom_e2e_smoke",
    srcs = ["empty_test.c"],
    cw310 = cw310_params(
        bitstream = "//hw/bitstream:rom",
    ),
    dv = dv_params(
        rom = "//sw/device/silicon_creator/rom",
    ),
    signed = True,
    targets = [
        "cw310_rom",
        "verilator",
        "dv",
    ],
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
    dv = dv_params(
        rom = "//sw/device/silicon_creator/rom",
    ),
    signed = True,
    targets = [
        "dv",
        "cw310_rom",
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
    signed = True,
    targets = ["cw310_rom"],
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "e2e_bootup_no_rom_ext_signature",
    srcs = ["empty_test.c"],
    cw310 = cw310_params(
        exit_failure = DEFAULT_TEST_SUCCESS_MSG,
        exit_success = DEFAULT_TEST_FAILURE_MSG,
    ),
    signed = False,
    targets = ["cw310_rom"],
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
        test_cmds = [
            "--bitstream=\"$(location //hw/bitstream:rom)\"",
            "--rom-kind=rom",
            "--rom-ext=\"$(location {flash})\"",
        ],
    ),
    signed = True,
    targets = ["cw310_rom"],
    test_harness = "//sw/host/tests/rom/e2e_bootup_bad_rom_ext_signature",
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "e2e_bootstrap_entry",
    srcs = ["empty_test.c"],
    cw310 = cw310_params(
        test_cmds = [
            "--rom-kind=rom",
            "--bitstream=\"$(location //hw/bitstream:rom)\"",
            "--bootstrap=\"$(location {flash})\"",
        ],
    ),
    # We don't want the `empty_test` to run, but we _also_ don't want some
    # leftover flash image from a previous test to run.  So, bootstrap an
    # unsigned image to force a boot failure.
    signed = False,
    targets = ["cw310_rom"],
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
        test_cmds = [
            "--rom-kind=rom",
            "--bitstream=\"$(location //hw/bitstream:rom)\"",
            "--bootstrap=\"$(location {flash})\"",
        ],
    ),
    signed = True,
    targets = ["cw310_rom"],
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

opentitan_functest(
    name = "rom_ext_a_flash_a",
    cw310 = cw310_params(
        exit_failure = MSG_BOOT_FAULT,
        exit_success = MSG_STARTING_ROM_EXT,
    ),
    ot_flash_binary = "//sw/device/silicon_creator/rom_ext:rom_ext_slot_a",
    targets = ["cw310_rom"],
)

opentitan_multislot_flash_binary(
    name = "rom_ext_b_flash_b_image",
    srcs = {
        "//sw/device/silicon_creator/rom_ext:rom_ext_slot_b": {
            "key": "test_key_0",
            "offset": SLOT_B_OFFSET,
        },
    },
    image_size = FLASH_SIZE,
)

opentitan_functest(
    name = "rom_ext_b_flash_b",
    cw310 = cw310_params(
        exit_failure = MSG_BOOT_FAULT,
        exit_success = MSG_STARTING_ROM_EXT,
    ),
    key = "multislot",
    ot_flash_binary = ":rom_ext_b_flash_b_image",
    targets = ["cw310_rom"],
)

opentitan_multislot_flash_binary(
    name = "rom_ext_a_flash_b_image",
    srcs = {
        "//sw/device/silicon_creator/rom_ext:rom_ext_slot_a": {
            "key": "test_key_0",
            "offset": SLOT_B_OFFSET,
        },
    },
    image_size = FLASH_SIZE,
)

opentitan_functest(
    name = "rom_ext_a_flash_b",
    cw310 = cw310_params(
        exit_failure = MSG_STARTING_ROM_EXT,
        exit_success = MSG_STORE_ACCESS_FAULT,
    ),
    key = "multislot",
    ot_flash_binary = ":rom_ext_a_flash_b_image",
    targets = ["cw310_rom"],
)

opentitan_multislot_flash_binary(
    name = "rom_ext_b_flash_a_image",
    srcs = {
        "//sw/device/silicon_creator/rom_ext:rom_ext_slot_b": {
            "key": "test_key_0",
            "offset": SLOT_A_OFFSET,
        },
    },
    image_size = FLASH_SIZE,
)

opentitan_functest(
    name = "rom_ext_b_flash_a",
    cw310 = cw310_params(
        exit_failure = MSG_STARTING_ROM_EXT,
        exit_success = MSG_STORE_ACCESS_FAULT,
    ),
    key = "multislot",
    ot_flash_binary = ":rom_ext_b_flash_a_image",
    targets = ["cw310_rom"],
)

opentitan_functest(
    name = "rom_ext_v_flash_a",
    cw310 = cw310_params(
        exit_failure = MSG_BOOT_FAULT,
        exit_success = MSG_STARTING_ROM_EXT,
    ),
    ot_flash_binary = "//sw/device/silicon_creator/rom_ext:rom_ext_slot_virtual",
    targets = ["cw310_rom"],
)

opentitan_multislot_flash_binary(
    name = "rom_ext_v_flash_b_image",
    srcs = {
        "//sw/device/silicon_creator/rom_ext:rom_ext_slot_virtual": {
            "key": "test_key_0",
            "offset": SLOT_B_OFFSET,
        },
    },
    image_size = FLASH_SIZE,
)

opentitan_functest(
    name = "rom_ext_v_flash_b",
    cw310 = cw310_params(
        exit_failure = MSG_BOOT_FAULT,
        exit_success = MSG_STARTING_ROM_EXT,
    ),
    key = "multislot",
    ot_flash_binary = ":rom_ext_v_flash_b_image",
    targets = ["cw310_rom"],
)

opentitan_functest(
    name = "rom_ext_a_flash_a_bad_addr_trans",
    cw310 = cw310_params(
        exit_failure = MSG_STARTING_ROM_EXT,
        exit_success = MSG_ILLEGAL_INSTRUCTION_FAULT,
    ),
    ot_flash_binary = "//sw/device/silicon_creator/rom_ext:rom_ext_slot_a_bad_address_translation",
    targets = ["cw310_rom"],
)

test_suite(
    name = "address_translation",
    tests = [
        "rom_ext_a_flash_a",
        "rom_ext_a_flash_a_bad_addr_trans",
        "rom_ext_a_flash_b",
        "rom_ext_b_flash_a",
        "rom_ext_b_flash_b",
        "rom_ext_v_flash_a",
        "rom_ext_v_flash_b",
    ],
)

opentitan_functest(
    name = "sigverify_key_auth",
    srcs = ["empty_test.c"],
    cw310 = cw310_params(
        exit_failure = MSG_PASS,
        exit_success = MSG_BAD_KEY,
    ),
    key = "unauthorized_0",
    signed = True,
    targets = ["cw310_rom"],
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)
