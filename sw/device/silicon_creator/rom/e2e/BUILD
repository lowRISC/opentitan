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
    "opentitan_flash_binary",
    "opentitan_multislot_flash_binary",
)
load(
    "//rules:manifest.bzl",
    "CONST",
    "manifest",
)

package(default_visibility = ["//visibility:public"])

MSG_STARTING_ROM_EXT = "Starting ROM_EXT"

MSG_BOOT_FAULT = "BFV:"

MSG_STORE_ACCESS_FAULT = "BFV:07495202(?s:.*)BFV:07495202"

MSG_ILLEGAL_INSTRUCTION_FAULT = "BFV:02495202(?s:.*)BFV:02495202"

MSG_PASS = "PASS!"

MSG_BAD_KEY = "BFV:02535603(?s:.*)BFV:02535603"

SLOTS = [
    "a",
    "b",
]

SLOT_A_OFFSET = "0x0"

SLOT_B_OFFSET = "0x80000"

opentitan_flash_binary(
    name = "empty_test_slot_a",
    srcs = ["empty_test.c"],
    devices = [
        "fpga_cw310",
        "sim_dv",
        "sim_verilator",
    ],
    signed = True,
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "@//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
    ],
)

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
    cw310 = cw310_params(
        bitstream = "//hw/bitstream:rom",
    ),
    dv = dv_params(
        rom = "//sw/device/silicon_creator/rom",
    ),
    key = "test_key_0",
    ot_flash_binary = ":empty_test_slot_a",
    targets = [
        "cw310_rom",
        "verilator",
        "dv",
    ],
    verilator = verilator_params(
        timeout = "eternal",
        rom = "//sw/device/silicon_creator/rom",
    ),
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

opentitan_functest(
    name = "e2e_keymgr_init",
    srcs = ["rom_e2e_keymgr_init_test.c"],
    signed = True,
    targets = [
        "cw310_rom",
        "verilator",
    ],
    verilator = verilator_params(
        timeout = "eternal",
        rom = "//sw/device/silicon_creator/rom",
    ),
    deps = [
        "//sw/device/lib/dif:keymgr",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

# Same as `:e2e_bootup_success`, but the Dev OTP image is spliced into the
# bitstream before it's sent to the CW310 FPGA.
opentitan_functest(
    name = "e2e_bootup_success_otp_dev",
    cw310 = cw310_params(
        bitstream = "//hw/bitstream:rom_otp_dev",
        # TODO(lowRISC/opentitan#13603): Remove this "manual" tag when the
        # bitstream target can fetch pre-spliced bitstream from GCP.
        tags = ["manual"],
    ),
    key = "test_key_0",
    ot_flash_binary = ":empty_test_slot_a",
    targets = ["cw310_rom"],
)

opentitan_functest(
    name = "e2e_bootup_no_rom_ext_signature",
    cw310 = cw310_params(
        exit_failure = DEFAULT_TEST_SUCCESS_MSG,
        exit_success = DEFAULT_TEST_FAILURE_MSG,
    ),
    ot_flash_binary = ":empty_test_slot_a",
    signed = False,
    targets = ["cw310_rom"],
    verilator = verilator_params(
        exit_failure = DEFAULT_TEST_SUCCESS_MSG,
        exit_success = DEFAULT_TEST_FAILURE_MSG,
        rom = "//sw/device/silicon_creator/rom",
    ),
)

opentitan_functest(
    name = "e2e_bootup_bad_rom_ext_signature",
    args = [],
    cw310 = cw310_params(
        test_cmds = [
            "--bitstream=\"$(location //hw/bitstream:rom)\"",
            "--rom-kind=rom",
            "--rom-ext=\"$(location {flash})\"",
        ],
    ),
    key = "test_key_0",
    ot_flash_binary = ":empty_test_slot_a",
    targets = ["cw310_rom"],
    test_harness = "//sw/host/tests/rom/e2e_bootup_bad_rom_ext_signature",
)

opentitan_functest(
    name = "e2e_bootstrap_entry",
    cw310 = cw310_params(
        test_cmds = [
            "--rom-kind=rom",
            "--bitstream=\"$(location //hw/bitstream:rom)\"",
            "--bootstrap=\"$(location {flash})\"",
        ],
    ),
    ot_flash_binary = ":empty_test_slot_a",
    # We don't want the `empty_test` to run, but we _also_ don't want some
    # leftover flash image from a previous test to run.  So, bootstrap an
    # unsigned image to force a boot failure.
    signed = False,
    targets = ["cw310_rom"],
    test_harness = "//sw/host/tests/rom/e2e_bootstrap_entry",
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
        "//sw/device/lib/testing/json:chip_specific_startup",
        "//sw/device/lib/testing/json:command",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
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
    cw310 = cw310_params(
        exit_failure = MSG_PASS,
        exit_success = MSG_BAD_KEY,
    ),
    key = "unauthorized_0",
    ot_flash_binary = ":empty_test_slot_a",
    targets = ["cw310_rom"],
)

MSG_SHUTDOWN = {
    "test": "BFV:0142500d\r\nLCV:02108421\r\n",
    "dev": "BFV:0142500d\r\nLCV:21084210\r\n",
    "prod": "BFV:0142500d\r\nLCV:2318c631\r\n",
    "prod_end": "BFV:0142500d\r\nLCV:25294a52\r\n",
    "rma": "BFV:0142500d\r\nLCV:2739ce73\r\n",
}

LC_STATES = ["rma"]

manifest(
    name = "manifest_bad_identifier",
    address_translation = CONST.FALSE,
    identifier = 0,
)

# TODO(#14270): Add remaining lifecycle states.
[opentitan_functest(
    name = "shutdown_output_{}".format(lc_state),
    cw310 = cw310_params(
        bitstream = "@//hw/bitstream:rom",
        exit_failure = MSG_PASS,
        exit_success = MSG_SHUTDOWN[lc_state],
    ),
    manifest = ":manifest_bad_identifier",
    ot_flash_binary = ":empty_test_slot_a",
    signed = False,
    targets = ["cw310_rom"],
) for lc_state in LC_STATES]

test_suite(
    name = "shutdown_output",
    tests = ["shutdown_output_{}".format(lc_state) for lc_state in LC_STATES],
)

SEC_VERS = [
    0,
    1,
]

[manifest(
    name = "manifest_sec_ver_{}".format(sec_ver),
    address_translation = CONST.FALSE,
    identifier = CONST.ROM_EXT,
    security_version = sec_ver,
) for sec_ver in SEC_VERS]

[opentitan_flash_binary(
    name = "empty_test_slot_{}_sec_ver_{}".format(slot, sec_ver),
    srcs = ["empty_test.c"],
    devices = ["fpga_cw310"],
    local_defines = [
        "EMPTY_TEST_MSG=\"slot={} security_version={}\"".format(slot, sec_ver),
    ],
    manifest = ":manifest_sec_ver_{}".format(sec_ver),
    signed = True,
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "@//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_{}".format(slot),
    ],
) for slot in SLOTS for sec_ver in SEC_VERS]

[opentitan_multislot_flash_binary(
    name = "sec_ver_{}_{}_image".format(sec_ver_a, sec_ver_b),
    srcs = {
        ":empty_test_slot_a_sec_ver_{}".format(sec_ver_a): {
            "key": "test_key_0",
            "offset": SLOT_A_OFFSET,
        },
        ":empty_test_slot_b_sec_ver_{}".format(sec_ver_b): {
            "key": "test_key_0",
            "offset": SLOT_B_OFFSET,
        },
    },
    devices = ["fpga_cw310"],
) for sec_ver_a in SEC_VERS for sec_ver_b in SEC_VERS]

# [[sec_ver_a, sec_ver_b, correct_slot, correct_sec_ver], ...]
BOOT_POLICY_NEWER_CASES = [
    [
        0,
        0,
        "a",
        0,
    ],
    [
        0,
        1,
        "b",
        1,
    ],
    [
        1,
        0,
        "a",
        1,
    ],
    [
        1,
        1,
        "a",
        1,
    ],
]

[opentitan_functest(
    name = "boot_policy_newer_a_{}_b_{}".format(sec_ver_a, sec_ver_b),
    cw310 = cw310_params(
        exit_success = "slot={} security_version={}".format(correct_slot, correct_sec_ver),
    ),
    key = "multislot",
    ot_flash_binary = ":sec_ver_{}_{}_image".format(sec_ver_a, sec_ver_b),
    targets = ["cw310_rom"],
) for sec_ver_a, sec_ver_b, correct_slot, correct_sec_ver in BOOT_POLICY_NEWER_CASES]

test_suite(
    name = "boot_policy_newer",
    tests = ["boot_policy_newer_a_{}_b_{}".format(sec_ver_a, sec_ver_b) for sec_ver_a, sec_ver_b, _, _ in BOOT_POLICY_NEWER_CASES],
)
