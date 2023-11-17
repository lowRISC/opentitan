# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:const.bzl", "CONST", "get_lc_items")
load("//rules:lc.bzl", "lc_raw_unlock_token")
load(
    "//rules:opentitan.bzl",
    "RSA_ONLY_KEY_STRUCTS",
)
load("//rules:otp.bzl", "otp_image")
load("//rules:splice.bzl", "bitstream_splice")
load(
    "//rules/opentitan:defs.bzl",
    "cw310_jtag_params",
    "hyper310_jtag_params",
    "opentitan_binary",
    "opentitan_test",
    "rsa_key_for_lc_state",
    "silicon_jtag_params",
)

_TEST_UNLOCKED_LC_ITEMS = get_lc_items(
    CONST.LCV.TEST_UNLOCKED0,
    CONST.LCV.TEST_UNLOCKED1,
    CONST.LCV.TEST_UNLOCKED2,
    CONST.LCV.TEST_UNLOCKED3,
    CONST.LCV.TEST_UNLOCKED4,
    CONST.LCV.TEST_UNLOCKED5,
    CONST.LCV.TEST_UNLOCKED6,
    CONST.LCV.TEST_UNLOCKED7,
)

_TEST_LOCKED_LC_ITEMS = get_lc_items(
    CONST.LCV.TEST_LOCKED0,
    CONST.LCV.TEST_LOCKED1,
    CONST.LCV.TEST_LOCKED2,
    CONST.LCV.TEST_LOCKED3,
    CONST.LCV.TEST_LOCKED4,
    CONST.LCV.TEST_LOCKED5,
    CONST.LCV.TEST_LOCKED6,
)

_MISSION_MODE_LC_ITEMS = get_lc_items(
    CONST.LCV.DEV,
    CONST.LCV.PROD,
    CONST.LCV.PROD_END,
    CONST.LCV.RMA,
)

_PROD_LC_ITEMS = get_lc_items(
    CONST.LCV.PROD,
    CONST.LCV.PROD_END,
)

_ALL_LC_ITEMS = (
    _TEST_LOCKED_LC_ITEMS +
    _TEST_UNLOCKED_LC_ITEMS +
    _MISSION_MODE_LC_ITEMS
)

# When running a test in TEST_LOCKED state, we will not actually run any code but
# we still need to sign it with a key. This will use the default key.
_MANUF_TEST_LOCKED_KEY = None

# We bootstrap code into flash in LC states where CPU execution is enabled. In
# other LC states, we do not perform bootstrap, as it will not succeed.
[
    opentitan_test(
        name = "manuf_scrap_functest_{}".format(lc_state.lower()),
        srcs = ["empty_functest.c"],
        cw310 = cw310_jtag_params(
            bitstream = "//hw/bitstream:rom_with_fake_keys_otp_{}".format(lc_state.lower()),
            lc_state = lc_state,  # will be expanded in test_cmd
            tags = ["manuf"],
            test_cmd = (
                "" if (
                    (lc_state, lc_val) in _TEST_LOCKED_LC_ITEMS
                ) else "--bootstrap={firmware}"
            ) + " --initial-lc-state={lc_state}",
            test_harness = "//sw/host/tests/manuf/manuf_scrap",
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
            "//hw/top_earlgrey:fpga_hyper310_rom_with_fake_keys": None,
        },
        hyper310 = hyper310_jtag_params(
            bitstream = "//hw/bitstream/hyperdebug:rom_with_fake_keys_otp_{}".format(lc_state.lower()),
            lc_state = lc_state,  # will be expanded in test_cmd
            tags = ["manuf"],
            test_cmd = (
                "" if (
                    (lc_state, lc_val) in _TEST_LOCKED_LC_ITEMS
                ) else "--bootstrap={firmware}"
            ) + " --initial-lc-state={lc_state}",
            test_harness = "//sw/host/tests/manuf/manuf_scrap",
        ),
        rsa_key = _MANUF_TEST_LOCKED_KEY if (lc_state, lc_val) in _TEST_LOCKED_LC_ITEMS else rsa_key_for_lc_state(RSA_ONLY_KEY_STRUCTS, lc_val),
        deps = [
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing/test_framework:ottf_main",
        ],
    )
    for lc_state, lc_val in _ALL_LC_ITEMS
]

test_suite(
    name = "manuf_scrap_functest",
    tags = ["manual"],
    tests = [
        ":manuf_scrap_functest_{}".format(lc_state.lower())
        for lc_state, _ in _ALL_LC_ITEMS
    ],
)

lc_raw_unlock_token(
    name = "lc_raw_unlock_token",
)

opentitan_test(
    name = "manuf_cp_unlock_raw_functest",
    srcs = ["//sw/device/silicon_creator/rom/e2e:empty_test.c"],
    cw310 = cw310_jtag_params(
        bitstream = "//hw/bitstream:rom_with_fake_keys_otp_raw",
        tags = ["manuf"],
        test_harness = "//sw/host/tests/manuf/manuf_cp_unlock_raw",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        "//hw/top_earlgrey:fpga_hyper310_rom_with_fake_keys": None,
    },
    hyper310 = hyper310_jtag_params(
        bitstream = "//hw/bitstream/hyperdebug:rom_with_fake_keys_otp_raw",
        tags = ["manuf"],
        test_harness = "//sw/host/tests/manuf/manuf_cp_unlock_raw",
    ),
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/silicon_creator/lib/sigverify:spx_verify",
    ],
)

opentitan_test(
    name = "manuf_cp_volatile_unlock_raw_functest",
    srcs = ["//sw/device/silicon_creator/rom/e2e:empty_test.c"],
    cw310 = cw310_jtag_params(
        bitstream = "//hw/bitstream:rom_with_fake_keys_otp_raw",
        tags = ["manuf"],
        test_harness = "//sw/host/tests/manuf/manuf_cp_volatile_unlock_raw",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        "//hw/top_earlgrey:fpga_hyper310_rom_with_fake_keys": None,
    },
    hyper310 = hyper310_jtag_params(
        bitstream = "//hw/bitstream/hyperdebug:rom_with_fake_keys_otp_raw",
        tags = ["manuf"],
        test_harness = "//sw/host/tests/manuf/manuf_cp_volatile_unlock_raw",
    ),
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/silicon_creator/lib/sigverify:spx_verify",
    ],
)

# This is the same as rom_with_fake_keys_otp_test_unlocked* but with ROM execution disabled.
[
    otp_image(
        name = "otp_img_rom_exec_disabled_test_unlocked{}".format(i),
        src = "//hw/ip/otp_ctrl/data:otp_json_test_unlocked{}".format(i),
        overlays = [
            "//hw/ip/otp_ctrl/data:otp_json_fixed_secret0",
            "//hw/ip/otp_ctrl/data:otp_json_exec_disabled",
        ],
        visibility = ["//visibility:private"],
    )
    for i in range(0, 8)
]

# Bitstream with ROM and above OTP image that is in the test_unlocked* LC state
# with ROM execution disabled.
# TODO: Add hyper310 targets too?
[
    bitstream_splice(
        name = "bitstream_rom_exec_disabled_test_unlocked{}".format(i),
        src = "//hw/bitstream:rom_with_fake_keys",
        data = ":otp_img_rom_exec_disabled_test_unlocked{}".format(i),
        meminfo = "//hw/bitstream:otp_mmi",
        update_usr_access = True,
        visibility = ["//visibility:private"],
    )
    for i in range(0, 8)
]

[
    opentitan_test(
        name = "manuf_cp_yield_test_functest_{}".format(lc_state.lower()),
        srcs = ["//sw/device/silicon_creator/rom/e2e:empty_test.c"],
        cw310 = cw310_jtag_params(
            bitstream = ":bitstream_rom_exec_disabled_{}".format(lc_state.lower()),
            lc_state = lc_state,  # will be expanded in test_cmd
            tags = ["manuf"],
            test_cmd = "--initial-lc-state={lc_state}",
            test_harness = "//sw/host/tests/manuf/manuf_cp_yield_test",
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        },
        deps = [
            "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib/drivers:lifecycle",
            "//sw/device/silicon_creator/lib/drivers:otp",
            "//sw/device/silicon_creator/lib/sigverify:spx_verify",
        ],
    )
    for lc_state, _ in _TEST_UNLOCKED_LC_ITEMS
]

test_suite(
    name = "manuf_cp_yield_test_functest",
    tags = ["manual"],
    tests = [
        ":manuf_cp_yield_test_functest_{}".format(lc_state.lower())
        for lc_state, _ in _TEST_UNLOCKED_LC_ITEMS
    ],
)

cc_library(
    name = "test_wafer_auth_secret",
    srcs = ["test_wafer_auth_secret.h"],
    visibility = ["//visibility:private"],
    deps = [
        "//sw/device/silicon_creator/manuf/lib:flash_info_fields",
    ],
)

# We are using a bitstream with ROM execution disabled so the contents of flash
# does not matter but opentitan_functest() is unhappy if we don't provide one.
# Additionally, ROM execution is disabled in the OTP image we use so we do not
# attempt to bootstrap.
[
    opentitan_test(
        name = "manuf_sram_program_crc_{}_functest".format(lc_state.lower()),
        srcs = ["sram_empty_functest.c"],
        cw310 = cw310_jtag_params(
            bitstream = ":bitstream_rom_exec_disabled_{}".format(lc_state.lower()),
            test_cmd = "--elf={firmware}",
            test_harness = "//sw/host/tests/manuf/manuf_sram_program_crc_check",
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
        kind = "ram",
        linker_script = "//sw/device/silicon_creator/manuf/lib:sram_program_linker_script",
        silicon = silicon_jtag_params(
            test_cmd = "--elf={firmware}",
            test_harness = "//sw/host/tests/manuf/manuf_sram_program_crc_check",
        ),
        deps = [
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/arch:device",
            "//sw/device/lib/base:macros",
            "//sw/device/lib/dif:pinmux",
            "//sw/device/lib/dif:uart",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing:pinmux_testutils",
            "//sw/device/lib/testing/test_framework:ottf_test_config",
            "//sw/device/lib/testing/test_framework:status",
            "//sw/device/silicon_creator/manuf/lib:sram_start",
        ],
    )
    for lc_state, _ in _TEST_UNLOCKED_LC_ITEMS
]

test_suite(
    name = "manuf_sram_program_crc_functest",
    tags = ["manual"],
    tests = [
        ":manuf_sram_program_crc_{}_functest".format(lc_state.lower())
        for lc_state, _ in _TEST_UNLOCKED_LC_ITEMS
    ],
)

opentitan_binary(
    name = "sram_device_info_flash_wr_functest",
    testonly = True,
    srcs = ["sram_device_info_flash_wr_functest.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
    },
    kind = "ram",
    linker_script = "//sw/device/silicon_creator/manuf/lib:sram_program_linker_script",
    deps = [
        ":test_wafer_auth_secret",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:lc_ctrl",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_test_config",
        "//sw/device/lib/testing/test_framework:status",
        "//sw/device/silicon_creator/manuf/lib:flash_info_fields",
        "//sw/device/silicon_creator/manuf/lib:individualize_sw_cfg_earlgrey_a0_sku_generic",
        "//sw/device/silicon_creator/manuf/lib:sram_start",
    ],
)

[
    opentitan_test(
        name = "manuf_cp_device_info_flash_wr_{}_to_{}_functest".format(
            init_lc_state.lower(),
            target_lc_state.lower(),
        ),
        srcs = ["flash_device_info_flash_wr_functest.c"],
        cw310 = cw310_jtag_params(
            binaries = {
                ":sram_device_info_flash_wr_functest": "sram_program",
            },
            bitstream = "bitstream_rom_exec_disabled_{}".format(init_lc_state.lower()),
            tags = ["manuf"],
            target_lc_state = target_lc_state,  # will be expanded in test_cmd
            test_cmd = """
                --bootstrap={firmware}
                --target-lc-state={target_lc_state}
                --elf={sram_program}
            """,
            test_harness = "//sw/host/tests/manuf/manuf_cp_device_info_flash_wr",
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        },
        # We select the PROD key since the SRAM test program does an LC transition to DEV.
        rsa_key = rsa_key_for_lc_state(
            RSA_ONLY_KEY_STRUCTS,
            CONST.LCV.PROD,
        ),
        deps = [
            ":test_wafer_auth_secret",
            "//sw/device/lib/dif:flash_ctrl",
            "//sw/device/lib/dif:lc_ctrl",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing:flash_ctrl_testutils",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/manuf/lib:flash_info_fields",
        ],
    )
    for init_lc_state, _ in _TEST_UNLOCKED_LC_ITEMS
    for target_lc_state, _ in _PROD_LC_ITEMS
]

test_suite(
    name = "manuf_cp_device_info_flash_wr_functest",
    tags = ["manual"],
    tests = [
        ":manuf_cp_device_info_flash_wr_{}_to_{}_functest".format(
            init_lc_state.lower(),
            target_lc_state.lower(),
        )
        for init_lc_state, _ in _TEST_UNLOCKED_LC_ITEMS
        for target_lc_state, _ in _PROD_LC_ITEMS
    ],
)

opentitan_binary(
    name = "sram_exec_test",
    testonly = True,
    srcs = ["sram_exec_test.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
    },
    kind = "ram",
    linker_script = "//sw/device/silicon_creator/manuf/lib:sram_program_linker_script",
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_test_config",
        "//sw/device/lib/testing/test_framework:status",
        "//sw/device/silicon_creator/manuf/lib:sram_start",
    ],
)

# We are using a bitstream with disabled execution so the content of the flash
# does not matter but opentitan_functest() is unhappy if we don't provide one.
# Additionally, ROM execution is disabled in the OTP image we use so we do not
# attempt to bootstrap.
[
    opentitan_test(
        name = "manuf_cp_ast_test_execution_{}_functest".format(lc_state.lower()),
        srcs = ["idle_functest.c"],
        cw310 = cw310_jtag_params(
            binaries = {
                ":sram_exec_test": "sram_program",
            },
            bitstream = ":bitstream_rom_exec_disabled_{}".format(lc_state.lower()),
            tags = ["manuf"],
            test_cmd = """
                --elf={sram_program}
            """,
            test_harness = "//sw/host/tests/manuf/manuf_cp_ast_test_execution",
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        },
        deps = [
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing:otp_ctrl_testutils",
            "//sw/device/lib/testing/test_framework:check",
            "//sw/device/lib/testing/test_framework:ottf_main",
        ],
    )
    for lc_state, _ in _TEST_UNLOCKED_LC_ITEMS
]

test_suite(
    name = "manuf_cp_ast_test_execution_functest",
    tags = ["manual"],
    tests = [
        ":manuf_cp_ast_test_execution_{}_functest".format(lc_state.lower())
        for lc_state, _ in _TEST_UNLOCKED_LC_ITEMS
    ],
)

opentitan_test(
    name = "manuf_cp_test_lock_functest",
    srcs = ["//sw/device/silicon_creator/rom/e2e:empty_test.c"],
    cw310 = cw310_jtag_params(
        bitstream = ":bitstream_otp_ctrl_functest",
        tags = ["manuf"],
        test_harness = "//sw/host/tests/manuf/manuf_cp_test_lock",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
    },
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/silicon_creator/lib/sigverify:spx_verify",
    ],
)

otp_image(
    name = "otp_img_otp_ctrl_functest",
    src = "//hw/ip/otp_ctrl/data:otp_json_test_unlocked0",
    visibility = ["//visibility:private"],
)

# TODO: Add hyper310 targets too?
bitstream_splice(
    name = "bitstream_otp_ctrl_functest",
    src = "//hw/bitstream:rom_with_fake_keys",
    data = ":otp_img_otp_ctrl_functest",
    meminfo = "//hw/bitstream:otp_mmi",
    update_usr_access = True,
    visibility = ["//visibility:private"],
)

opentitan_test(
    name = "otp_ctrl_functest",
    srcs = [":empty_functest.c"],
    cw310 = cw310_jtag_params(
        bitstream = ":bitstream_otp_ctrl_functest",
        tags = ["manuf"],
        test_harness = "//sw/host/tests/manuf/otp_ctrl:otp_ctrl",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
    },
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/silicon_creator/lib/sigverify:spx_verify",
    ],
)
