# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "cw310_jtag_params",
    "opentitan_test",
)
load(
    "//rules:opentitan_test.bzl",
    "OPENTITANTOOL_OPENOCD_DATA_DEPS",
    "OPENTITANTOOL_OPENOCD_TEST_CMDS",
    "cw310_params",
    "opentitan_functest",
)
load(
    "//rules:const.bzl",
    "CONST",
    "get_lc_items",
)
load(
    "//rules:otp.bzl",
    "STD_OTP_OVERLAYS",
    "otp_image",
    "otp_json",
)
load(
    "//rules:splice.bzl",
    "bitstream_splice",
)

package(default_visibility = ["//visibility:public"])

# Apply an overlay that disables ROM execution on top of the base OTP configs.
[
    otp_image(
        name = "img_{}_exec_disabled".format(lc_state),
        src = "//hw/ip/otp_ctrl/data:otp_json_" + lc_state,
        overlays = STD_OTP_OVERLAYS + ["//hw/ip/otp_ctrl/data:otp_json_exec_disabled"],
        visibility = ["//visibility:private"],
    )
    for lc_state, _ in get_lc_items()
]

# Splice each execution-disabled OTP image into the ROM bitstream.
[
    bitstream_splice(
        name = "rom_with_fake_keys_otp_{}_exec_disabled".format(lc_state),
        src = "//hw/bitstream/hyperdebug:rom_with_fake_keys",
        data = "img_{}_exec_disabled".format(lc_state),
        meminfo = "//hw/bitstream/hyperdebug:otp_mmi",
        tags = [
            "manual",
        ],
        update_usr_access = True,
        visibility = ["//visibility:private"],
    )
    for lc_state, _ in get_lc_items()
]

[
    # We are using a bitstream with disabled execution so the content of the flash
    # does not matter but opentitan_test() is unhappy if we don't provide one.
    # Since execution in the ROM is disabled, bootstrap is not possible so we need
    # to make sure that the test does not try to bootstrap
    opentitan_test(
        name = "sram_program_fpga_cw310_test_otp_{}".format(lc_state),
        srcs = ["//sw/device/silicon_creator/rom/e2e:empty_test"],
        cw310 = cw310_jtag_params(
            binaries = {
                "//sw/device/examples/sram_program:sram_program": "sram_program",
            },
            bitstream = ":rom_with_fake_keys_otp_{}_exec_disabled".format(lc_state),
            logging = "debug",
            tags = ["cw310_rom_with_fake_keys"],
            test_cmd = """
                --elf={sram_program}
            """,
            test_harness = "//sw/host/tests/chip/jtag:sram_load",
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        },
        deps = [
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib/drivers:otp",
            "//sw/device/silicon_creator/lib/sigverify:spx_verify",
        ],
    )
    for lc_state, _ in get_lc_items(
        CONST.LCV.TEST_UNLOCKED0,
        CONST.LCV.DEV,
        CONST.LCV.RMA,
    )
]

test_suite(
    name = "rom_e2e_jtag_inject_tests",
    tags = ["manual"],
    tests = [
        "sram_program_fpga_cw310_test_otp_" + lc_state
        for lc_state, _ in get_lc_items(
            CONST.LCV.TEST_UNLOCKED0,
            CONST.LCV.DEV,
            CONST.LCV.RMA,
        )
    ],
)

LC_STATES_DEBUG_DISALLOWED = [
    CONST.LCV.PROD,
    CONST.LCV.PROD_END,
]

[
    opentitan_test(
        name = "openocd_debug_test_otp_" + lc_state,
        srcs = ["//sw/device/silicon_creator/rom/e2e:empty_test"],
        cw310 = cw310_jtag_params(
            timeout = "moderate",
            binaries = {
                "//sw/device/silicon_creator/rom:rom_with_fake_keys_fpga_cw310_elf": "rom",
            },
            bitstream = ":rom_with_fake_keys_otp_{}_exec_disabled".format(lc_state),
            logging = "debug",
            tags = ["cw310_rom_with_fake_keys"],
            test_cmd = " --elf={rom}" + (" --expect-fail" if lc_state_val in LC_STATES_DEBUG_DISALLOWED else " "),
            test_harness = "//sw/host/tests/rom/e2e_openocd_debug_test",
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        },
        deps = [
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib/drivers:otp",
            "//sw/device/silicon_creator/lib/sigverify:spx_verify",
        ],
    )
    for lc_state, lc_state_val in get_lc_items(
        CONST.LCV.TEST_UNLOCKED0,
        CONST.LCV.DEV,
        CONST.LCV.RMA,
        CONST.LCV.PROD,
        CONST.LCV.PROD_END,
    )
]

test_suite(
    name = "rom_e2e_openocd_debug_test",
    tags = ["manual"],
    tests = [
        "openocd_debug_test_otp_" + lc_state
        for lc_state, _ in get_lc_items(
            CONST.LCV.TEST_UNLOCKED0,
            CONST.LCV.DEV,
            CONST.LCV.RMA,
            CONST.LCV.PROD,
            CONST.LCV.PROD_END,
        )
    ],
)
