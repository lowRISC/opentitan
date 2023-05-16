# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:opentitan_test.bzl",
    "OPENTITANTOOL_OPENOCD_DATA_DEPS",
    "OPENTITANTOOL_OPENOCD_TEST_CMDS",
    "cw310_params",
    "opentitan_functest",
)
load(
    "//rules:opentitan.bzl",
    "RSA_ONLY_KEY_STRUCTS",
    "filter_key_structs_for_lc_state",
    "opentitan_ram_binary",
)
load("//rules:const.bzl", "CONST", "get_lc_items")
load("//rules:lc.bzl", "lc_raw_unlock_token")
load("//rules:otp.bzl", "otp_image", "otp_json", "otp_partition")
load("//rules:splice.bzl", "bitstream_splice")

package(default_visibility = ["//visibility:public"])

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

_MANUF_LC_TRANSITION_TEST_CMDS = [
    "--rom-kind=rom",
    "--bitstream=\"$(rootpath {bitstream})\"",
    "--openocd=\"$(rootpath //third_party/openocd:openocd_bin)\"",
    "--openocd-adapter-config=\"$(rootpath //third_party/openocd:jtag_adapter_cfg)\"",
    "--openocd-riscv-target-config=\"$(rootpath //util/openocd/target:lowrisc-earlgrey.cfg)\"",
    "--openocd-lc-target-config=\"$(rootpath //util/openocd/target:lowrisc-earlgrey-lc.cfg)\"",
]

_MANUF_LC_TRANSITION_TEST_CMDS_WBOOTSTRAP = _MANUF_LC_TRANSITION_TEST_CMDS + [
    "--bootstrap=\"$(rootpath {flash})\"",
]

cc_library(
    name = "otp_img_types",
    hdrs = ["otp_img_types.h"],
)

cc_library(
    name = "otp_img",
    srcs = ["otp_img.c"],
    hdrs = ["otp_img.h"],
    deps = [
        ":otp_img_types",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/testing:otp_ctrl_testutils",
    ],
)

cc_library(
    name = "individualize",
    srcs = ["individualize.c"],
    hdrs = [
        "individualize.h",
    ],
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:lc_ctrl",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:lc_ctrl_testutils",
        "//sw/device/lib/testing:otp_ctrl_testutils",
    ],
)

opentitan_functest(
    name = "individualize_functest",
    srcs = ["individualize_functest.c"],
    cw310 = cw310_params(
        bitstream = "//hw/bitstream:rom_with_fake_keys_otp_dev_initial",
        tags = ["manuf"],
    ),
    key_struct = RSA_ONLY_KEY_STRUCTS[1],
    targets = [
        "cw310_rom_with_fake_keys",
    ],
    deps = [
        ":individualize",
        "//hw/ip/flash_ctrl/data:flash_ctrl_regs",
        "//hw/ip/lc_ctrl/data:lc_ctrl_regs",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:lc_ctrl",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

cc_library(
    name = "individualize_preop",
    srcs = ["individualize_preop.c"],
    hdrs = [
        "individualize_preop.h",
    ],
    deps = [
        ":otp_img",
        "//hw/ip/otp_ctrl/data/sku_earlgrey_a0:otp_img_sku_earlgrey_a0_stage_individualize",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/testing:lc_ctrl_testutils",
        "//sw/device/lib/testing:otp_ctrl_testutils",
    ],
)

opentitan_functest(
    name = "individualize_preop_functest",
    srcs = ["individualize_preop_functest.c"],
    cw310 = cw310_params(
        bitstream = "//hw/bitstream:rom_with_fake_keys_otp_test_unlocked0",
        tags = ["manuf"],
    ),
    targets = [
        "cw310_rom_with_fake_keys",
    ],
    deps = [
        ":individualize_preop",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

cc_library(
    name = "provisioning",
    srcs = ["provisioning.c"],
    hdrs = [
        "provisioning.h",
    ],
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/crypto/impl:aes",
        "//sw/device/lib/crypto/impl:ecc",
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:lc_ctrl",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:lc_ctrl_testutils",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing/json:provisioning_data",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/silicon_creator/manuf/keys",
    ],
)

opentitan_functest(
    name = "provisioning_functest",
    srcs = ["provisioning_functest.c"],
    cw310 = cw310_params(
        bitstream = "//hw/bitstream:rom_with_fake_keys_otp_dev_individualized",
        tags = ["manuf"],
        test_cmds = [
            "--clear-bitstream",
            "--rom-kind=rom",
            "--bitstream=\"$(location {bitstream})\"",
            "--bootstrap=\"$(location {flash})\"",
            "--hsm-ecdh-sk=\"$(rootpath //sw/device/silicon_creator/manuf/keys/fake:rma_unlock_token_export_key.sk_hsm.der)\"",
        ] + OPENTITANTOOL_OPENOCD_TEST_CMDS,
    ),
    data = [
        "//sw/device/silicon_creator/manuf/keys/fake:rma_unlock_token_export_key.sk_hsm.der",
    ] + OPENTITANTOOL_OPENOCD_DATA_DEPS,
    key_struct = RSA_ONLY_KEY_STRUCTS[1],
    targets = [
        "cw310_rom_with_fake_keys",
    ],
    test_harness = "//sw/host/tests/manuf/provisioning",
    deps = [
        ":provisioning",
        "//hw/ip/flash_ctrl/data:flash_ctrl_regs",
        "//hw/ip/lc_ctrl/data:lc_ctrl_regs",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:lc_ctrl",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/json:command",
        "//sw/device/lib/testing/json:provisioning_data",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/manuf/keys/fake",
    ],
)

lc_raw_unlock_token(
    name = "lc_raw_unlock_token",
)

# We bootstrap code into flash in LC states where CPU execution is enabled. In
# other LC states, we do not perform bootstrap, as it will not succeed.
[
    opentitan_functest(
        name = "manuf_scrap_functest_{}".format(lc_state.lower()),
        srcs = ["empty_functest.c"],
        cw310 = cw310_params(
            bitstream = "//hw/bitstream:rom_with_fake_keys_otp_{}".format(lc_state.lower()),
            tags = ["manuf"],
            test_cmds = (
                _MANUF_LC_TRANSITION_TEST_CMDS if (
                    (lc_state, lc_val) in _TEST_LOCKED_LC_ITEMS
                ) else _MANUF_LC_TRANSITION_TEST_CMDS_WBOOTSTRAP
            ) + [
                "--initial-lc-state=\"{}\"".format(lc_state),
            ],
        ),
        data = OPENTITANTOOL_OPENOCD_DATA_DEPS,
        key_struct = RSA_ONLY_KEY_STRUCTS[0] if (lc_state, lc_val) in _TEST_LOCKED_LC_ITEMS else filter_key_structs_for_lc_state(RSA_ONLY_KEY_STRUCTS, lc_val)[0],
        targets = ["cw310_rom_with_fake_keys"],
        test_harness = "//sw/host/tests/manuf/manuf_scrap",
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

opentitan_functest(
    name = "manuf_cp_unlock_raw_functest",
    srcs = ["//sw/device/silicon_creator/rom/e2e:empty_test.c"],
    cw310 = cw310_params(
        bitstream = "//hw/bitstream:rom_with_fake_keys_otp_raw",
        tags = ["manuf"],
        test_cmds = _MANUF_LC_TRANSITION_TEST_CMDS,
    ),
    data = OPENTITANTOOL_OPENOCD_DATA_DEPS,
    targets = ["cw310_rom_with_fake_keys"],
    test_harness = "//sw/host/tests/manuf/manuf_cp_unlock_raw",
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/silicon_creator/lib/sigverify:spx_verify",
    ],
)

otp_json(
    name = "otp_json_fixed_secret0",
    partitions = [
        otp_partition(
            name = "SECRET0",
            items = {
                # These match their cSHAKE-128 (w/ "LC_CTRL" customization string)
                # preimage counterpart of: 0x1111_1111_1111_1111_1111_1111_1111_1111,
                # which is hardcoded into the test that use this overlay.
                # The script that generated this token is:
                # //sw/host/tests/manuf/manuf_cp_device_info_flash_wr:gen_test_exit_token
                "TEST_UNLOCK_TOKEN": "0xde0a1f1e0d6a649fd35fadb75ec82674",
                "TEST_EXIT_TOKEN": "0xde0a1f1e0d6a649fd35fadb75ec82674",
            },
            lock = True,
        ),
    ],
    visibility = ["//visibility:private"],
)

# This is the same as rom_with_fake_keys_otp_test_unlocked* but with ROM execution disabled.
[
    otp_image(
        name = "otp_img_rom_exec_disabled_test_unlocked{}".format(i),
        src = "//hw/ip/otp_ctrl/data:otp_json_test_unlocked{}".format(i),
        overlays = [
            ":otp_json_fixed_secret0",
            "//hw/ip/otp_ctrl/data:otp_json_exec_disabled",
        ],
        visibility = ["//visibility:private"],
    )
    for i in range(0, 8)
]

# Bitstream with ROM and above OTP image that is in the test_unlocked* LC state
# with ROM execution disabled.
[
    bitstream_splice(
        name = "bitstream_rom_exec_disabled_test_unlocked{}".format(i),
        src = "//hw/bitstream:rom_with_fake_keys",
        data = "otp_img_rom_exec_disabled_test_unlocked{}".format(i),
        meminfo = "//hw/bitstream:otp_mmi",
        update_usr_access = True,
        visibility = ["//visibility:private"],
    )
    for i in range(0, 8)
]

[
    opentitan_functest(
        name = "manuf_cp_yield_test_functest_{}".format(lc_state.lower()),
        srcs = ["//sw/device/silicon_creator/rom/e2e:empty_test.c"],
        cw310 = cw310_params(
            bitstream = ":bitstream_rom_exec_disabled_{}".format(lc_state.lower()),
            tags = ["manuf"],
            test_cmds = _MANUF_LC_TRANSITION_TEST_CMDS + [
                "--initial-lc-state=\"{}\"".format(lc_state),
            ],
        ),
        data = OPENTITANTOOL_OPENOCD_DATA_DEPS,
        targets = ["cw310_rom_with_fake_keys"],
        test_harness = "//sw/host/tests/manuf/manuf_cp_yield_test",
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
    name = "isolated_flash_partition",
    srcs = ["isolated_flash_partition.c"],
    hdrs = ["isolated_flash_partition.h"],
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/testing:flash_ctrl_testutils",
    ],
)

cc_library(
    name = "test_wafer_auth_secret",
    srcs = ["test_wafer_auth_secret.h"],
    visibility = ["//visibility:private"],
    deps = [
        ":isolated_flash_partition",
    ],
)

opentitan_ram_binary(
    name = "sram_device_info_flash_wr_functest",
    srcs = ["sram_device_info_flash_wr_functest.c"],
    hdrs = ["sram_device_info_flash_wr_functest.h"],
    archive_symbol_prefix = "sram_device_info_flash_wr_functest",
    deps = [
        ":individualize_preop",
        ":isolated_flash_partition",
        ":test_wafer_auth_secret",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/examples/sram_program:sram_program_linker_script",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:lc_ctrl",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:status",
    ],
)

[
    opentitan_functest(
        name = "manuf_cp_device_info_flash_wr_{}_to_{}_functest".format(
            init_lc_state.lower(),
            target_lc_state.lower(),
        ),
        srcs = ["flash_device_info_flash_wr_functest.c"],
        cw310 = cw310_params(
            bitstream = "bitstream_rom_exec_disabled_{}".format(init_lc_state.lower()),
            tags = ["manuf"],
            test_cmds = [
                "--clear-bitstream",
                "--rom-kind=rom",
                "--bitstream=\"$(rootpath {bitstream})\"",
                "--bootstrap=\"$(location {flash})\"",
                "--target-lc-state=\"{}\"".format(target_lc_state),
                "--vmem=\"$(rootpath :sram_device_info_flash_wr_functest_fpga_cw310_vmem)\"",
                # the following values come from the sram linker script
                "--load-addr=0x10001fc4",
                "--stack-pointer=0x10020000",
                "--stack-size=1024",
                "--global-pointer=0x100027C4",  # sram_load_addr + 2048;
            ] + OPENTITANTOOL_OPENOCD_TEST_CMDS,
        ),
        data = [
            ":sram_device_info_flash_wr_functest_fpga_cw310_vmem",
        ] + OPENTITANTOOL_OPENOCD_DATA_DEPS,
        # We select the PROD key since the SRAM test program does an LC transition to DEV.
        key_struct = filter_key_structs_for_lc_state(
            RSA_ONLY_KEY_STRUCTS,
            CONST.LCV.PROD,
        )[0],
        targets = ["cw310_rom_with_fake_keys"],
        test_harness = "//sw/host/tests/manuf/manuf_cp_device_info_flash_wr",
        deps = [
            ":isolated_flash_partition",
            ":test_wafer_auth_secret",
            "//sw/device/lib/dif:flash_ctrl",
            "//sw/device/lib/dif:lc_ctrl",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing/test_framework:ottf_main",
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

opentitan_ram_binary(
    name = "sram_exec_test",
    srcs = ["sram_exec_test.c"],
    hdrs = ["sram_exec_test.h"],
    archive_symbol_prefix = "sram_exec_test",
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/examples/sram_program:sram_program_linker_script",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:status",
    ],
)

# We are using a bitstream with disabled execution so the content of the flash
# does not matter but opentitan_functest() is unhappy if we don't provide one.
# Additionally, ROM execution is disabled in the OTP image we use so we do not
# attempt to bootstrap.
[
    opentitan_functest(
        name = "manuf_cp_ast_test_execution_{}_functest".format(lc_state.lower()),
        srcs = ["idle_functest.c"],
        cw310 = cw310_params(
            bitstream = ":bitstream_rom_exec_disabled_test_unlocked0",
            tags = ["manuf"],
            test_cmds = [
                "--clear-bitstream",
                "--rom-kind=rom",
                "--bitstream=\"$(rootpath {bitstream})\"",
                "--vmem=\"$(rootpath :sram_exec_test_fpga_cw310_vmem)\"",
                # the following values come from the sram linker script
                "--load-addr=0x10001fc4",
                "--stack-pointer=0x10020000",
                "--stack-size=1024",
                "--global-pointer=0x100027C4",  # sram_load_addr + 2048;
            ] + OPENTITANTOOL_OPENOCD_TEST_CMDS,
        ),
        data = [
            ":sram_exec_test_fpga_cw310_vmem",
        ] + OPENTITANTOOL_OPENOCD_DATA_DEPS,
        targets = ["cw310_rom_with_fake_keys"],
        test_harness = "//sw/host/tests/manuf/manuf_cp_ast_test_execution",
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

otp_image(
    name = "otp_img_otp_ctrl_functest",
    src = "//hw/ip/otp_ctrl/data:otp_json_test_unlocked0",
    visibility = ["//visibility:private"],
)

bitstream_splice(
    name = "bitstream_otp_ctrl_functest",
    src = "//hw/bitstream:rom_with_fake_keys",
    data = "otp_img_otp_ctrl_functest",
    meminfo = "//hw/bitstream:otp_mmi",
    update_usr_access = True,
    visibility = ["//visibility:private"],
)

opentitan_functest(
    name = "otp_ctrl_functest",
    srcs = ["//sw/device/silicon_creator/manuf/lib:empty_functest.c"],
    cw310 = cw310_params(
        bitstream = ":bitstream_otp_ctrl_functest",
        tags = ["manuf"],
        test_cmds = _MANUF_LC_TRANSITION_TEST_CMDS,
    ),
    data = OPENTITANTOOL_OPENOCD_DATA_DEPS,
    targets = ["cw310_rom_with_fake_keys"],
    test_harness = "//sw/host/tests/manuf/otp_ctrl:otp_ctrl",
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/silicon_creator/lib/sigverify:spx_verify",
    ],
)

opentitan_functest(
    name = "manuf_cp_test_lock_functest",
    srcs = ["//sw/device/silicon_creator/rom/e2e:empty_test.c"],
    cw310 = cw310_params(
        bitstream = ":bitstream_otp_ctrl_functest",
        tags = ["manuf"],
        test_cmds = _MANUF_LC_TRANSITION_TEST_CMDS,
    ),
    data = OPENTITANTOOL_OPENOCD_DATA_DEPS,
    targets = ["cw310_rom_with_fake_keys"],
    test_harness = "//sw/host/tests/manuf/manuf_cp_test_lock",
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/silicon_creator/lib/sigverify:spx_verify",
    ],
)
