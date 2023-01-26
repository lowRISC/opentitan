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
load("//rules:const.bzl", "CONST", "error_redact", "get_lc_items", "hex", "hex_digits", "lcv_hw_to_sw")
load(
    "//rules:opentitan.bzl",
    "bin_to_vmem",
    "opentitan_flash_binary",
    "opentitan_multislot_flash_binary",
    "scramble_flash_vmem",
)
load("//rules:manifest.bzl", "manifest")
load("//rules:opentitan_gdb_test.bzl", "IBEX_GPRS", "gdb_commands_copy_registers", "gdb_commands_restore_registers", "gdb_commands_set_registers", "get_gdb_readable_csr_names", "get_gdb_settable_csr_names", "opentitan_gdb_fpga_cw310_test")
load("//rules:otp.bzl", "STD_OTP_OVERLAYS", "otp_alert_digest", "otp_image", "otp_json", "otp_partition")
load("//rules:rom_e2e.bzl", "maybe_skip_in_ci")
load("//rules:splice.bzl", "bitstream_splice")
load("@bazel_skylib//lib:shell.bzl", "shell")
load("@bazel_skylib//lib:structs.bzl", "structs")

package(default_visibility = ["//visibility:public"])

MSG_TEMPLATE_BFV = "{}{}\r\n(?s:.*){}{}\r\n".format(
    CONST.SHUTDOWN.PREFIX.BFV,
    "{0}",
    CONST.SHUTDOWN.PREFIX.BFV,
    "{0}",
)

MSG_TEMPLATE_BFV_LCV = "{}{}\r\n{}{}\r\n(?s:.*){}{}\r\n{}{}\r\n".format(
    CONST.SHUTDOWN.PREFIX.BFV,
    "{0}",
    CONST.SHUTDOWN.PREFIX.LCV,
    "{1}",
    CONST.SHUTDOWN.PREFIX.BFV,
    "{0}",
    CONST.SHUTDOWN.PREFIX.LCV,
    "{1}",
)

MSG_STARTING_ROM_EXT = "Starting ROM_EXT"

MSG_PASS = "PASS!"

SLOTS = {
    "a": "0x0",
    "b": "0x80000",
}

LC_KEY_TYPES = {
    CONST.LCV.TEST_UNLOCKED0: [
        "fake_test_key_0",
        "fake_prod_key_0",
    ],
    CONST.LCV.DEV: [
        "fake_dev_key_0",
        "fake_prod_key_0",
    ],
    CONST.LCV.PROD: ["fake_prod_key_0"],
    CONST.LCV.PROD_END: ["fake_prod_key_0"],
    CONST.LCV.RMA: [
        "fake_test_key_0",
        "fake_prod_key_0",
    ],
}

# Default OTP in TEST_UNLOCKED state
otp_json(
    name = "otp_json_default",
    partitions = [
        otp_partition(
            name = "OWNER_SW_CFG",
            items = {
                "OWNER_SW_CFG_ROM_BOOTSTRAP_EN": "0x739",
            },
        ),
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {
                "CREATOR_SW_CFG_ROM_EXEC_EN": "0xffffffff",
                # Enable use of entropy for countermeasures. See the definition
                # of `hardened_bool_t` in sw/device/lib/base/hardened.h.
                "CREATOR_SW_CFG_RNG_EN": "0x739",
                # Entropy source health check default values. This needs to be
                # populated when `CREATOR_SW_CFG_RNG_EN` is set to true.
                "CREATOR_SW_CFG_RNG_REPCNT_THRESHOLDS": "0xffffffff",
                "CREATOR_SW_CFG_RNG_REPCNTS_THRESHOLDS": "0xffffffff",
                "CREATOR_SW_CFG_RNG_ADAPTP_HI_THRESHOLDS": "0xffffffff",
                "CREATOR_SW_CFG_RNG_ADAPTP_LO_THRESHOLDS": "0x0",
                "CREATOR_SW_CFG_RNG_BUCKET_THRESHOLDS": "0xffffffff",
                "CREATOR_SW_CFG_RNG_MARKOV_HI_THRESHOLDS": "0xffffffff",
                "CREATOR_SW_CFG_RNG_MARKOV_LO_THRESHOLDS": "0x0",
                "CREATOR_SW_CFG_RNG_EXTHT_HI_THRESHOLDS": "0xffffffff",
                "CREATOR_SW_CFG_RNG_EXTHT_LO_THRESHOLDS": "0x0",
                "CREATOR_SW_CFG_RNG_ALERT_THRESHOLD": "0xfffd0002",
                "CREATOR_SW_CFG_RNG_HEALTH_CONFIG_DIGEST": "0x8264cf75",
            },
        ),
        otp_partition(
            name = "LIFE_CYCLE",
            count = 1,
            state = "TEST_UNLOCKED0",
        ),
    ],
)

otp_image(
    name = "otp_img_default",
    src = ":otp_json_default",
    visibility = ["//visibility:private"],
)

bitstream_splice(
    name = "bitstream_default_otp",
    src = "//hw/bitstream:rom",
    data = ":otp_img_default",
    meminfo = "//hw/bitstream:otp_mmi",
    tags = ["vivado"] + maybe_skip_in_ci(CONST.LCV.RMA),
    update_usr_access = True,
    visibility = ["//visibility:private"],
)

opentitan_functest(
    name = "rom_e2e_default_otp_bootup",
    srcs = ["empty_test.c"],
    cw310 = cw310_params(
        bitstream = ":bitstream_default_otp",
        tags = ["vivado"] + maybe_skip_in_ci(CONST.LCV.RMA),
    ),
    signed = True,
    targets = [
        "cw310_rom",
    ],
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:otp",
    ],
)

[opentitan_flash_binary(
    name = "empty_test_slot_{}".format(slot),
    srcs = ["empty_test.c"],
    devices = [
        "fpga_cw310",
        "sim_dv",
        "sim_verilator",
    ],
    signed = True,
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_{}".format(slot),
    ],
) for slot in SLOTS]

opentitan_functest(
    name = "rom_e2e_flash_ctrl_init",
    srcs = ["rom_e2e_flash_ctrl_init_test.c"],
    signed = True,
    targets = [
        "cw310_rom",
    ],
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:otp",
    ],
)

opentitan_functest(
    name = "rom_e2e_shutdown_exception_c",
    srcs = ["rom_e2e_shutdown_exception_c_test.c"],
    cw310 = cw310_params(
        # Note: This test never prints a failure message so it will fail only
        # when it times out.
        exit_failure = "NO_FAILURE_MESSAGE",
        exit_success = MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.INTERRUPT.INSTRUCTION_ACCESS)),
    ),
    dv = dv_params(
        rom = "//sw/device/silicon_creator/rom:rom_with_fake_keys",
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
        exit_success = MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.INTERRUPT.INSTRUCTION_ACCESS)),
        rom = "//sw/device/silicon_creator/rom:rom_with_fake_keys",
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
        rom = "//sw/device/silicon_creator/rom:rom_with_fake_keys",
    ),
    key = "fake_test_key_0",
    ot_flash_binary = ":empty_test_slot_a",
    targets = [
        "cw310_rom",
        "verilator",
        "dv",
    ],
    verilator = verilator_params(
        timeout = "eternal",
        rom = "//sw/device/silicon_creator/rom:rom_with_fake_keys",
    ),
)

opentitan_functest(
    name = "rom_e2e_static_critical",
    srcs = ["rom_e2e_static_critical_test.c"],
    dv = dv_params(
        rom = "//sw/device/silicon_creator/rom:rom_with_fake_keys",
    ),
    signed = True,
    targets = [
        "dv",
        "cw310_rom",
        "verilator",
    ],
    verilator = verilator_params(
        timeout = "eternal",
        rom = "//sw/device/silicon_creator/rom:rom_with_fake_keys",
    ),
    deps = [
        "//sw/device/lib/dif:hmac",
        "//sw/device/lib/testing:hmac_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
    ],
)

opentitan_flash_binary(
    name = "rom_e2e_keymgr_init_test",
    srcs = [":rom_e2e_keymgr_init_test.c"],
    deps = [
        "//sw/device/lib/dif:keymgr",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:otp",
    ],
)

rom_e2e_keymgr_init_configs = [
    {
        "name": "rom_ext_meas",
        "value": CONST.TRUE,
    },
    {
        "name": "rom_ext_no_meas",
        "value": CONST.FALSE,
    },
    {
        "name": "rom_ext_invalid_meas",
        "value": 0,
    },
]

[
    otp_json(
        name = "otp_json_keymgr_{}".format(config["name"]),
        partitions = [
            otp_partition(
                name = "OWNER_SW_CFG",
                items = {
                    "OWNER_SW_CFG_ROM_KEYMGR_ROM_EXT_MEAS_EN": "0x{}".format(hex_digits(config["value"])),
                },
            ),
        ],
    )
    for config in rom_e2e_keymgr_init_configs
]

[
    otp_image(
        name = "otp_img_keymgr_{}".format(config["name"]),
        src = "//hw/ip/otp_ctrl/data:otp_json_rma",
        overlays = STD_OTP_OVERLAYS + [":otp_json_keymgr_{}".format(config["name"])],
        visibility = ["//visibility:private"],
    )
    for config in rom_e2e_keymgr_init_configs
]

[
    bitstream_splice(
        name = "bitstream_keymgr_{}".format(config["name"]),
        src = "//hw/bitstream:rom",
        data = ":otp_img_keymgr_{}".format(config["name"]),
        meminfo = "//hw/bitstream:otp_mmi",
        tags = ["vivado"],
        visibility = ["//visibility:private"],
    )
    for config in rom_e2e_keymgr_init_configs
]

[
    opentitan_functest(
        name = "rom_e2e_keymgr_init_{}".format(config["name"]),
        cw310 = cw310_params(
            bitstream = ":bitstream_keymgr_{}".format(config["name"]),
            tags = ["vivado"],
        ),
        dv = dv_params(
            otp = ":otp_img_keymgr_{}".format(config["name"]),
            rom = "//sw/device/silicon_creator/rom:rom_with_fake_keys",
        ),
        ot_flash_binary = ":rom_e2e_keymgr_init_test",
        targets = [
            "cw310_rom",
            "dv",
            "verilator",
        ],
        verilator = verilator_params(
            timeout = "eternal",
            otp = ":otp_img_keymgr_{}".format(config["name"]),
            rom = "//sw/device/silicon_creator/rom:rom_with_fake_keys",
        ),
    )
    for config in rom_e2e_keymgr_init_configs
]

test_suite(
    name = "keymgr_init",
    tags = ["manual"],
    tests = ["rom_e2e_keymgr_init_{}".format(
        config["name"],
    ) for config in rom_e2e_keymgr_init_configs],
)

opentitan_functest(
    name = "rom_e2e_c_init",
    srcs = ["rom_e2e_c_init_test.c"],
    cw310 = cw310_params(
        exit_failure = CONST.SHUTDOWN.PREFIX.BFV,
        exit_success = MSG_PASS,
    ),
    signed = True,
    targets = [
        "cw310_rom",
    ],
    deps = [
        "//hw/ip/uart/data:uart_regs",
        "//hw/top_earlgrey/ip/pinmux/data/autogen:pinmux_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/silicon_creator/lib:manifest_def",
        "//sw/device/silicon_creator/lib/base:static_critical_boot_measurements",
        "//sw/device/silicon_creator/lib/base:static_critical_epmp_state",
        "//sw/device/silicon_creator/lib/base:static_critical_sec_mmio",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/silicon_creator/lib/drivers:pinmux",
        "//sw/device/silicon_creator/lib/drivers:uart",
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
    key = "fake_test_key_0",
    ot_flash_binary = ":empty_test_slot_a",
    targets = ["cw310_rom"],
)

[otp_image(
    name = "otp_img_e2e_bootstrap_entry_{}".format(lc_state.lower()),
    src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state.lower()),
    overlays = STD_OTP_OVERLAYS,
) for lc_state in structs.to_dict(CONST.LCV)]

# Splice OTP images into bitstreams
[
    bitstream_splice(
        name = "bitstream_e2e_bootstrap_entry_{}".format(lc_state.lower()),
        src = "//hw/bitstream:rom",
        data = ":otp_img_e2e_bootstrap_entry_{}".format(lc_state.lower()),
        meminfo = "//hw/bitstream:otp_mmi",
        tags = ["vivado"] + maybe_skip_in_ci(lc_state_val),
        update_usr_access = True,
    )
    for lc_state, lc_state_val in structs.to_dict(CONST.LCV).items()
]

[
    opentitan_functest(
        name = "e2e_bootstrap_entry_{}".format(lc_state.lower()),
        cw310 = cw310_params(
            bitstream = ":bitstream_e2e_bootstrap_entry_{}".format(lc_state.lower()),
            tags = ["vivado"] + maybe_skip_in_ci(lc_state_val),
            test_cmds = [
                "--rom-kind=rom",
                "--bitstream=\"$(location {bitstream})\"",
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
        deps = [":bitstream_e2e_bootstrap_entry_{}".format(lc_state.lower())],
    )
    for lc_state, lc_state_val in structs.to_dict(CONST.LCV).items()
]

test_suite(
    name = "rom_e2e_bootstrap_entry",
    tags = ["manual"],
    tests = [":e2e_bootstrap_entry_{}".format(lc_state.lower()) for lc_state in structs.to_dict(CONST.LCV)],
)

otp_json(
    name = "otp_json_bootstrap_rma",
    partitions = [
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {
                "CREATOR_SW_CFG_RMA_SPIN_EN": "0x739",  # HARDENED_BOOL_TRUE
                "CREATOR_SW_CFG_RMA_SPIN_CYCLES": "10",
            },
        ),
    ],
    visibility = ["//visibility:private"],
)

# This OTP image is tightly coupled with the "rom_bootstrap_rma" testpoint.
# Despite its name ending with "rma", it actually puts the device into the PROD
# lifecycle state in order to test the transition from PROD to RMA.
otp_image(
    name = "otp_img_bootstrap_rma",
    src = "//hw/ip/otp_ctrl/data:otp_json_prod",
    overlays = STD_OTP_OVERLAYS + [
        ":otp_json_bootstrap_rma",
    ],
    visibility = ["//visibility:private"],
)

bitstream_splice(
    name = "bitstream_bootstrap_rma",
    src = "//hw/bitstream:rom",
    data = ":otp_img_bootstrap_rma",
    meminfo = "//hw/bitstream:otp_mmi",
    tags = [
        "vivado",
    ],
    update_usr_access = True,
    visibility = ["//visibility:private"],
)

opentitan_functest(
    name = "e2e_bootstrap_rma_iteration_1",
    srcs = ["rom_e2e_bootstrap_rma_test.c"],
    cw310 = cw310_params(
        bitstream = ":bitstream_bootstrap_rma",
        tags = ["vivado"],
        test_cmds = [
            "--rom-kind=rom",
            "--bitstream=\"$(location {bitstream})\"",
            "--bootstrap=\"$(location {flash})\"",
        ],
    ),
    key = LC_KEY_TYPES[CONST.LCV.PROD][0],
    targets = ["cw310_rom"],
    test_harness = "//sw/host/tests/rom/e2e_bootstrap_rma",
    deps = [
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
    ],
)

opentitan_functest(
    name = "e2e_bootstrap_disabled",
    cw310 = cw310_params(
        bitstream = "//hw/bitstream:rom_otp_bootstrap_disabled",
        tags = [
            "vivado",
        ],
        test_cmds = [
            "--bitstream=\"$(location {bitstream})\"",
        ],
    ),
    # Since the bitstream disables bootstrap, there is no firmware to
    # load into the chip.  However, opentitan_functest wants to build a
    # binary target.  We'll build an unsigned do-nothing binary.
    ot_flash_binary = ":empty_test_slot_a",
    signed = False,
    targets = ["cw310_rom"],
    test_harness = "//sw/host/tests/rom/e2e_bootstrap_disabled",
)

[
    bitstream_splice(
        name = "bitstream_chip_specific_startup_{}".format(lc_state.lower()),
        src = "//hw/bitstream:rom",
        data = ":otp_img_e2e_bootstrap_entry_{}".format(lc_state.lower()),
        meminfo = "//hw/bitstream:otp_mmi",
        tags = ["vivado"] + maybe_skip_in_ci(lc_state_val),
        update_usr_access = True,
    )
    for lc_state, lc_state_val in get_lc_items()
]

[
    opentitan_functest(
        name = "e2e_chip_specific_startup_{}".format(lc_state.lower()),
        srcs = ["chip_specific_startup.c"],
        args = [],
        cw310 = cw310_params(
            bitstream = ":bitstream_chip_specific_startup_{}".format(lc_state.lower()),
            otp = ":otp_img_e2e_bootstrap_entry_{}".format(lc_state.lower()),
            tags = ["vivado"] + maybe_skip_in_ci(lc_state_val),
            test_cmds = [
                "--rom-kind=rom",
                "--bitstream=\"$(location //sw/device/silicon_creator/rom/e2e:bitstream_chip_specific_startup_{})\"".format(lc_state.lower()),
                "--bootstrap=\"$(location {flash})\"",
                "--otp-unprogrammed",
            ],
        ),
        signed = True,
        targets = ["cw310_rom"],
        test_harness = "//sw/host/tests/rom/e2e_chip_specific_startup",
        deps = [
            "//hw/ip/csrng/data:csrng_regs",
            "//hw/ip/edn/data:edn_regs",
            "//hw/ip/entropy_src/data:entropy_src_regs",
            "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
            "//hw/top_earlgrey/ip/sensor_ctrl/data:sensor_ctrl_regs",
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/base:mmio",
            "//sw/device/lib/dif:clkmgr",
            "//sw/device/lib/dif:lc_ctrl",
            "//sw/device/lib/dif:otp_ctrl",
            "//sw/device/lib/dif:sram_ctrl",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing/json:chip_specific_startup",
            "//sw/device/lib/testing/json:command",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/lib/testing/test_framework:ujson_ottf",
            "//sw/device/lib/ujson",
        ],
    )
    for lc_state, lc_state_val in get_lc_items()
]

test_suite(
    name = "e2e_chip_specific_startup",
    tags = ["manual"],
    tests = [
        "e2e_chip_specific_startup_{}".format(lc_state)
        for lc_state, _ in get_lc_items()
    ],
)

opentitan_functest(
    name = "rom_ext_a_flash_a",
    cw310 = cw310_params(
        exit_failure = CONST.SHUTDOWN.PREFIX.BFV,
        exit_success = MSG_STARTING_ROM_EXT,
    ),
    ot_flash_binary = "//sw/device/silicon_creator/rom_ext:rom_ext_slot_a",
    targets = ["cw310_rom"],
)

opentitan_multislot_flash_binary(
    name = "rom_ext_b_flash_b_image",
    srcs = {
        "//sw/device/silicon_creator/rom_ext:rom_ext_slot_b": {
            "key": "fake_test_key_0",
            "offset": SLOTS["b"],
        },
    },
)

opentitan_functest(
    name = "rom_ext_b_flash_b",
    cw310 = cw310_params(
        exit_failure = CONST.SHUTDOWN.PREFIX.BFV,
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
            "key": "fake_test_key_0",
            "offset": SLOTS["b"],
        },
    },
)

opentitan_functest(
    name = "rom_ext_a_flash_b",
    cw310 = cw310_params(
        exit_failure = MSG_STARTING_ROM_EXT,
        exit_success = MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.INTERRUPT.STORE_ACCESS)),
    ),
    key = "multislot",
    ot_flash_binary = ":rom_ext_a_flash_b_image",
    targets = ["cw310_rom"],
)

opentitan_multislot_flash_binary(
    name = "rom_ext_b_flash_a_image",
    srcs = {
        "//sw/device/silicon_creator/rom_ext:rom_ext_slot_b": {
            "key": "fake_test_key_0",
            "offset": SLOTS["a"],
        },
    },
)

opentitan_functest(
    name = "rom_ext_b_flash_a",
    cw310 = cw310_params(
        exit_failure = MSG_STARTING_ROM_EXT,
        exit_success = MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.INTERRUPT.STORE_ACCESS)),
    ),
    key = "multislot",
    ot_flash_binary = ":rom_ext_b_flash_a_image",
    targets = ["cw310_rom"],
)

opentitan_functest(
    name = "rom_ext_v_flash_a",
    cw310 = cw310_params(
        exit_failure = CONST.SHUTDOWN.PREFIX.BFV,
        exit_success = MSG_STARTING_ROM_EXT,
    ),
    ot_flash_binary = "//sw/device/silicon_creator/rom_ext:rom_ext_slot_virtual",
    targets = ["cw310_rom"],
)

opentitan_multislot_flash_binary(
    name = "rom_ext_v_flash_b_image",
    srcs = {
        "//sw/device/silicon_creator/rom_ext:rom_ext_slot_virtual": {
            "key": "fake_test_key_0",
            "offset": SLOTS["b"],
        },
    },
)

opentitan_functest(
    name = "rom_ext_v_flash_b",
    cw310 = cw310_params(
        exit_failure = CONST.SHUTDOWN.PREFIX.BFV,
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
        exit_success = MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.INTERRUPT.ILLEGAL_INSTRUCTION)),
    ),
    ot_flash_binary = "//sw/device/silicon_creator/rom_ext:rom_ext_slot_a_bad_address_translation",
    targets = ["cw310_rom"],
)

test_suite(
    name = "address_translation",
    tags = ["manual"],
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
        exit_success = MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.SIGVERIFY.BAD_KEY)),
    ),
    key = "unauthorized_0",
    ot_flash_binary = ":empty_test_slot_a",
    targets = ["cw310_rom"],
)

[otp_image(
    name = "otp_img_shutdown_output_{}".format(lc_state),
    src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
    overlays = STD_OTP_OVERLAYS,
) for lc_state, _ in get_lc_items()]

# Splice OTP images into bitstreams
[
    bitstream_splice(
        name = "bitstream_shutdown_output_{}".format(lc_state),
        src = "//hw/bitstream:rom",
        data = ":otp_img_shutdown_output_{}".format(lc_state),
        meminfo = "//hw/bitstream:otp_mmi",
        tags = ["vivado"],
        update_usr_access = True,
    )
    for lc_state, _ in get_lc_items()
]

manifest({
    "name": "manifest_bad_identifier",
    "address_translation": hex(CONST.FALSE),
    "identifier": "0",
})

[opentitan_functest(
    name = "shutdown_output_{}".format(lc_state),
    cw310 = cw310_params(
        bitstream = ":bitstream_shutdown_output_{}".format(lc_state),
        exit_failure = MSG_PASS,
        exit_success = MSG_TEMPLATE_BFV_LCV.format(
            hex_digits(CONST.BFV.BOOT_POLICY.BAD_IDENTIFIER),
            hex_digits(lc_state_val),
        ),
        otp = ":otp_img_shutdown_output_{}".format(lc_state),
        tags = ["vivado"] + maybe_skip_in_ci(lc_state_val),
    ),
    dv = dv_params(
        otp = ":otp_img_shutdown_output_{}".format(lc_state),
        rom = "//sw/device/silicon_creator/rom:rom_with_fake_keys",
    ),
    manifest = ":manifest_bad_identifier",
    ot_flash_binary = ":empty_test_slot_a",
    signed = False,
    targets = [
        "cw310_rom",
        "dv",
    ],
) for lc_state, lc_state_val in get_lc_items()]

test_suite(
    name = "shutdown_output",
    tags = ["manual"],
    tests = ["shutdown_output_{}".format(lc_state) for lc_state, _ in get_lc_items()],
)

SEC_VERS = [
    0,
    1,
    2,
]

[manifest({
    "name": "manifest_sec_ver_{}".format(sec_ver),
    "address_translation": hex(CONST.FALSE),
    "identifier": hex(CONST.ROM_EXT),
    "security_version": hex(sec_ver),
}) for sec_ver in SEC_VERS]

[opentitan_flash_binary(
    name = "empty_test_slot_{}_sec_ver_{}".format(slot, sec_ver),
    srcs = ["empty_test.c"],
    devices = ["fpga_cw310"],
    local_defines = [
        shell.quote("EMPTY_TEST_MSG=\"slot=%p, security_version=%01d, lc_state=0x%08x\", manifest_def_get(), manifest_def_get()->security_version, lifecycle_raw_state_get()"),
    ],
    manifest = ":manifest_sec_ver_{}".format(sec_ver),
    signed = True,
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_{}".format(slot),
    ],
) for slot in SLOTS for sec_ver in SEC_VERS]

[opentitan_multislot_flash_binary(
    name = "sec_ver_{}_{}_image".format(sec_ver_a, sec_ver_b),
    srcs = {
        ":empty_test_slot_a_sec_ver_{}".format(sec_ver_a): {
            "key": "fake_prod_key_0",
            "offset": SLOTS["a"],
        },
        ":empty_test_slot_b_sec_ver_{}".format(sec_ver_b): {
            "key": "fake_prod_key_0",
            "offset": SLOTS["b"],
        },
    },
    devices = ["fpga_cw310"],
) for sec_ver_a in SEC_VERS for sec_ver_b in SEC_VERS]

BOOT_POLICY_NEWER_CASES = [
    {
        "a": 0,
        "b": 0,
        "exit_success": "slot=0x20000000, security_version=0, lc_state=0x{}",
    },
    {
        "a": 0,
        "b": 1,
        "exit_success": "slot=0x20080000, security_version=1, lc_state=0x{}",
    },
    {
        "a": 1,
        "b": 0,
        "exit_success": "slot=0x20000000, security_version=1, lc_state=0x{}",
    },
    {
        "a": 1,
        "b": 1,
        "exit_success": "slot=0x20000000, security_version=1, lc_state=0x{}",
    },
]

[otp_image(
    name = "otp_img_boot_policy_newer_{}".format(lc_state.lower()),
    src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state.lower()),
    overlays = STD_OTP_OVERLAYS,
) for lc_state in structs.to_dict(CONST.LCV)]

# Splice OTP images into bitstreams
[
    bitstream_splice(
        name = "bitstream_boot_policy_newer_{}".format(lc_state.lower()),
        src = "//hw/bitstream:rom",
        data = ":otp_img_boot_policy_newer_{}".format(lc_state.lower()),
        meminfo = "//hw/bitstream:otp_mmi",
        tags = ["vivado"],
        update_usr_access = True,
    )
    for lc_state in structs.to_dict(CONST.LCV)
]

[opentitan_functest(
    name = "boot_policy_newer_{}_a_{}_b_{}".format(
        lc_state.lower(),
        t["a"],
        t["b"],
    ),
    cw310 = cw310_params(
        bitstream = ":bitstream_boot_policy_newer_{}".format(lc_state.lower()),
        exit_success = t["exit_success"].format(hex_digits(lc_state_val)),
        tags = ["vivado"] + maybe_skip_in_ci(lc_state_val),
    ),
    key = "multislot",
    ot_flash_binary = ":sec_ver_{}_{}_image".format(
        t["a"],
        t["b"],
    ),
    targets = ["cw310_rom"],
) for lc_state, lc_state_val in structs.to_dict(CONST.LCV).items() for t in BOOT_POLICY_NEWER_CASES]

test_suite(
    name = "boot_policy_newer",
    tags = ["manual"],
    tests = ["boot_policy_newer_{}_a_{}_b_{}".format(
        lc_state.lower(),
        t["a"],
        t["b"],
    ) for lc_state in structs.to_dict(CONST.LCV) for t in BOOT_POLICY_NEWER_CASES],
)

BOOT_POLICY_ROLLBACK_CASES = [
    {
        "a": 0,
        "b": 0,
        "exit_success": MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.BOOT_POLICY.ROLLBACK)),
    },
    {
        "a": 0,
        "b": 1,
        "exit_success": "slot=0x20080000, security_version=1",
    },
    {
        "a": 2,
        "b": 0,
        "exit_success": "slot=0x20000000, security_version=2",
    },
    {
        "a": 1,
        "b": 1,
        "exit_success": "slot=0x20000000, security_version=1",
    },
]

otp_json(
    name = "otp_json_boot_policy_rollback",
    partitions = [
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {
                "CREATOR_SW_CFG_MIN_SEC_VER_ROM_EXT": "1",
            },
        ),
    ],
)

[otp_image(
    name = "otp_img_boot_policy_rollback_{}".format(lc_state),
    src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
    overlays = STD_OTP_OVERLAYS + [":otp_json_boot_policy_rollback"],
    visibility = ["//visibility:private"],
) for lc_state, _ in get_lc_items()]

[bitstream_splice(
    name = "bitstream_boot_policy_rollback_{}".format(
        lc_state,
    ),
    src = "//hw/bitstream:rom",
    data = ":otp_img_boot_policy_rollback_{}".format(
        lc_state,
    ),
    meminfo = "//hw/bitstream:otp_mmi",
    tags = ["vivado"],
    update_usr_access = True,
    visibility = ["//visibility:private"],
) for lc_state, _ in get_lc_items()]

[
    opentitan_functest(
        name = "boot_policy_rollback_{}_a_{}_b_{}".format(
            lc_state,
            t["a"],
            t["b"],
        ),
        cw310 = cw310_params(
            bitstream = "bitstream_boot_policy_rollback_{}".format(lc_state),
            exit_success = t["exit_success"],
            tags = ["vivado"] + maybe_skip_in_ci(lc_state_val),
        ),
        key = "multislot",
        ot_flash_binary = ":sec_ver_{}_{}_image".format(
            t["a"],
            t["b"],
        ),
        targets = ["cw310_rom"],
    )
    for lc_state, lc_state_val in get_lc_items()
    for t in BOOT_POLICY_ROLLBACK_CASES
]

test_suite(
    name = "rom_e2e_boot_policy_rollback",
    tags = ["manual"],
    tests = [
        "boot_policy_rollback_{}_a_{}_b_{}".format(
            lc_state,
            t["a"],
            t["b"],
        )
        for lc_state, _ in get_lc_items()
        for t in BOOT_POLICY_ROLLBACK_CASES
    ],
)

# Watchdog configuration test cases.
#
# These test cases verify the ROM correctly configures the watchdog in each life
# cycle state. Tests are run for OTP configurations that disable the watchdog
# and for OTP configurations that enable the watchdog.

# Watchdog bite threshold for the watchdog-enabled cases. This is 2 seconds,
# assuming a 200kHz clock.
WATCHDOG_BITE_THRESHOLD = "0x61a80"

# OTP overlay that enables the watchdog. The bite threshold is 2 seconds,
# assuming a 200kHz clock.
otp_json(
    name = "otp_json_watchdog_enable",
    partitions = [
        otp_partition(
            name = "OWNER_SW_CFG",
            items = {"OWNER_SW_CFG_ROM_WATCHDOG_BITE_THRESHOLD_CYCLES": WATCHDOG_BITE_THRESHOLD},
        ),
    ],
)

# OTP images that enable the watchdog.
[otp_image(
    name = "otp_img_watchdog_enable_{}".format(lc_state.lower()),
    src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state.lower()),
    overlays = STD_OTP_OVERLAYS + [":otp_json_watchdog_enable"],
) for lc_state in structs.to_dict(CONST.LCV)]

# Bitstreams with the watchdog-enable OTP images spliced in.
[bitstream_splice(
    name = "bitstream_watchdog_enable_{}".format(lc_state.lower()),
    src = "//hw/bitstream:rom",
    data = ":otp_img_watchdog_enable_{}".format(lc_state.lower()),
    meminfo = "//hw/bitstream:otp_mmi",
    tags = ["vivado"] + maybe_skip_in_ci(lc_state_val),
    update_usr_access = True,
) for lc_state, lc_state_val in structs.to_dict(CONST.LCV).items()]

# Creates a binary that confirms the watchdog is enabled and a binary that
# confirms the watchdog is disabled.
[opentitan_flash_binary(
    name = "test_watchdog_{}".format(watchdog_config),
    srcs = ["watchdog_test.c"],
    devices = [
        "fpga_cw310",
        "sim_verilator",
    ],
    local_defines = [
        "EXPECT_WATCHDOG_{}".format(watchdog_config.upper()),
        "WATCHDOG_BITE_THRESHOLD={}".format(WATCHDOG_BITE_THRESHOLD),
    ],
    deps = [
        "//hw/ip/aon_timer/data:aon_timer_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
) for watchdog_config in [
    "disabled",
    "enabled",
]]

WATCHDOG_TEST_CASES = {
    "disable": {
        "DEV": "disabled",
        "PROD": "disabled",
        "PROD_END": "disabled",
        "RMA": "disabled",
        "TEST_UNLOCKED0": "disabled",
    },
    "enable": {
        "DEV": "enabled",
        "PROD": "enabled",
        "PROD_END": "enabled",
        "RMA": "disabled",
        "TEST_UNLOCKED0": "disabled",
    },
}

# Bitstream targets (CW310) and otp images (verilator) for the watchdog config
# tests. The format argument should be replaced with the desired life cycle
# state.
WATCHDOG_BITSTREAM = {
    "disable": "//hw/bitstream:rom_otp_{}",
    "enable": ":bitstream_watchdog_enable_{}",
}

WATCHDOG_OTP = {
    "disable": "//hw/ip/otp_ctrl/data:img_{}",
    "enable": ":otp_img_watchdog_enable_{}",
}

[opentitan_functest(
    name = "watchdog_{}_{}".format(
        otp_config,
        lc_state.lower(),
    ),
    cw310 = cw310_params(
        bitstream = WATCHDOG_BITSTREAM[otp_config].format(lc_state.lower()),
        tags = ["vivado"] + maybe_skip_in_ci(lc_state_val),
    ),
    ot_flash_binary = ":test_watchdog_{}".format(WATCHDOG_TEST_CASES[otp_config][lc_state]),
    targets = [
        "cw310_rom",
        "verilator",
    ],
    verilator = verilator_params(
        timeout = "eternal",
        otp = WATCHDOG_OTP[otp_config].format(lc_state.lower()),
        rom = "//sw/device/silicon_creator/rom:rom_with_fake_keys",
        # Test cases that enable the watchdog time out in verilator, cause
        # unknown.
        tags = ["broken"] if WATCHDOG_TEST_CASES[otp_config][lc_state] == "enabled" else [],
    ),
) for otp_config in [
    "disable",
    "enable",
] for lc_state, lc_state_val in structs.to_dict(CONST.LCV).items()]

test_suite(
    name = "rom_e2e_watchdog_reconfig",
    tags = ["manual"],
    tests = [
        "watchdog_{}_{}".format(
            otp_config,
            lc_state.lower(),
        )
        for otp_config in [
            "disable",
            "enable",
        ]
        for lc_state in structs.to_dict(CONST.LCV)
    ],
)

# Alert Handler configuration test cases.
#
# These test cases verify the ROM correctly configures the alert_handler in each
# life cycle state.

# Alert handler configuration is not checked in the TEST LC state.
ALERT_LC_STATES = get_lc_items(
    CONST.LCV.PROD,
    CONST.LCV.PROD_END,
    CONST.LCV.DEV,
    CONST.LCV.RMA,
)

[otp_image(
    name = "otp_img_alert_{}".format(lc_state),
    src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
    overlays = STD_OTP_OVERLAYS,
) for lc_state, _ in ALERT_LC_STATES]

[bitstream_splice(
    name = "bitstream_alert_{}".format(lc_state),
    src = "//hw/bitstream:rom",
    data = ":otp_img_alert_{}".format(lc_state),
    meminfo = "//hw/bitstream:otp_mmi",
    tags = ["vivado"] + maybe_skip_in_ci(lc_state_val),
    update_usr_access = True,
) for lc_state, lc_state_val in ALERT_LC_STATES]

[opentitan_flash_binary(
    name = "rom_e2e_alert_config_test_{}".format(lc_state),
    srcs = ["rom_e2e_alert_config_test.c"],
    devices = [
        "fpga_cw310",
    ],
    local_defines = [
        "OTP_ALERT_DIGEST=OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_ALERT_DIGEST_{}_OFFSET".format(lc_state.upper()),
    ],
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:alert",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
    ],
) for lc_state, _ in ALERT_LC_STATES]

[
    opentitan_functest(
        name = "alert_{}".format(
            lc_state,
        ),
        cw310 = cw310_params(
            bitstream = ":bitstream_alert_{}".format(lc_state),
            tags = ["vivado"] + maybe_skip_in_ci(lc_state_val),
        ),
        key = "fake_prod_key_0",
        ot_flash_binary = ":rom_e2e_alert_config_test_{}".format(lc_state),
        signed = True,
        targets = [
            "cw310_rom",
        ],
    )
    for lc_state, lc_state_val in ALERT_LC_STATES
]

test_suite(
    name = "rom_e2e_alert_config",
    tags = ["manual"],
    tests = [
        "alert_{}".format(lc_state)
        for lc_state, _ in ALERT_LC_STATES
    ],
)

otp_json(
    name = "shutdown_alert_owner_sw_cfg",
    partitions = [
        otp_partition(
            name = "OWNER_SW_CFG",
            items = {
                # Enable bootstrap.
                "OWNER_SW_CFG_ROM_BOOTSTRAP_EN": hex(CONST.TRUE),
                # Report errors without any redaction.
                "OWNER_SW_CFG_ROM_ERROR_REPORTING": hex(CONST.SHUTDOWN.REDACT.NONE),
                # Enable class A alerts.
                "OWNER_SW_CFG_ROM_ALERT_CLASS_EN": hex(
                    CONST.ALERT.NONE << 24 |
                    CONST.ALERT.NONE << 16 |
                    CONST.ALERT.NONE << 8 |
                    CONST.ALERT.ENABLE,
                ),
                # Configure class A to escalate until phase 3 and disable other classes.
                "OWNER_SW_CFG_ROM_ALERT_ESCALATION": hex(
                    CONST.ALERT.ESC_NONE << 24 |
                    CONST.ALERT.ESC_NONE << 16 |
                    CONST.ALERT.ESC_NONE << 8 |
                    CONST.ALERT.ESC_PHASE_3,
                ),
                # Classify UART0 alerts (alert source 0) as class A and leave others as unconfigured.
                "OWNER_SW_CFG_ROM_ALERT_CLASSIFICATION": [
                    hex(
                        CONST.ALERT.CLASS_A << 24 |
                        CONST.ALERT.CLASS_A << 16 |
                        CONST.ALERT.CLASS_A << 8 |
                        CONST.ALERT.CLASS_A,
                    ),
                ] + [
                    hex(
                        CONST.ALERT.CLASS_X << 24 |
                        CONST.ALERT.CLASS_X << 16 |
                        CONST.ALERT.CLASS_X << 8 |
                        CONST.ALERT.CLASS_X,
                    ),
                ] * 79,
                # Leave local alert classification as unconfigured.
                "OWNER_SW_CFG_ROM_LOCAL_ALERT_CLASSIFICATION": [hex(
                    CONST.ALERT.CLASS_X << 24 |
                    CONST.ALERT.CLASS_X << 16 |
                    CONST.ALERT.CLASS_X << 8 |
                    CONST.ALERT.CLASS_X,
                )] * 16,
                # Set the alert accumulation thresholds to 0.
                "OWNER_SW_CFG_ROM_ALERT_ACCUM_THRESH": ["0x00000000"] * 4,
                # Set the alert timeout cycles to 0.
                "OWNER_SW_CFG_ROM_ALERT_TIMEOUT_CYCLES": ["0x00000000"] * 4,
                # Set the alert phase cycles to 0.
                "OWNER_SW_CFG_ROM_ALERT_PHASE_CYCLES": ["0x00000000"] * 16,
            },
        ),
    ],
)

otp_alert_digest(
    name = "shutdown_alert_digest_cfg",
    otp_img = ":shutdown_alert_owner_sw_cfg",
)

[otp_image(
    name = "otp_img_shutdown_alert_{}".format(lc_state),
    src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
    overlays = STD_OTP_OVERLAYS + [
        ":shutdown_alert_owner_sw_cfg",
        ":shutdown_alert_digest_cfg",
    ],
) for lc_state, _ in ALERT_LC_STATES]

[bitstream_splice(
    name = "bitstream_shutdown_alert_{}".format(lc_state),
    src = "//hw/bitstream:rom",
    data = ":otp_img_shutdown_alert_{}".format(lc_state),
    meminfo = "//hw/bitstream:otp_mmi",
    tags = ["vivado"] + maybe_skip_in_ci(lc_state_val),
    update_usr_access = True,
) for lc_state, lc_state_val in ALERT_LC_STATES]

[opentitan_flash_binary(
    name = "rom_e2e_shutdown_alert_config_test_{}".format(lc_state),
    srcs = ["rom_e2e_shutdown_alert_config_test.c"],
    devices = [
        "fpga_cw310",
    ],
    deps = [
        "//hw/ip/uart/data:uart_regs",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
    ],
) for lc_state, _ in ALERT_LC_STATES]

[
    opentitan_functest(
        name = "shutdown_alert_{}".format(lc_state),
        cw310 = cw310_params(
            bitstream = ":bitstream_shutdown_alert_{}".format(lc_state),
            tags = ["vivado"] + maybe_skip_in_ci(lc_state_val),
        ),
        key = "fake_prod_key_0",
        ot_flash_binary = ":rom_e2e_shutdown_alert_config_test_{}".format(lc_state),
        signed = True,
        targets = [
            "cw310_rom",
        ],
    )
    for lc_state, lc_state_val in ALERT_LC_STATES
]

test_suite(
    name = "rom_e2e_shutdown_alert_config",
    tags = ["manual"],
    tests = [
        "shutdown_alert_{}".format(lc_state)
        for lc_state, _ in ALERT_LC_STATES
    ],
)

SIGVERIFY_MOD_EXP_CASES = [
    {
        "name": "sw",
        "use_sw_rsa_verify": CONST.TRUE,
        "exit_success": {lc_state: "use_sw_rsa_verify=0x00000739" for lc_state, _ in get_lc_items()},
    },
    {
        "name": "otbn",
        "use_sw_rsa_verify": CONST.FALSE,
        "exit_success": {lc_state: "use_sw_rsa_verify=0x000001d4" for lc_state, _ in get_lc_items()},
    },
    {
        "name": "invalid",
        "use_sw_rsa_verify": 0,
        "exit_success": {
            lc_state: MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.INTERRUPT.ILLEGAL_INSTRUCTION)) if lc_state_val != CONST.LCV.TEST_UNLOCKED0 else "use_sw_rsa_verify=0x00000000"
            for lc_state, lc_state_val in get_lc_items()
        },
    },
]

opentitan_flash_binary(
    name = "empty_test_sigverify_mod_exp",
    srcs = ["empty_test.c"],
    devices = [
        "fpga_cw310",
        "sim_dv",
    ],
    local_defines = [
        shell.quote("EMPTY_TEST_MSG=\"use_sw_rsa_verify=0x%08x\", otp_read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_SIGVERIFY_RSA_MOD_EXP_IBEX_EN_OFFSET)"),
    ],
    signed = True,
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
    ],
)

[
    otp_json(
        name = "otp_json_sigverify_mod_exp_{}".format(t["name"]),
        partitions = [
            otp_partition(
                name = "CREATOR_SW_CFG",
                items = {"CREATOR_SW_CFG_SIGVERIFY_RSA_MOD_EXP_IBEX_EN": hex(t["use_sw_rsa_verify"])},
            ),
        ],
    )
    for t in SIGVERIFY_MOD_EXP_CASES
]

[
    otp_image(
        name = "otp_img_sigverify_mod_exp_{}_{}".format(
            lc_state,
            t["name"],
        ),
        src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
        overlays = STD_OTP_OVERLAYS + [":otp_json_sigverify_mod_exp_{}".format(t["name"])],
        visibility = ["//visibility:private"],
    )
    for lc_state, _ in get_lc_items()
    for t in SIGVERIFY_MOD_EXP_CASES
]

[
    bitstream_splice(
        name = "bitstream_sigverify_mod_exp_{}_{}".format(
            lc_state,
            t["name"],
        ),
        src = "//hw/bitstream:rom",
        data = ":otp_img_sigverify_mod_exp_{}_{}".format(
            lc_state,
            t["name"],
        ),
        meminfo = "//hw/bitstream:otp_mmi",
        tags = ["vivado"],
        update_usr_access = True,
        visibility = ["//visibility:private"],
    )
    for lc_state, _ in get_lc_items()
    for t in SIGVERIFY_MOD_EXP_CASES
]

[
    opentitan_functest(
        name = "sigverify_mod_exp_{}_{}".format(
            lc_state,
            t["name"],
        ),
        cw310 = cw310_params(
            bitstream = ":bitstream_sigverify_mod_exp_{}_{}".format(
                lc_state,
                t["name"],
            ),
            exit_success = t["exit_success"][lc_state],
            tags = ["vivado"] + maybe_skip_in_ci(lc_state_val),
        ),
        ot_flash_binary = ":empty_test_sigverify_mod_exp",
        targets = ["cw310_rom"],
    )
    for lc_state, lc_state_val in get_lc_items()
    for t in SIGVERIFY_MOD_EXP_CASES
]

test_suite(
    name = "rom_e2e_sigverify_mod_exp",
    tags = ["manual"],
    tests = [
        "sigverify_mod_exp_{}_{}".format(
            lc_state,
            t["name"],
        )
        for lc_state, _ in get_lc_items()
        for t in SIGVERIFY_MOD_EXP_CASES
    ],
)

BOOT_POLICY_BAD_MANIFEST_CASES = [
    {
        "name": "bad_identifier",
        "manifest": {
            "identifier": "0",
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.BOOT_POLICY.BAD_IDENTIFIER)),
    },
    {
        "name": "too_small",
        "manifest": {
            "identifier": hex(CONST.ROM_EXT),
            "length": hex(CONST.ROM_EXT_SIZE_MIN - 1),
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.BOOT_POLICY.BAD_LENGTH)),
    },
    {
        "name": "too_large",
        "manifest": {
            "identifier": hex(CONST.ROM_EXT),
            "length": hex(CONST.ROM_EXT_SIZE_MAX + 1),
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.BOOT_POLICY.BAD_LENGTH)),
    },
    {
        "name": "empty_code",
        "manifest": {
            # Note: `length` is filled automatically unless overriden here.
            "identifier": hex(CONST.ROM_EXT),
            "code_start": hex(CONST.MANIFEST_SIZE + 12),
            "code_end": hex(CONST.MANIFEST_SIZE + 12),
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.MANIFEST.BAD_CODE_REGION)),
    },
    {
        "name": "code_in_manifest",
        "manifest": {
            "identifier": hex(CONST.ROM_EXT),
            "code_start": hex(CONST.MANIFEST_SIZE - 4),
            "code_end": hex(CONST.MANIFEST_SIZE + 12),
            "entry_point": hex(CONST.MANIFEST_SIZE + 8),
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.MANIFEST.BAD_CODE_REGION)),
    },
    {
        "name": "code_outside_image",
        "manifest": {
            "identifier": hex(CONST.ROM_EXT),
            "code_start": hex(CONST.ROM_EXT_SIZE_MAX),
            "code_end": hex(CONST.MANIFEST_SIZE + 12),
            "entry_point": hex(CONST.MANIFEST_SIZE + 8),
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.MANIFEST.BAD_CODE_REGION)),
    },
    {
        "name": "code_start_unaligned",
        "manifest": {
            "identifier": hex(CONST.ROM_EXT),
            "code_start": hex(CONST.MANIFEST_SIZE + 6),
            "code_end": hex(CONST.MANIFEST_SIZE + 12),
            "entry_point": hex(CONST.MANIFEST_SIZE + 8),
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.MANIFEST.BAD_CODE_REGION)),
    },
    {
        "name": "code_end_unaligned",
        "manifest": {
            "identifier": hex(CONST.ROM_EXT),
            "code_start": hex(CONST.MANIFEST_SIZE + 8),
            "code_end": hex(CONST.MANIFEST_SIZE + 10),
            "entry_point": hex(CONST.MANIFEST_SIZE + 8),
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.MANIFEST.BAD_CODE_REGION)),
    },
    {
        "name": "entry_before_code_start",
        "manifest": {
            "identifier": hex(CONST.ROM_EXT),
            "code_start": hex(CONST.MANIFEST_SIZE + 8),
            "code_end": hex(CONST.MANIFEST_SIZE + 12),
            "entry_point": hex(CONST.MANIFEST_SIZE + 4),
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.MANIFEST.BAD_ENTRY_POINT)),
    },
    {
        "name": "entry_at_code_end",
        "manifest": {
            "identifier": hex(CONST.ROM_EXT),
            "code_start": hex(CONST.MANIFEST_SIZE + 8),
            "code_end": hex(CONST.MANIFEST_SIZE + 12),
            "entry_point": hex(CONST.MANIFEST_SIZE + 12),
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.MANIFEST.BAD_ENTRY_POINT)),
    },
    {
        "name": "entry_unaligned",
        "manifest": {
            "identifier": hex(CONST.ROM_EXT),
            "code_start": hex(CONST.MANIFEST_SIZE + 8),
            "code_end": hex(CONST.MANIFEST_SIZE + 12),
            "entry_point": hex(CONST.MANIFEST_SIZE + 10),
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.MANIFEST.BAD_ENTRY_POINT)),
    },
    {
        "name": "rollback",
        "manifest": {
            "identifier": hex(CONST.ROM_EXT),
            "code_start": hex(CONST.MANIFEST_SIZE + 8),
            "code_end": hex(CONST.MANIFEST_SIZE + 12),
            "entry_point": hex(CONST.MANIFEST_SIZE + 8),
            "security_version": "0",
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.BOOT_POLICY.ROLLBACK)),
        "sec_ver": 1,
    },
]

[opentitan_flash_binary(
    name = "boot_policy_bad_manifest_{}_{}_bin".format(
        t["name"],
        slot,
    ),
    srcs = ["empty_test.c"],
    devices = [
        "fpga_cw310",
        "sim_dv",
        "sim_verilator",
    ],
    manifest = manifest(dict(
        t["manifest"],
        name = "{}_{}".format(
            t["name"],
            slot,
        ),
    )),
    signed = True,
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_{}".format(slot),
    ],
) for t in BOOT_POLICY_BAD_MANIFEST_CASES for slot in SLOTS]

[opentitan_multislot_flash_binary(
    name = "boot_policy_bad_manifest_{}_{}_img".format(
        t["name"],
        slot,
    ),
    srcs = {
        "boot_policy_bad_manifest_{}_{}_bin".format(
            t["name"],
            slot,
        ): {
            "key": "fake_test_key_0",
            "offset": offset,
        },
    },
    devices = [
        "fpga_cw310",
        "sim_dv",
        "sim_verilator",
    ],
) for t in BOOT_POLICY_BAD_MANIFEST_CASES for slot, offset in SLOTS.items()]

[
    otp_json(
        name = "otp_json_sec_ver_{}".format(sec_ver),
        partitions = [
            otp_partition(
                name = "CREATOR_SW_CFG",
                items = {
                    "CREATOR_SW_CFG_MIN_SEC_VER_ROM_EXT": "{}".format(sec_ver),
                },
            ),
        ],
    )
    for sec_ver in [
        0,
        1,
    ]
]

[
    otp_image(
        name = "otp_img_boot_policy_bad_manifest_{}_sec_ver_{}".format(
            lc_state,
            sec_ver,
        ),
        src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
        overlays = STD_OTP_OVERLAYS + [":otp_json_sec_ver_{}".format(sec_ver)],
        visibility = ["//visibility:private"],
    )
    for lc_state, _ in get_lc_items()
    for sec_ver in [
        0,
        1,
    ]
]

[
    bitstream_splice(
        name = "bitstream_boot_policy_bad_manifest_{}_sec_ver_{}".format(
            lc_state,
            sec_ver,
        ),
        src = "//hw/bitstream:rom",
        data = ":otp_img_boot_policy_bad_manifest_{}_sec_ver_{}".format(
            lc_state,
            sec_ver,
        ),
        meminfo = "//hw/bitstream:otp_mmi",
        tags = ["vivado"],
        update_usr_access = True,
        visibility = ["//visibility:private"],
    )
    for lc_state, _ in get_lc_items()
    for sec_ver in [
        0,
        1,
    ]
]

[
    opentitan_functest(
        name = "boot_policy_bad_manifest_{}_{}_{}".format(
            lc_state,
            t["name"],
            slot,
        ),
        cw310 = cw310_params(
            bitstream = "bitstream_boot_policy_bad_manifest_{}_sec_ver_{}".format(
                lc_state,
                t.get("sec_ver", 0),
            ),
            exit_success = t["exit_success"],
            tags = ["vivado"] + maybe_skip_in_ci(lc_state_val),
        ),
        key = "multislot",
        ot_flash_binary = "boot_policy_bad_manifest_{}_{}_img".format(
            t["name"],
            slot,
        ),
        targets = [
            "cw310_rom",
            "verilator",
        ],
        verilator = verilator_params(
            tags = [
                # FIXME:#16056 Verilator fails to set up test.
                "vivado",
                "broken",
            ],
        ),
    )
    for lc_state, lc_state_val in get_lc_items()
    for t in BOOT_POLICY_BAD_MANIFEST_CASES
    for slot in SLOTS
]

test_suite(
    name = "rom_e2e_boot_policy_bad_manifest",
    tags = ["manual"],
    tests = [
        "boot_policy_bad_manifest_{}_{}_{}".format(
            lc_state,
            t["name"],
            slot,
        )
        for lc_state, _ in get_lc_items()
        for t in BOOT_POLICY_BAD_MANIFEST_CASES
        for slot in SLOTS
    ],
)

BOOT_DATA_RECOVERY_CASES = [
    {
        "lc_state": "test_unlocked0",
        "min_sec_ver": 0,
        "default_boot_data": "nodefault",
        "expected_bfv": None,
    },
    {
        "lc_state": "dev",
        "min_sec_ver": 1,
        "default_boot_data": "nodefault",
        "expected_bfv": None,
    },
    {
        "lc_state": "prod",
        "min_sec_ver": 1,
        "default_boot_data": "default",
        "expected_bfv": None,
    },
    {
        "lc_state": "prod",
        "min_sec_ver": 0,
        "default_boot_data": "nodefault",
        "expected_bfv": CONST.BFV.BOOT_DATA.NOT_FOUND,
    },
    {
        "lc_state": "prod_end",
        "min_sec_ver": 0,
        "default_boot_data": "default",
        "expected_bfv": None,
    },
    {
        "lc_state": "prod_end",
        "min_sec_ver": 1,
        "default_boot_data": "nodefault",
        "expected_bfv": CONST.BFV.BOOT_DATA.NOT_FOUND,
    },
    {
        "lc_state": "rma",
        "min_sec_ver": 0,
        "default_boot_data": "nodefault",
        "expected_bfv": None,
    },
]

[otp_json(
    name = "boot_data_recovery_creator_sw_cfg_{}_{}".format(
        case["lc_state"],
        case["default_boot_data"],
    ),
    partitions = [
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {
                # Set the min_sec version.
                "CREATOR_SW_CFG_MIN_SEC_VER_ROM_EXT": hex(case["min_sec_ver"]),
                # Set allowing use of default boot data in PROD LC state.
                "CREATOR_SW_CFG_DEFAULT_BOOT_DATA_IN_PROD_EN": hex(
                    CONST.TRUE if case["default_boot_data"] == "default" else CONST.FALSE,
                ),
            },
        ),
    ],
) for case in BOOT_DATA_RECOVERY_CASES]

[otp_image(
    name = "otp_img_boot_data_recovery_{}_{}".format(
        case["lc_state"],
        case["default_boot_data"],
    ),
    src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(case["lc_state"]),
    overlays = STD_OTP_OVERLAYS + [":boot_data_recovery_creator_sw_cfg_{}_{}".format(
        case["lc_state"],
        case["default_boot_data"],
    )],
) for case in BOOT_DATA_RECOVERY_CASES]

[bitstream_splice(
    name = "bitstream_boot_data_recovery_{}_{}".format(
        case["lc_state"],
        case["default_boot_data"],
    ),
    src = "//hw/bitstream:rom",
    data = ":otp_img_boot_data_recovery_{}_{}".format(
        case["lc_state"],
        case["default_boot_data"],
    ),
    meminfo = "//hw/bitstream:otp_mmi",
    tags = ["vivado"] + maybe_skip_in_ci(getattr(
        CONST.LCV,
        case["lc_state"].upper(),
    )),
    update_usr_access = True,
) for case in BOOT_DATA_RECOVERY_CASES]

[opentitan_flash_binary(
    name = "rom_e2e_boot_data_recovery_{}_{}".format(
        case["lc_state"],
        case["default_boot_data"],
    ),
    srcs = ["empty_test.c"],
    devices = [
        "fpga_cw310",
    ],
    manifest = manifest(
        dict(
            name = "boot_data_recovery_manifest_{}_{}".format(
                case["lc_state"],
                case["default_boot_data"],
            ),
            address_translation = hex(CONST.FALSE),
            identifier = hex(CONST.ROM_EXT),
            security_version = hex(2),
        ),
    ),
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:otp",
    ],
) for case in BOOT_DATA_RECOVERY_CASES]

[
    opentitan_functest(
        name = "boot_data_recovery_{}_{}".format(
            case["lc_state"],
            case["default_boot_data"],
        ),
        cw310 = cw310_params(
            bitstream = ":bitstream_boot_data_recovery_{}_{}".format(
                case["lc_state"],
                case["default_boot_data"],
            ),
            exit_success = MSG_TEMPLATE_BFV.format(hex_digits(case["expected_bfv"])) if case["expected_bfv"] != None else MSG_PASS,
            tags = ["vivado"] + maybe_skip_in_ci(getattr(
                CONST.LCV,
                case["lc_state"].upper(),
            )),
        ),
        key = "fake_prod_key_0",
        ot_flash_binary = ":rom_e2e_boot_data_recovery_{}_{}".format(
            case["lc_state"],
            case["default_boot_data"],
        ),
        signed = True,
        targets = [
            "cw310_rom",
        ],
    )
    for case in BOOT_DATA_RECOVERY_CASES
]

test_suite(
    name = "rom_e2e_boot_data_recovery",
    tags = ["manual"],
    tests = [
        "boot_data_recovery_{}_{}".format(
            case["lc_state"],
            case["default_boot_data"],
        )
        for case in BOOT_DATA_RECOVERY_CASES
    ],
)

SHUTDOWN_WATCHDOG_BITE_THRESHOLDS = [
    400000,  # 2 seconds at 200 kHz
    0,  # Watchdog disabled
]

SHUTDOWN_WATCHDOG_CASES = [
    {
        "lc_state": lc_state,
        "exit_success": "Returning after 1 seconds",
        "bite_threshold": bite_threshold,
    }
    for lc_state in [
        "test_unlocked0",
        "rma",
    ]
    for bite_threshold in SHUTDOWN_WATCHDOG_BITE_THRESHOLDS
] + [
    {
        "lc_state": lc_state,
        "exit_success": "Returning after 1 seconds" if bite_threshold == 0 else "I00000[^\r\n]*\r\nROM:[0-9a-f]{8}\r\n",
        "bite_threshold": bite_threshold,
    }
    for lc_state in [
        "dev",
        "prod",
        "prod_end",
    ]
    for bite_threshold in SHUTDOWN_WATCHDOG_BITE_THRESHOLDS
]

[
    otp_json(
        name = "otp_json_shutdown_watchdog_{}_{}".format(
            t["lc_state"],
            t["bite_threshold"],
        ),
        partitions = [
            otp_partition(
                name = "OWNER_SW_CFG",
                items = {"OWNER_SW_CFG_ROM_WATCHDOG_BITE_THRESHOLD_CYCLES": hex(t["bite_threshold"])},
            ),
        ],
    )
    for t in SHUTDOWN_WATCHDOG_CASES
]

[
    otp_image(
        name = "otp_img_shutdown_watchdog_{}_{}".format(
            t["lc_state"],
            t["bite_threshold"],
        ),
        src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(t["lc_state"]),
        overlays = STD_OTP_OVERLAYS + [
            ":otp_json_shutdown_watchdog_{}_{}".format(
                t["lc_state"],
                t["bite_threshold"],
            ),
        ],
    )
    for t in SHUTDOWN_WATCHDOG_CASES
]

[
    bitstream_splice(
        name = "bitstream_shutdown_watchdog_{}_{}".format(
            t["lc_state"],
            t["bite_threshold"],
        ),
        src = "//hw/bitstream:rom",
        data = ":otp_img_shutdown_watchdog_{}_{}".format(
            t["lc_state"],
            t["bite_threshold"],
        ),
        meminfo = "//hw/bitstream:otp_mmi",
        tags = ["vivado"],
        update_usr_access = True,
        visibility = ["//visibility:private"],
    )
    for t in SHUTDOWN_WATCHDOG_CASES
]

[
    opentitan_functest(
        name = "shutdown_watchdog_{}_{}".format(
            t["lc_state"],
            t["bite_threshold"],
        ),
        srcs = ["hang_test.c"],
        cw310 = cw310_params(
            bitstream = ":bitstream_shutdown_watchdog_{}_{}".format(
                t["lc_state"],
                t["bite_threshold"],
            ),
            exit_success = t["exit_success"],
            tags = ["vivado"] + maybe_skip_in_ci(getattr(
                CONST.LCV,
                t["lc_state"].upper(),
            )),
        ),
        local_defines = [
            "HANG_SECS=1",
        ],
        targets = ["cw310_rom"],
        deps = [
            "//sw/device/lib/testing/test_framework:ottf_main",
        ],
    )
    for t in SHUTDOWN_WATCHDOG_CASES
]

test_suite(
    name = "rom_e2e_shutdown_watchdog",
    tags = ["manual"],
    tests = [
        "shutdown_watchdog_{}_{}".format(
            t["lc_state"],
            t["bite_threshold"],
        )
        for t in SHUTDOWN_WATCHDOG_CASES
    ],
)

SIGVERIFY_LC_KEYS = [
    "fake_test_key_0",
    "fake_dev_key_0",
    "fake_prod_key_0",
]

[
    genrule(
        name = "empty_test_slot_{}_corrupted_{}_bin_signed_{}".format(slot, device, key),
        testonly = True,
        srcs = ["empty_test_slot_{}_{}_bin_signed_{}".format(slot, device, key)],
        outs = ["empty_test_slot_{}_corrupted_{}.{}.signed.bin".format(slot, device, key)],
        cmd_bash = "cat $(SRCS) > $(OUTS) && dd if=/dev/zero of=$(OUTS) bs=4 seek=7 count=1 conv=notrunc status=none".format(slot),
    )
    for slot in SLOTS
    for device in [
        "sim_dv",
        "fpga_cw310",
    ]
    for key in SIGVERIFY_LC_KEYS
]

# The below three rule sets (bin_to_vmem, scramble_flash_vmem, and filegroup)
# are needed to run `sigverify_always` test in DV.
[
    bin_to_vmem(
        name = "empty_test_slot_{}_corrupted_sim_dv_vmem64_signed_{}".format(slot, key),
        testonly = True,
        bin = "empty_test_slot_{}_corrupted_sim_dv_bin_signed_{}".format(slot, key),
        word_size = 64,  # Backdoor-load VMEM image uses 64-bit words
    )
    for slot in SLOTS
    for key in SIGVERIFY_LC_KEYS
]

[
    scramble_flash_vmem(
        name = "empty_test_slot_{}_corrupted_sim_dv_scr_vmem64_signed_{}".format(slot, key),
        testonly = True,
        vmem = "empty_test_slot_{}_corrupted_sim_dv_vmem64_signed_{}".format(slot, key),
    )
    for slot in SLOTS
    for key in SIGVERIFY_LC_KEYS
]

[
    filegroup(
        name = "empty_test_slot_{}_corrupted_sim_dv".format(slot),
        testonly = True,
        srcs = [
            "empty_test_slot_{}_corrupted_sim_dv_{}_signed_{}".format(slot, file_type, key)
            for file_type in [
                "bin",
                "vmem64",
                "scr_vmem64",
            ]
            for key in SIGVERIFY_LC_KEYS
        ],
    )
    for slot in SLOTS
]

BOOT_POLICY_VALID_CASES = [
    {
        "desc": "good",
        "suffix": "",
    },
    {
        "desc": "bad",
        "suffix": "_corrupted",
    },
]

[
    opentitan_multislot_flash_binary(
        name = "boot_policy_valid_img_a_{}_b_{}".format(
            a["desc"],
            b["desc"],
        ),
        srcs = {
            ":empty_test_slot_a{}".format(a["suffix"]): {
                "key": "fake_prod_key_0",
                "offset": SLOTS["a"],
            },
            ":empty_test_slot_b{}".format(b["suffix"]): {
                "key": "fake_prod_key_0",
                "offset": SLOTS["b"],
            },
        },
        devices = ["fpga_cw310"],
    )
    for a in BOOT_POLICY_VALID_CASES
    for b in BOOT_POLICY_VALID_CASES
]

[
    otp_image(
        name = "otp_img_boot_policy_valid_{}".format(lc_state.lower()),
        src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state.lower()),
        overlays = STD_OTP_OVERLAYS,
    )
    for lc_state in structs.to_dict(CONST.LCV)
]

# Splice OTP images into bitstreams
[
    bitstream_splice(
        name = "bitstream_boot_policy_valid_{}".format(lc_state.lower()),
        src = "//hw/bitstream:rom",
        data = ":otp_img_boot_policy_valid_{}".format(lc_state.lower()),
        meminfo = "//hw/bitstream:otp_mmi",
        tags = ["vivado"],
        update_usr_access = True,
    )
    for lc_state in structs.to_dict(CONST.LCV)
]

[
    opentitan_functest(
        name = "boot_policy_valid_{}_a_{}_b_{}".format(
            lc_state,
            a["desc"],
            b["desc"],
        ),
        cw310 = cw310_params(
            bitstream = "bitstream_boot_policy_valid_{}".format(lc_state),
            exit_failure = MSG_PASS if a["desc"] == b["desc"] and a["desc"] == "bad" else DEFAULT_TEST_FAILURE_MSG,
            exit_success = MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.SIGVERIFY.BAD_ENCODED_MSG)) if a["desc"] == b["desc"] and a["desc"] == "bad" else MSG_PASS,
            tags = ["vivado"] + maybe_skip_in_ci(lc_state_val),
        ),
        key = "multislot",
        ot_flash_binary = ":boot_policy_valid_img_a_{}_b_{}".format(
            a["desc"],
            b["desc"],
        ),
        targets = ["cw310_rom"],
    )
    for lc_state, lc_state_val in get_lc_items()
    for a in BOOT_POLICY_VALID_CASES
    for b in BOOT_POLICY_VALID_CASES
]

test_suite(
    name = "rom_e2e_boot_policy_valid",
    tags = ["manual"],
    tests = [
        "boot_policy_valid_{}_a_{}_b_{}".format(
            lc_state,
            a["desc"],
            b["desc"],
        )
        for lc_state, _ in get_lc_items()
        for a in BOOT_POLICY_VALID_CASES
        for b in BOOT_POLICY_VALID_CASES
    ],
)

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
        name = "rom_otp_{}_exec_disabled".format(lc_state),
        src = "//hw/bitstream:rom",
        data = "img_{}_exec_disabled".format(lc_state),
        meminfo = "//hw/bitstream:otp_mmi",
        tags = [
            "manual",
            "vivado",
        ],
        update_usr_access = True,
        visibility = ["//visibility:private"],
    )
    for lc_state, _ in get_lc_items()
]

SRAM_JTAG_INJECTION_GDB_SCRIPT = """
        target extended-remote :3333

        echo :::: Send OpenOCD the 'reset halt' command.\\n
        monitor reset halt


        # Mitigate flakiness from the watchdog timer. Prior to connecting
        # OpenOCD and GDB, the device is executing normally. The ROM has
        # probably already started up and configured the watchdog timer. This is
        # a problem; if the timer fires while we're connected, the interrupt
        # will steal control away from the debugger and cause this test to fail.
        # Thus, we need to disable the watchdog timer as quickly as possible to
        # minimize the chances of it firing.
        #
        # The proper solution would be to disable ROM execution by provisioning
        # with an OTP image that has CREATOR_SW_CFG_ROM_EXEC_EN set to zero.
        #
        # Initialize and disable the watchdog timer per aon_timer docs [1]. The
        # hardcoded addresses were computed by adding REG_OFFSET values from
        # //hw/ip/aon_timer/data:aon_timer_regs to the base address
        # TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR.
        #
        # [1]: https://docs.opentitan.org/hw/ip/aon_timer/doc/#initialization

        echo :::: Disable the watchdog timer.\\n
        monitor mdw 0x40470014
        monitor mww 0x40470014 0
        echo :::: Reset WDOG_COUNT.\\n
        monitor mdw 0x40470020
        monitor mww 0x40470020 0
        echo :::: Clear the interrupt (if any) by writing to INTR_STATE.\\n
        monitor mdw 0x40470024
        monitor mww 0x40470024 0


        # Before transferring the SRAM program to the device, we must configure
        # the PMP unit to enable writing to and executing from SRAM. Due to
        # implementation details of OpenTitan's hardware debug module, we cannot
        # set pmpcfg* registers to arbitrary values [1]. However, we can safely
        # modify unused PMP configuration registers. Thankfully, pmp0cfg (the
        # lowest byte of CSR pmpcfg0) is unused and has the highest priority.
        #
        # In more detail, the problem is that our debug module implements the
        # "Access Register" abstract command by assembling instructions in the
        # program buffer and then executing the buffer. If one of those
        # instructions clobbers the PMP configuration register that allows
        # execution from the program buffer, subsequent instruction fetches will
        # generate exceptions.
        #
        # Debug module concepts like abstract commands and the program buffer
        # buffer are defined in "RISC-V External Debug Support Version 0.13.2"
        # [2]. OpenTitan's (vendored-in) implementation lives in
        # //hw/vendor/pulp_riscv_dbg.
        #
        # [1]: https://github.com/lowRISC/opentitan/issues/14978
        # [2]: https://riscv.org/wp-content/uploads/2019/03/riscv-debug-release.pdf

        echo :::: Configure the PMP unit.\\n
        monitor reg pmpcfg0
        # Write "L NAPOT X W R" to pmp{0,1,2,3}cfg in pmpcfg0. Crucially, this
        # value is no less permissive than whatever the current value is.
        monitor reg pmpcfg0 0x9f9f9f9f
        monitor reg pmpaddr0 0xffffffff

        echo :::: Value of CREATOR_SW_CFG_ROM_EXEC_EN.\\n
        monitor mdw 0x40131108

        echo :::: Load the SRAM program onto the device and check integrity.\\n
        file sram_program.elf
        load sram_program.elf
        compare-sections

        echo :::: Update registers before calling functions.\\n
        set $sp = _stack_end
        set $gp = __global_pointer$
        info registers

        # When testing SRAM execution, we want to be sure the code is running
        # out of SRAM and not the instruction cache.
        echo :::: Invalidate the icache.\\n
        print icache_invalidate()

        echo :::: Call sram_main().\\n
        print sram_main()

        echo :::: Done.\\n
"""

[
    opentitan_gdb_fpga_cw310_test(
        name = "sram_program_fpga_cw310_test_otp_" + lc_state,
        timeout = "short",
        exit_success_pattern = "sram_program\\.c:\\d+\\] PC: 0x1000[0-2][0-9a-f]{3}, SRAM: \\[0x10000000, 0x10020000\\)",
        gdb_script = SRAM_JTAG_INJECTION_GDB_SCRIPT,
        gdb_script_symlinks = {
            "//sw/device/examples/sram_program:sram_program_fpga_cw310.elf": "sram_program.elf",
        },
        rom_bitstream = ":rom_otp_{}_exec_disabled".format(lc_state),
        rom_kind = "Rom",
        tags = [
            "cw310_rom",
            "vivado",
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

[
    opentitan_functest(
        name = "epmp_init_otp_" + lc_state,
        srcs = ["epmp_init_test.c"],
        cw310 = cw310_params(
            bitstream = "//hw/bitstream:rom_otp_" + lc_state,
            tags = ["vivado"] + maybe_skip_in_ci(lc_state_val),
        ),
        key = LC_KEY_TYPES[lc_state_val][0],
        local_defines = [
            "EXPECT_DEBUG={}".format(1 if lc_state_val in [
                CONST.LCV.TEST_UNLOCKED0,
                CONST.LCV.DEV,
                CONST.LCV.RMA,
            ] else 0),
        ],
        targets = [
            "cw310_rom",
            "verilator",
        ],
        verilator = verilator_params(
            timeout = "eternal",
            otp = "//hw/ip/otp_ctrl/data:img_" + lc_state,
            rom = "//sw/device/silicon_creator/rom:rom_with_fake_keys",
        ),
        deps = [
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/base:csr",
            "//sw/device/lib/dif:lc_ctrl",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing:lc_ctrl_testutils",
            "//sw/device/lib/testing/test_framework:check",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/lib/testing/test_framework:status",
            "//sw/device/silicon_creator/lib:epmp_defs",
        ],
    )
    for lc_state, lc_state_val in get_lc_items()
]

test_suite(
    name = "rom_e2e_epmp_init",
    tags = ["manual"],
    tests = ["epmp_init_otp_" + lc_state for lc_state, _ in get_lc_items()],
)

[
    opentitan_gdb_fpga_cw310_test(
        name = "debug_disallowed_in_prod_fpga_cw310_test_otp_" + lc_state,
        timeout = "short",
        expect_debug_disallowed = lc_state_val in [
            CONST.LCV.PROD,
            CONST.LCV.PROD_END,
        ],
        gdb_script = """
            target extended-remote :3333

            echo :::: Send OpenOCD the 'reset halt' command.\\n
            monitor reset halt

            echo :::: Load ROM symbols into GDB.\\n
            file rom.elf

            print $pc
        """,
        gdb_script_symlinks = {
            "//sw/device/silicon_creator/rom:rom_with_fake_keys_fpga_cw310.elf": "rom.elf",
        },
        rom_bitstream = ":rom_otp_{}_exec_disabled".format(lc_state),
        rom_kind = "Rom",
        tags = [
            "cw310_rom",
            "vivado",
        ] + maybe_skip_in_ci(lc_state_val),
    )
    for lc_state, lc_state_val in get_lc_items(
        CONST.LCV.PROD,
        CONST.LCV.PROD_END,
        CONST.LCV.RMA,
    )
]

test_suite(
    name = "rom_e2e_debug_disallowed_in_prod_tests",
    tags = ["manual"],
    tests = [
        "debug_disallowed_in_prod_fpga_cw310_test_otp_" + lc_state
        for lc_state, _ in get_lc_items(
            CONST.LCV.PROD,
            CONST.LCV.PROD_END,
            CONST.LCV.RMA,
        )
    ],
)

[
    opentitan_gdb_fpga_cw310_test(
        name = "asm_interrupt_handler_fpga_cw310_test_otp_" + lc_state,
        timeout = "short",
        gdb_script = """
            target extended-remote :3333

            echo :::: Send OpenOCD the 'reset halt' command.\\n
            monitor reset halt

            echo :::: Load ROM symbols into GDB.\\n
            file rom.elf

            echo :::: Set breakpoint on exception handler.\\n
            break _asm_exception_handler

            echo :::: Attempt to trigger an exception.\\n
            set $pc = 0
            continue
            printf ":::: PC=%p. Expected PC=%p.\\n", $pc, _asm_exception_handler

            if $pc == _asm_exception_handler
                echo :::: Test passed!\\n
                quit 0
            else
                echo :::: Test failed!\\n
                quit 1
            end
        """,
        gdb_script_symlinks = {
            "//sw/device/silicon_creator/rom:rom_with_fake_keys_fpga_cw310.elf": "rom.elf",
        },
        rom_bitstream = ":rom_otp_{}_exec_disabled".format(lc_state),
        rom_kind = "Rom",
        tags = [
            "cw310_rom",
            "vivado",
        ] + maybe_skip_in_ci(lc_state_val),
    )
    for lc_state, lc_state_val in get_lc_items(
        CONST.LCV.TEST_UNLOCKED0,
        CONST.LCV.DEV,
        CONST.LCV.RMA,
    )
]

test_suite(
    name = "rom_e2e_asm_interrupt_handler",
    tags = ["manual"],
    tests = [
        "asm_interrupt_handler_fpga_cw310_test_otp_" + lc_state
        for lc_state, _ in get_lc_items(
            CONST.LCV.TEST_UNLOCKED0,
            CONST.LCV.DEV,
            CONST.LCV.RMA,
        )
    ],
)

[
    opentitan_gdb_fpga_cw310_test(
        name = "shutdown_exception_asm_otp_" + lc_state,
        timeout = "short",
        gdb_expect_output_sequence = [
            ":::: About to reset.",
            "unable to resume hart 0",
        ],
        gdb_script = """
            target extended-remote :3333

            echo :::: Send OpenOCD the 'reset halt' command.\\n
            monitor reset halt

            echo :::: Load ROM symbols into GDB.\\n
            file rom.elf

            echo :::: Set breakpoint on exception handler.\\n
            break _asm_exception_handler

            echo :::: Set PC to start of main SRAM.\\n
            set $pc = 0x10000000
            continue
            printf ":::: PC=%p. Expected PC=%p.\\n", $pc, _asm_exception_handler
            if $pc != _asm_exception_handler
                quit 1
            end

            echo :::: About to reset.\\n
            continue

            # Not reached.
            quit 123
        """,
        gdb_script_symlinks = {
            "//sw/device/silicon_creator/rom:rom_with_fake_keys_fpga_cw310.elf": "rom.elf",
        },
        rom_bitstream = ":rom_otp_{}_exec_disabled".format(lc_state),
        rom_kind = "Rom",
        tags = [
            "cw310_rom",
            "vivado",
        ] + maybe_skip_in_ci(lc_state_val),
    )
    for lc_state, lc_state_val in get_lc_items(
        CONST.LCV.TEST_UNLOCKED0,
        CONST.LCV.DEV,
        CONST.LCV.RMA,
    )
]

test_suite(
    name = "rom_e2e_shutdown_exception_asm",
    tags = ["manual"],
    tests = [
        "shutdown_exception_asm_otp_" + lc_state
        for lc_state, _ in get_lc_items(
            CONST.LCV.TEST_UNLOCKED0,
            CONST.LCV.DEV,
            CONST.LCV.RMA,
        )
    ],
)

# Ensure that the watchdog restarts the ROM even when the bite threshold has
# been artificially inflated.
[
    opentitan_gdb_fpga_cw310_test(
        name = "rom_e2e_asm_watchdog_bark_fpga_cw310_test_otp_" + lc_state,
        timeout = "short",
        gdb_script = """
            target extended-remote :3333

            echo :::: Send OpenOCD the 'reset halt' command.\\n
            monitor reset halt

            echo :::: Load ROM symbols into GDB.\\n
            file rom.elf

            echo :::: Run until we check whether ROM execution is enabled.\\n
            break kRomStartBootMaybeHalt
            continue

            printf ":::: PC=%p. Expected PC=%p.\\n", $pc, kRomStartBootMaybeHalt
            if $pc != kRomStartBootMaybeHalt
                quit 42
            end

            echo :::: Pretend execution is enabled.\\n
            set $pc = kRomStartBootExecEn

            break kRomStartStoreT1ToBiteThold
            continue
            printf ":::: PC=%p. Expected PC=%p.\\n", $pc, kRomStartStoreT1ToBiteThold
            if $pc != kRomStartStoreT1ToBiteThold
                quit 43
            end

            # Set the bite threshold to UINT32_MAX. We want to exercise that the
            # bark causes control to reach the interrupt handler.
            set $t1 = 0xffffffff

            echo :::: Run until right after configuring the watchdog timer.\\n
            break kRomStartWatchdogEnabled
            continue

            printf ":::: PC=%p. Expected PC=%p.\\n", $pc, kRomStartWatchdogEnabled
            if $pc != kRomStartWatchdogEnabled
                quit 44
            end

            echo :::: Set breakpoint on NMI handler.\\n
            delete breakpoints
            break _asm_exception_handler

            echo :::: Wait for interrupt.\\n
            set $pc = kRomStartBootMaybeHalt
            echo :::: Continue.\\n
            continue

            printf ":::: PC=%p. Expected PC=%p.\\n", $pc, _asm_exception_handler
            if $pc != _asm_exception_handler
                quit 45
            end
        """,
        gdb_script_symlinks = {
            "//sw/device/silicon_creator/rom:rom_with_fake_keys_fpga_cw310.elf": "rom.elf",
        },
        rom_bitstream = ":rom_otp_{}_exec_disabled".format(lc_state),
        rom_kind = "Rom",
        tags = [
            "cw310_rom",
            "vivado",
        ] + maybe_skip_in_ci(lc_state_val),
    )
    for lc_state, lc_state_val in get_lc_items(
        CONST.LCV.TEST_UNLOCKED0,
        CONST.LCV.DEV,
        CONST.LCV.RMA,
    )
]

# Ensure that the watchdog's bite restarts the ROM.
[
    opentitan_gdb_fpga_cw310_test(
        name = "rom_e2e_asm_watchdog_bite_fpga_cw310_test_otp_" + lc_state,
        timeout = "short",
        gdb_expect_output_sequence = [
            ":::: Wait for interrupt.",
            "Hart 0 unexpectedly reset!",
        ],
        gdb_script = """
            target extended-remote :3333

            echo :::: Send OpenOCD the 'reset halt' command.\\n
            monitor reset halt

            echo :::: Load ROM symbols into GDB.\\n
            file rom.elf

            echo :::: Run until we check whether ROM execution is enabled.\\n
            break kRomStartBootMaybeHalt
            continue

            printf ":::: PC=%p. Expected PC=%p.\\n", $pc, kRomStartBootMaybeHalt
            if $pc != kRomStartBootMaybeHalt
                quit 42
            end

            echo :::: Pretend execution is enabled.\\n
            set $pc = kRomStartBootExecEn

            echo :::: Run until right after configuring the watchdog timer.\\n
            break kRomStartWatchdogEnabled
            continue

            printf ":::: PC=%p. Expected PC=%p.\\n", $pc, kRomStartWatchdogEnabled
            if $pc != kRomStartWatchdogEnabled
                quit 43
            end

            echo :::: Set breakpoint on NMI handler.\\n
            delete breakpoints
            break _asm_exception_handler

            echo :::: Wait for interrupt.\\n
            set $pc = kRomStartBootMaybeHalt
            echo :::: Continue.\\n
            continue

            # Not reached.
            quit 123
        """,
        gdb_script_symlinks = {
            "//sw/device/silicon_creator/rom:rom_with_fake_keys_fpga_cw310.elf": "rom.elf",
        },
        rom_bitstream = ":rom_otp_{}_exec_disabled".format(lc_state),
        rom_kind = "Rom",
        tags = [
            "cw310_rom",
            "vivado",
        ] + maybe_skip_in_ci(lc_state_val),
    )
    for lc_state, lc_state_val in get_lc_items(
        CONST.LCV.TEST_UNLOCKED0,
        CONST.LCV.DEV,
        CONST.LCV.RMA,
    )
]

test_suite(
    name = "rom_e2e_asm_watchdog",
    tags = ["manual"],
    tests = [
        "rom_e2e_asm_watchdog_" + type + "_fpga_cw310_test_otp_" + lc_state
        for lc_state, lc_state_val in get_lc_items(
            CONST.LCV.TEST_UNLOCKED0,
            CONST.LCV.DEV,
            CONST.LCV.RMA,
        )
        for type in ("bite", "bark")
    ],
)

# Shutdown Redact Test

# Dict that also includes an invalid redaction value for test purposes.
REDACT = structs.to_dict(CONST.SHUTDOWN.REDACT)

REDACT.update({"INVALID": 0x0})

[
    otp_json(
        name = "otp_json_{}_overlay".format(k.lower()),
        partitions = [
            otp_partition(
                name = "OWNER_SW_CFG",
                items = {
                    "OWNER_SW_CFG_ROM_ERROR_REPORTING": hex(v),
                },
            ),
        ],
    )
    for k, v in REDACT.items()
]

[
    otp_image(
        name = "img_{}_{}".format(
            lc_state,
            redact.lower(),
        ),
        src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
        overlays = STD_OTP_OVERLAYS + [":otp_json_{}_overlay".format(redact.lower())],
        visibility = ["//visibility:private"],
    )
    for lc_state, _ in get_lc_items()
    for redact in REDACT
]

[
    bitstream_splice(
        name = "bitstream_{}_{}".format(
            lc_state,
            redact.lower(),
        ),
        src = "//hw/bitstream:rom",
        data = ":img_{}_{}".format(
            lc_state,
            redact.lower(),
        ),
        meminfo = "//hw/bitstream:otp_mmi",
        tags = ["vivado"],
        update_usr_access = True,
        visibility = ["//visibility:private"],
    )
    for lc_state, _ in get_lc_items()
    for redact in REDACT
]

[
    opentitan_functest(
        name = "e2e_shutdown_redact_{}_{}".format(
            lc_state,
            redact.lower(),
        ),
        srcs = ["empty_test.c"],
        cw310 = cw310_params(
            bitstream = "bitstream_{}_{}".format(
                lc_state,
                redact.lower(),
            ),
            exit_failure = MSG_PASS,
            exit_success = MSG_TEMPLATE_BFV.format(hex_digits(error_redact(
                CONST.BFV.BOOT_POLICY.BAD_IDENTIFIER,
                lc_state_val,
                redact_val,
            ))),
            tags = ["vivado"] + maybe_skip_in_ci(lc_state_val),
        ),
        signed = False,
        targets = ["cw310_rom"],
        deps = [
            "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib/drivers:lifecycle",
            "//sw/device/silicon_creator/lib/drivers:otp",
        ],
    )
    for lc_state, lc_state_val in get_lc_items()
    for redact, redact_val in REDACT.items()
]

test_suite(
    name = "rom_e2e_shutdown_redact",
    tags = ["manual"],
    tests = [
        "e2e_shutdown_redact_{}_{}".format(
            lc_state,
            redact.lower(),
        )
        for lc_state, _ in get_lc_items()
        for redact in REDACT
    ],
)

[
    opentitan_multislot_flash_binary(
        name = "sigverify_always_img_a_{}_b_{}_{}".format(
            "nothing" if slot == "b" else "bad",
            "nothing" if slot == "a" else "bad",
            key,
        ),
        srcs = {
            ":empty_test_slot_{}_corrupted".format(slot): {
                "key": key,
                "offset": offset,
            },
        },
        devices = [
            "sim_dv",
            "fpga_cw310",
        ],
    )
    for slot, offset in SLOTS.items()
    for key in SIGVERIFY_LC_KEYS
]

[
    opentitan_multislot_flash_binary(
        name = "sigverify_always_img_a_bad_b_bad_{}".format(key),
        srcs = {
            ":empty_test_slot_a_corrupted": {
                "key": key,
                "offset": SLOTS["a"],
            },
            ":empty_test_slot_b_corrupted": {
                "key": key,
                "offset": SLOTS["b"],
            },
        },
        devices = [
            "sim_dv",
            "fpga_cw310",
        ],
    )
    for key in SIGVERIFY_LC_KEYS
]

# Since we cannot feed the `assemble_flash_image` rule that is instantiated by
# the `opentitan_multislot_flash_binary` macro an empty dictionary, we create
# two images with "nothing" in them by created files of all ones, and stitching
# them together.
[
    genrule(
        name = "sigverify_always_img_{}_nothing_{}_bin_signed_{}".format(slot, device, key),
        outs = ["sigverify_always_img_{}_all_ones_{}_bin_signed_{}".format(slot, device, key)],
        cmd_bash = "touch $(OUTS)",
    )
    for slot in SLOTS
    for device in [
        "sim_dv",
        "fpga_cw310",
    ]
    for key in SIGVERIFY_LC_KEYS
]

[
    opentitan_multislot_flash_binary(
        name = "sigverify_always_img_a_nothing_b_nothing_{}".format(key),
        srcs = {
            ":sigverify_always_img_a_nothing": {
                "key": key,
                "offset": SLOTS["a"],
            },
            ":sigverify_always_img_b_nothing": {
                "key": key,
                "offset": SLOTS["b"],
            },
        },
        devices = [
            "sim_dv",
            "fpga_cw310",
        ],
    )
    for key in [
        "fake_test_key_0",
        "fake_dev_key_0",
        "fake_prod_key_0",
    ]
]

[otp_image(
    name = "otp_img_sigverify_always_{}".format(lc_state),
    src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
    overlays = STD_OTP_OVERLAYS,
) for lc_state, _ in get_lc_items()]

# Splice OTP images into bitstreams
[
    bitstream_splice(
        name = "bitstream_sigverify_always_{}".format(lc_state),
        src = "//hw/bitstream:rom",
        data = ":otp_img_sigverify_always_{}".format(lc_state),
        meminfo = "//hw/bitstream:otp_mmi",
        tags = ["vivado"] + maybe_skip_in_ci(lc_state_val),
        update_usr_access = True,
    )
    for lc_state, lc_state_val in get_lc_items()
]

SIGVERIFY_BAD_CASES = [
    {
        "a": "nothing",
        "b": "bad",
        "expected_bfv": hex_digits(CONST.BFV.SIGVERIFY.BAD_ENCODED_MSG),
    },
    {
        "a": "bad",
        "b": "nothing",
        "expected_bfv": hex_digits(CONST.BFV.SIGVERIFY.BAD_ENCODED_MSG),
    },
    {
        "a": "bad",
        "b": "bad",
        "expected_bfv": hex_digits(CONST.BFV.SIGVERIFY.BAD_ENCODED_MSG),
    },
    {
        "a": "nothing",
        "b": "nothing",
        "expected_bfv": hex_digits(CONST.BFV.BOOT_POLICY.BAD_IDENTIFIER),
    },
]

SIGVERIFY_LCS_2_VALID_KEY = {
    "test_unlocked0": "fake_test_key_0",
    "dev": "fake_dev_key_0",
    "prod": "fake_prod_key_0",
    "prod_end": "fake_prod_key_0",
    "rma": "fake_prod_key_0",
}

[
    opentitan_functest(
        name = "sigverify_always_{}_a_{}_b_{}".format(
            lc_state,
            case["a"],
            case["b"],
        ),
        cw310 = cw310_params(
            bitstream = ":bitstream_sigverify_always_{}".format(lc_state),
            exit_failure = MSG_PASS,
            exit_success = MSG_TEMPLATE_BFV_LCV.format(
                case["expected_bfv"],
                hex_digits(lc_state_val),
            ),
            otp = ":otp_img_sigverify_always_{}".format(lc_state),
            tags = ["vivado"] + maybe_skip_in_ci(lc_state_val),
        ),
        dv = dv_params(
            otp = ":otp_img_sigverify_always_{}".format(lc_state),
            rom = "//sw/device/silicon_creator/rom:rom_with_fake_keys",
        ),
        key = "multislot",
        ot_flash_binary = ":sigverify_always_img_a_{}_b_{}_{}".format(
            case["a"],
            case["b"],
            SIGVERIFY_LCS_2_VALID_KEY[lc_state],
        ),
        targets = [
            "dv",
            "cw310_rom",
        ],
    )
    for case in SIGVERIFY_BAD_CASES
    for lc_state, lc_state_val in get_lc_items()
]

test_suite(
    name = "sigverify_always",
    tags = ["manual"],
    tests = [
        "sigverify_always_{}_a_{}_b_{}".format(
            lc_state,
            case["a"],
            case["b"],
        )
        for case in SIGVERIFY_BAD_CASES
        for lc_state, _ in get_lc_items()
    ],
)

[
    otp_image(
        name = "otp_img_sigverify_key_type_{}".format(lc_state),
        src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
        overlays = STD_OTP_OVERLAYS,
    )
    for lc_state, _ in get_lc_items()
]

[
    bitstream_splice(
        name = "bitstream_sigverify_key_type_{}".format(
            lc_state,
        ),
        src = "//hw/bitstream:rom",
        data = ":otp_img_sigverify_key_type_{}".format(
            lc_state,
        ),
        meminfo = "//hw/bitstream:otp_mmi",
        tags = ["vivado"] + maybe_skip_in_ci(lc_state_val),
        update_usr_access = True,
        visibility = ["//visibility:private"],
    )
    for lc_state, lc_state_val in get_lc_items()
]

SIGVERIFY_KEY_TYPE_KEYS = [
    "fake_test_key_0",
    "fake_dev_key_0",
    "fake_prod_key_0",
]

[
    opentitan_functest(
        name = "sigverify_key_type_{}_{}".format(
            lc_state,
            key,
        ),
        cw310 = cw310_params(
            bitstream = ":bitstream_sigverify_key_type_{}".format(lc_state),
            exit_failure = MSG_PASS if key not in LC_KEY_TYPES[lc_state_val] else MSG_TEMPLATE_BFV_LCV.format(
                hex_digits(CONST.BFV.SIGVERIFY.BAD_KEY),
                hex_digits(lc_state_val),
            ),
            exit_success = MSG_PASS if key in LC_KEY_TYPES[lc_state_val] else MSG_TEMPLATE_BFV_LCV.format(
                hex_digits(CONST.BFV.SIGVERIFY.BAD_KEY),
                hex_digits(lc_state_val),
            ),
            tags = ["vivado"] + maybe_skip_in_ci(lc_state_val),
        ),
        key = key,
        ot_flash_binary = "empty_test_slot_a",
        targets = [
            "cw310_rom",
        ],
    )
    for lc_state, lc_state_val in get_lc_items()
    for key in SIGVERIFY_KEY_TYPE_KEYS
]

test_suite(
    name = "rom_e2e_sigverify_key_type",
    tags = ["manual"],
    tests = [
        "sigverify_key_type_{}_{}".format(
            lc_state,
            key,
        )
        for lc_state, _ in get_lc_items()
        for key in SIGVERIFY_KEY_TYPE_KEYS
    ],
)

otp_json(
    name = "otp_json_sigverify_key_validity",
    partitions = [
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {
                "CREATOR_SW_CFG_SIGVERIFY_RSA_KEY_EN": "0x4b4b4b4b4bff004b",
            },
        ),
    ],
)

[
    otp_image(
        name = "otp_img_sigverify_key_validity_{}".format(lc_state),
        src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
        overlays = STD_OTP_OVERLAYS + [":otp_json_sigverify_key_validity"],
    )
    for lc_state, _ in get_lc_items()
]

[
    bitstream_splice(
        name = "bitstream_sigverify_key_validity_{}".format(
            lc_state,
        ),
        src = "//hw/bitstream:rom",
        data = ":otp_img_sigverify_key_validity_{}".format(
            lc_state,
        ),
        meminfo = "//hw/bitstream:otp_mmi",
        tags = ["vivado"] + maybe_skip_in_ci(lc_state_val),
        update_usr_access = True,
        visibility = ["//visibility:private"],
    )
    for lc_state, lc_state_val in get_lc_items()
]

[
    opentitan_functest(
        name = "sigverify_key_validity_{}_{}".format(
            lc_state,
            key,
        ),
        cw310 = cw310_params(
            bitstream = ":bitstream_sigverify_key_validity_{}".format(lc_state),
            exit_failure = MSG_PASS if lc_state_val != CONST.LCV.TEST_UNLOCKED0 else MSG_TEMPLATE_BFV_LCV.format(
                hex_digits(CONST.BFV.SIGVERIFY.BAD_KEY),
                hex_digits(lc_state_val),
            ),
            exit_success = MSG_TEMPLATE_BFV_LCV.format(
                hex_digits(CONST.BFV.SIGVERIFY.BAD_KEY),
                hex_digits(lc_state_val),
            ) if lc_state_val != CONST.LCV.TEST_UNLOCKED0 else MSG_PASS,
            tags = ["vivado"] + maybe_skip_in_ci(lc_state_val),
        ),
        key = key,
        ot_flash_binary = "empty_test_slot_a",
        targets = [
            "cw310_rom",
        ],
    )
    for lc_state, lc_state_val in get_lc_items()
    for key in LC_KEY_TYPES[lc_state_val]
]

test_suite(
    name = "rom_e2e_sigverify_key_validity",
    tags = ["manual"],
    tests = [
        "sigverify_key_validity_{}_{}".format(
            lc_state,
            key,
        )
        for lc_state, lc_state_val in get_lc_items()
        for key in LC_KEY_TYPES[lc_state_val]
    ],
)

# Sigverify usage constraint tests
_test_device_id = [
    "0xa0a1a2a3",  # Least-significant word
    "0x12345678",
    "0x00000003",
    "0xabababab",
    "0xcdcdcdcd",
    "0x01010101",
    "0x10101010",
    "0xf0f1f2f3",  # Most-significant word
]

_test_manuf_states = {
    "creator": "0xfedcba98",
    "owner": "0x12345678",
}

# Generate OTP image with a specific device ID, creator manufacturing state,
# and owner manufacturing state
_test_device_id_joined = "0x" + "".join([word[2:] for word in reversed(_test_device_id)])

otp_json(
    name = "otp_json_set_usage_constraint_params_overlay",
    partitions = [
        otp_partition(
            name = "HW_CFG",
            items = {"DEVICE_ID": _test_device_id_joined},
        ),
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {"CREATOR_SW_CFG_MANUF_STATE": _test_manuf_states["creator"]},
        ),
        otp_partition(
            name = "OWNER_SW_CFG",
            items = {"OWNER_SW_CFG_MANUF_STATE": _test_manuf_states["owner"]},
        ),
    ],
    visibility = ["//visibility:private"],
)

[otp_image(
    name = "otp_img_sigverify_usage_constraints_{}".format(lc_state),
    src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
    overlays = STD_OTP_OVERLAYS + [":otp_json_set_usage_constraint_params_overlay"],
    visibility = ["//visibility:private"],
) for lc_state, _ in get_lc_items()]

[bitstream_splice(
    name = "bitstream_sigverify_usage_constraints_{}".format(lc_state),
    src = "//hw/bitstream:rom",
    data = ":otp_img_sigverify_usage_constraints_{}".format(lc_state),
    meminfo = "//hw/bitstream:otp_mmi",
    tags = ["vivado"] + maybe_skip_in_ci(lc_state_val),
    update_usr_access = True,
    visibility = ["//visibility:private"],
) for lc_state, lc_state_val in get_lc_items()]

_SIGVERIFY_FAIL_MSG = MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.SIGVERIFY.BAD_ENCODED_MSG))

device_id_test_cases = [
    {
        "name": "device_id_match",
        "manifest": {
            "selector_bits": "0xff",
            "device_id": _test_device_id,
        },
        "bitstream": ":bitstream_sigverify_usage_constraints_rma",
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": _SIGVERIFY_FAIL_MSG,
        "lc_state_val": CONST.LCV.RMA,
    },
    {
        "name": "device_id_no_match",
        "manifest": {
            "selector_bits": "0xff",
            "device_id": ["0xbad"] * 8,
        },
        "bitstream": ":bitstream_sigverify_usage_constraints_rma",
        "exit_success": _SIGVERIFY_FAIL_MSG,
        "exit_failure": DEFAULT_TEST_SUCCESS_MSG,
        "lc_state_val": CONST.LCV.RMA,
    },
    {
        "name": "device_id_family_match",
        "manifest": {
            # Select words 0, 3, and 5 to match on:
            # 0b0010_1001 = 0x29
            "selector_bits": "0x29",
            "device_id": [
                _test_device_id[0],
                hex(CONST.DEFAULT_USAGE_CONSTRAINTS),
                hex(CONST.DEFAULT_USAGE_CONSTRAINTS),
                _test_device_id[3],
                hex(CONST.DEFAULT_USAGE_CONSTRAINTS),
                _test_device_id[5],
                hex(CONST.DEFAULT_USAGE_CONSTRAINTS),
                hex(CONST.DEFAULT_USAGE_CONSTRAINTS),
            ],
        },
        "bitstream": ":bitstream_sigverify_usage_constraints_rma",
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": _SIGVERIFY_FAIL_MSG,
        "lc_state_val": CONST.LCV.RMA,
    },
    {
        "name": "device_id_family_no_match",
        "manifest": {
            # Select words 0, 3, and 5 to match on:
            # 0b0010_1001 = 0x29
            "selector_bits": "0x29",
            "device_id": [
                "0xbad",
                hex(CONST.DEFAULT_USAGE_CONSTRAINTS),
                hex(CONST.DEFAULT_USAGE_CONSTRAINTS),
                "0xbad",
                hex(CONST.DEFAULT_USAGE_CONSTRAINTS),
                "0xbad",
                hex(CONST.DEFAULT_USAGE_CONSTRAINTS),
                hex(CONST.DEFAULT_USAGE_CONSTRAINTS),
            ],
        },
        "bitstream": ":bitstream_sigverify_usage_constraints_rma",
        "exit_success": _SIGVERIFY_FAIL_MSG,
        "exit_failure": DEFAULT_TEST_SUCCESS_MSG,
        "lc_state_val": CONST.LCV.RMA,
    },
]

lc_state_test_cases = [
    {
        "name": "lc_state_{}_{}".format(
            lc_state,
            "match" if match_case else "no_match",
        ),
        # Note: the manifest value for a given life-cycle state is determined
        # by CONST.LCV_SW instead of CONST.LCV. These two structs have slightly
        # different mappings for the TEST_* LC state, so lc_hw_to_sw is used to
        # convert from the names in CONST.LCV to those in CONST.LCV_SW before
        # performing the lookup.
        "manifest": {
            "selector_bits": "0x400",
            "life_cycle_state": hex(lcv_hw_to_sw(lc_state_val)) if match_case else "0",
        },
        "bitstream": ":bitstream_sigverify_usage_constraints_{}".format(lc_state),
        "exit_success": DEFAULT_TEST_SUCCESS_MSG if match_case else _SIGVERIFY_FAIL_MSG,
        "exit_failure": _SIGVERIFY_FAIL_MSG if match_case else DEFAULT_TEST_SUCCESS_MSG,
        "lc_state_val": lc_state_val,
    }
    for lc_state, lc_state_val in get_lc_items()
    for match_case in (True, False)
]

manuf_state_test_cases = [
    {
        "name": "manuf_state_{}_{}".format(
            entity,
            "match" if match_case else "no_match",
        ),
        "manifest": {
            "selector_bits": "0x100" if entity == "creator" else "0x200",
            "manuf_state_{}".format(entity): "{}".format(_test_manuf_states[entity]) if match_case else "0",
        },
        "bitstream": ":bitstream_sigverify_usage_constraints_rma",
        "exit_success": DEFAULT_TEST_SUCCESS_MSG if match_case else _SIGVERIFY_FAIL_MSG,
        "exit_failure": _SIGVERIFY_FAIL_MSG if match_case else DEFAULT_TEST_SUCCESS_MSG,
        "lc_state_val": CONST.LCV.RMA,
    }
    for entity in ("creator", "owner")
    for match_case in (True, False)
]

# The all-constraints case is tested against all LC states. For each LC state,
# we try all 5 LC state settings in the manifest and ensure that only one
# boots successfully.
all_constr_test_cases = [
    {
        "name": "all_constraints_mf_lc_{}_bs_lc_{}".format(
            mf_lc_state.lower(),
            bs_lc_state,
        ),
        "manifest": {
            "selector_bits": "0x7ff",
            "device_id": _test_device_id,
            "life_cycle_state": hex(mf_lc_val),
            "manuf_state_creator": _test_manuf_states["creator"],
            "manuf_state_owner": _test_manuf_states["owner"],
        },
        "bitstream": ":bitstream_sigverify_usage_constraints_{}".format(bs_lc_state),
        "exit_success": DEFAULT_TEST_SUCCESS_MSG if mf_lc_val == lcv_hw_to_sw(bs_lc_val) else _SIGVERIFY_FAIL_MSG,
        "exit_failure": _SIGVERIFY_FAIL_MSG if mf_lc_val == lcv_hw_to_sw(bs_lc_val) else DEFAULT_TEST_SUCCESS_MSG,
        "lc_state_val": bs_lc_val,
    }
    for mf_lc_state, mf_lc_val in structs.to_dict(CONST.LCV_SW).items()
    for bs_lc_state, bs_lc_val in get_lc_items()
]

# Usage constraints that are not selected by the selector_bits must be set to
# MANIFEST_USAGE_CONSTRAINT_UNSELECTED_WORD. These tests check for a failure if
# they are not by setting various fields to otherwise valid values while
# setting the selector_bits to 0.
invalid_unselected_word_cases = [
    {
        "name": "invalid_unselected_{}".format(field),
        "manifest": {
            field: field_val,
            "selector_bits": "0",
            "selector_mismatch_is_failure": False,
        },
        "bitstream": ":bitstream_sigverify_usage_constraints_rma",
        "exit_success": _SIGVERIFY_FAIL_MSG,
        "exit_failure": DEFAULT_TEST_SUCCESS_MSG,
        "lc_state_val": CONST.LCV.RMA,
    }
    for field, field_val in [
        ("device_id", _test_device_id),
        (
            "life_cycle_state",
            hex(CONST.LCV_SW.RMA),
        ),
        (
            "manuf_state_creator",
            _test_manuf_states["creator"],
        ),
        (
            "manuf_state_owner",
            _test_manuf_states["owner"],
        ),
    ]
]

test_cases = device_id_test_cases + lc_state_test_cases + manuf_state_test_cases + all_constr_test_cases + invalid_unselected_word_cases

[opentitan_functest(
    name = "sigverify_usage_constraint_{}".format(t["name"]),
    srcs = ["empty_test.c"],
    cw310 = cw310_params(
        bitstream = t["bitstream"],
        exit_failure = t["exit_failure"],
        exit_success = t["exit_success"],
        tags = ["vivado"] + maybe_skip_in_ci(t["lc_state_val"]),
    ),
    manifest = manifest(
        dict(
            t["manifest"],
            name = "sigverify_usage_constraint_manifest_{}".format(t["name"]),
            address_translation = hex(CONST.FALSE),
            identifier = hex(CONST.ROM_EXT),
        ),
    ),
    signed = True,
    targets = ["cw310_rom"],
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:otp",
    ],
) for t in test_cases]

test_suite(
    name = "rom_e2e_sigverify_usage_constraints",
    tags = ["manual"],
    tests = ["sigverify_usage_constraint_{}".format(t["name"]) for t in test_cases],
)

[
    opentitan_gdb_fpga_cw310_test(
        name = "rom_e2e_debug_test_otp_" + lc_state,
        timeout = "short",
        exit_success_pattern = "OK!GDB-OK(?s:.*)BFV:0142500d",
        gdb_expect_output_sequence = [
            ":::: GDB script complete.",
            "Hart 0 unexpectedly reset!",
        ],
        gdb_script = """
            define assert_pc
                printf ":::: PC=%p. Expected PC=%p.\\n", $pc, $arg0
                if $pc != $arg0
                    quit 1
                end
            end

            target extended-remote :3333

            echo :::: Send OpenOCD the 'reset halt' command.\\n
            monitor reset halt

            echo :::: Load ROM symbols into GDB.\\n
            file rom.elf

            # Immediately after reset, we should be sitting on the Ibex reset
            # handler, the 33rd entry in the interrupt vector.
            set $ibex_reset_handler = _rom_interrupt_vector_asm + 32 * 4
            assert_pc $ibex_reset_handler

            # Executing the `j _rom_start_boot` instruction should take us
            # to _rom_start_boot.
            stepi
            assert_pc _rom_start_boot

            echo :::: Run until we check whether ROM execution is enabled.\\n
            break kRomStartBootMaybeHalt
            continue
            assert_pc kRomStartBootMaybeHalt

            # Use three of four hardware breakpoints. Leave one unused so we can
            # use `call` and `finish`. (See RvCoreIbexDbgHwBreakNum in
            # hw/top_earlgrey/data/top_earlgrey.hjson.)
            echo :::: Set all but one available breakpoints.\\n
            # Set a breakpoint at the actual address of rom_main(), without
            # trying to skip the function prologue.
            break *rom_main
            break *uart_init

            echo :::: Pretend execution is enabled.\\n
            set $pc = kRomStartBootExecEn

            echo :::: Continue until watchdog config.\\n
            break kRomStartWatchdogEnabled
            continue

            echo :::: Disable watchdog config.\\n
            set {{int}}{watchdog_ctrl_reg_addr} = 0
            delete 4

            echo :::: Continue until rom_main.\\n
            continue
            assert_pc rom_main

            echo :::: Continue until uart_init.\\n
            continue
            assert_pc uart_init

            echo :::: Finish uart_init.\\n
            finish

            echo :::: Read and write GPRs.\\n
            {gpr_copy_commands}
            {gpr_set_commands}
            {gpr_restore_commands}

            echo :::: Read selected CSRs.\\n
            {csr_copy_commands}
            {csr_set_commands}
            {csr_restore_commands}

            echo :::: Read and write memory (both SRAM and device).\\n
            # See hw/top_earlgrey/sw/autogen/top_earlgrey_memory.h
            set $sram_base = 0x10000000
            set $sram_len = 0x00008000
            x/16xb $sram_base
            x/16xb $sram_base + ($sram_len / 2)
            x/16xb $sram_base + $sram_len - 16

            echo :::: Manually write bytes to UART0.\\n
            set $uart0_base = 0x40000000
            set $uart_wdata = 0x1c
            print *(uint32_t*)($uart0_base + $uart_wdata) = 'O'
            print *(uint32_t*)($uart0_base + $uart_wdata) = 'K'
            print *(uint32_t*)($uart0_base + $uart_wdata) = '!'

            echo :::: Execute code from GDB with `call` command.\\n
            call uart_putchar('G')
            call uart_putchar('D')
            call uart_putchar('B')
            call uart_putchar('-')
            call uart_putchar('O')
            call uart_putchar('K')
            call uart_putchar('\\r')
            call uart_putchar('\\n')

            echo :::: GDB script complete.\\n
            continue
        """.format(
            csr_copy_commands = gdb_commands_copy_registers(get_gdb_readable_csr_names()),
            csr_restore_commands = gdb_commands_restore_registers(get_gdb_settable_csr_names()),
            csr_set_commands = gdb_commands_set_registers(
                "0x89abcdef",
                get_gdb_settable_csr_names(),
            ),
            gpr_copy_commands = gdb_commands_copy_registers(IBEX_GPRS),
            gpr_restore_commands = gdb_commands_restore_registers(IBEX_GPRS),
            gpr_set_commands = gdb_commands_set_registers("0x89abcdef", IBEX_GPRS),
            watchdog_ctrl_reg_addr = "0x40470014",
        ),
        gdb_script_symlinks = {
            "//sw/device/silicon_creator/rom:rom_with_fake_keys_fpga_cw310.elf": "rom.elf",
        },
        rom_bitstream = ":rom_otp_{}_exec_disabled".format(lc_state),
        rom_kind = "Rom",
        tags = [
            "cw310_rom",
            "vivado",
        ] + maybe_skip_in_ci(lc_state_val),
    )
    for lc_state, lc_state_val in get_lc_items(
        CONST.LCV.TEST_UNLOCKED0,
        CONST.LCV.DEV,
        CONST.LCV.RMA,
    )
]

test_suite(
    name = "rom_e2e_debug_test",
    tags = ["manual"],
    tests = [
        "rom_e2e_debug_test_otp_" + lc_state
        for lc_state, _ in get_lc_items(
            CONST.LCV.TEST_UNLOCKED0,
            CONST.LCV.DEV,
            CONST.LCV.RMA,
        )
    ],
)

opentitan_flash_binary(
    name = "rom_ext_upgrade_test",
    srcs = ["rom_ext_upgrade_test.c"],
    devices = [
        "fpga_cw310",
    ],
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_data",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
    ],
)

opentitan_functest(
    name = "rom_ext_upgrade",
    cw310 = cw310_params(
        # Fail if we see version 3, because the test has updated twice, FAIL, version 0 twice, or PASS
        exit_failure = "(min_security_version_rom_ext:[^01])|(FAIL)|((min_security_version_rom_ext:0(?s:.*)){2,})|(PASS)",
        exit_success = "min_security_version_rom_ext:0(?s:.*)min_security_version_rom_ext:1(?s:.*)" + MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.BOOT_POLICY.ROLLBACK)),
        test_cmds = [
            "--exec=\"fpga load-bitstream --rom-kind=rom $(rootpath {bitstream})\"",
            "--exec=\"bootstrap --clear-uart=true $(rootpath {flash})\"",
            "--exec=\"console --exit-success={exit_success} --exit-failure={exit_failure}\"",
            "fpga",
            "load-bitstream",
            "$(rootpath {bitstream})",  # This test should clean up after itself
        ],
    ),
    ot_flash_binary = "rom_ext_upgrade_test",
    targets = [
        "cw310_rom",
    ],
)

otp_json(
    name = "otp_json_reset_ret_ram_overlay",
    partitions = [
        otp_partition(
            name = "CREATOR_SW_CFG",
            # Set the mask to 1 << kRstmgrReasonSoftwareRequest to trigger a
            # retention RAM reset after a SW-requested reset
            items = {"CREATOR_SW_CFG_RET_RAM_RESET_MASK": "0x4"},
        ),
    ],
)

otp_image(
    name = "otp_img_reset_ret_ram",
    src = "//hw/ip/otp_ctrl/data:otp_json_rma",
    overlays = STD_OTP_OVERLAYS + [":otp_json_reset_ret_ram_overlay"],
    visibility = ["//visibility:private"],
)

bitstream_splice(
    name = "bitstream_reset_ret_ram",
    src = "//hw/bitstream:rom",
    data = ":otp_img_reset_ret_ram",
    meminfo = "//hw/bitstream:otp_mmi",
    tags = ["vivado"] + maybe_skip_in_ci(CONST.LCV.RMA),
    update_usr_access = True,
    visibility = ["//visibility:private"],
)

opentitan_functest(
    name = "rom_e2e_ret_ram_init",
    srcs = ["rom_e2e_ret_ram_init_test.c"],
    cw310 = cw310_params(
        bitstream = ":bitstream_reset_ret_ram",
        tags = ["vivado"] + maybe_skip_in_ci(CONST.LCV.RMA),
    ),
    signed = True,
    targets = [
        "cw310_rom",
    ],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:test_main",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
    ],
)

opentitan_functest(
    name = "rom_e2e_ret_ram_keep",
    srcs = ["rom_e2e_ret_ram_keep_test.c"],
    cw310 = cw310_params(
        bitstream = "//hw/bitstream:rom",
        tags = ["vivado"] + maybe_skip_in_ci(CONST.LCV.RMA),
    ),
    signed = True,
    targets = [
        "cw310_rom",
    ],
    deps = [
        "//hw/top_earlgrey/ip/pwrmgr/data/autogen:pwrmgr_regs",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:test_main",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
    ],
)

manifest({
    "name": "manifest_rom_ext_upgrade_interrupt",
    "address_translation": hex(CONST.FALSE),
    "identifier": hex(CONST.ROM_EXT),
    "security_version": hex(10),
})

otp_json(
    name = "otp_json_rom_ext_upgrade_interrupt",
    partitions = [
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {
                "CREATOR_SW_CFG_DEFAULT_BOOT_DATA_IN_PROD_EN": hex(CONST.TRUE),
            },
        ),
    ],
)

[
    otp_image(
        name = "otp_img_rom_ext_upgrade_interrupt_{}".format(lc_state),
        src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
        overlays = STD_OTP_OVERLAYS + [":otp_json_rom_ext_upgrade_interrupt"],
        visibility = ["//visibility:private"],
    )
    for lc_state, _ in get_lc_items()
]

[
    bitstream_splice(
        name = "bitstream_rom_ext_upgrade_interrupt_{}".format(
            lc_state,
        ),
        src = "//hw/bitstream:rom",
        data = ":otp_img_rom_ext_upgrade_interrupt_{}".format(
            lc_state,
        ),
        meminfo = "//hw/bitstream:otp_mmi",
        tags = ["vivado"] + maybe_skip_in_ci(lc_state_val),
        update_usr_access = True,
        visibility = ["//visibility:private"],
    )
    for lc_state, lc_state_val in get_lc_items()
]

[
    opentitan_functest(
        name = "rom_ext_upgrade_interrupt_{}".format(lc_state),
        srcs = ["rom_ext_upgrade_interrupt.c"],
        cw310 = cw310_params(
            bitstream = ":bitstream_rom_ext_upgrade_interrupt_{}".format(lc_state),
            clear_bitstream = True,
            tags = ["vivado"] + maybe_skip_in_ci(lc_state_val),
        ),
        manifest = ":manifest_rom_ext_upgrade_interrupt",
        targets = [
            "cw310_rom",
        ],
        deps = [
            "//sw/device/lib/testing:flash_ctrl_testutils",
            "//sw/device/lib/testing/test_framework:check",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib:boot_data",
            "//sw/device/silicon_creator/lib:test_main",
            "//sw/device/silicon_creator/lib/drivers:lifecycle",
            "//sw/device/silicon_creator/lib/drivers:rstmgr",
        ],
    )
    for lc_state, lc_state_val in get_lc_items()
]

test_suite(
    name = "rom_e2e_rom_ext_upgrade_interrupt",
    tags = ["manual"],
    tests = ["rom_ext_upgrade_interrupt_{}".format(lc_state) for lc_state, _ in get_lc_items()],
)
