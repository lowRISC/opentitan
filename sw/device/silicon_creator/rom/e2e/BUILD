# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:opentitan_test.bzl",
    "DEFAULT_TEST_FAILURE_MSG",
    "cw310_params",
    "dv_params",
    "opentitan_functest",
    "verilator_params",
)
load("//rules:const.bzl", "CONST", "error_redact", "hex")
load(
    "//rules:opentitan.bzl",
    "opentitan_flash_binary",
    "opentitan_multislot_flash_binary",
)
load("//rules:manifest.bzl", "manifest")
load("//rules:opentitan_gdb_test.bzl", "opentitan_gdb_fpga_cw310_test")
load("//rules:otp.bzl", "otp_image", "otp_json", "otp_partition")
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
        exit_success = MSG_TEMPLATE_BFV.format(hex(CONST.BFV.INTERRUPT.INSTRUCTION_ACCESS)),
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
        exit_success = MSG_TEMPLATE_BFV.format(hex(CONST.BFV.INTERRUPT.INSTRUCTION_ACCESS)),
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
    name = "rom_e2e_keymgr_init",
    srcs = ["rom_e2e_keymgr_init_test.c"],
    dv = dv_params(
        rom = "//sw/device/silicon_creator/rom",
    ),
    signed = True,
    targets = [
        "cw310_rom",
        "dv",
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
            "key": "test_key_0",
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
            "key": "test_key_0",
            "offset": SLOTS["b"],
        },
    },
)

opentitan_functest(
    name = "rom_ext_a_flash_b",
    cw310 = cw310_params(
        exit_failure = MSG_STARTING_ROM_EXT,
        exit_success = MSG_TEMPLATE_BFV.format(hex(CONST.BFV.INTERRUPT.STORE_ACCESS)),
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
            "offset": SLOTS["a"],
        },
    },
)

opentitan_functest(
    name = "rom_ext_b_flash_a",
    cw310 = cw310_params(
        exit_failure = MSG_STARTING_ROM_EXT,
        exit_success = MSG_TEMPLATE_BFV.format(hex(CONST.BFV.INTERRUPT.STORE_ACCESS)),
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
            "key": "test_key_0",
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
        exit_success = MSG_TEMPLATE_BFV.format(hex(CONST.BFV.INTERRUPT.ILLEGAL_INSTRUCTION)),
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
        exit_success = MSG_TEMPLATE_BFV.format(hex(CONST.BFV.SIGVERIFY.BAD_KEY)),
    ),
    key = "unauthorized_0",
    ot_flash_binary = ":empty_test_slot_a",
    targets = ["cw310_rom"],
)

[otp_image(
    name = "otp_img_shutdown_output_{}".format(lc_state.lower()),
    src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state.lower()),
    overlays = [
        "//hw/ip/otp_ctrl/data:otp_json_creator_sw_cfg",
        "//hw/ip/otp_ctrl/data:otp_json_owner_sw_cfg",
        "//hw/ip/otp_ctrl/data:otp_json_hw_cfg",
    ],
) for lc_state in structs.to_dict(CONST.LCV)]

# Splice OTP images into bitstreams
[
    bitstream_splice(
        name = "bitstream_shutdown_output_{}".format(lc_state.lower()),
        src = "//hw/bitstream:rom",
        data = ":otp_img_shutdown_output_{}".format(lc_state.lower()),
        meminfo = "//hw/bitstream:otp_mmi",
        tags = ["vivado"],
        update_usr_access = True,
    )
    for lc_state in structs.to_dict(CONST.LCV)
]

manifest({
    "name": "manifest_bad_identifier",
    "address_translation": CONST.FALSE,
    "identifier": 0,
})

[opentitan_functest(
    name = "shutdown_output_{}".format(lc_state.lower()),
    cw310 = cw310_params(
        bitstream = ":bitstream_shutdown_output_{}".format(lc_state.lower()),
        exit_failure = MSG_PASS,
        exit_success = MSG_TEMPLATE_BFV_LCV.format(
            hex(CONST.BFV.BOOT_POLICY.BAD_IDENTIFIER),
            hex(lc_state_val),
        ),
        tags = ["vivado"] + maybe_skip_in_ci(lc_state_val),
    ),
    manifest = ":manifest_bad_identifier",
    ot_flash_binary = ":empty_test_slot_a",
    signed = False,
    targets = ["cw310_rom"],
) for lc_state, lc_state_val in structs.to_dict(CONST.LCV).items()]

test_suite(
    name = "shutdown_output",
    tags = ["manual"],
    tests = ["shutdown_output_{}".format(lc_state.lower()) for lc_state in structs.to_dict(CONST.LCV)],
)

SEC_VERS = [
    0,
    1,
    2,
]

[manifest({
    "name": "manifest_sec_ver_{}".format(sec_ver),
    "address_translation": CONST.FALSE,
    "identifier": CONST.ROM_EXT,
    "security_version": sec_ver,
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
            "key": "test_key_0",
            "offset": SLOTS["a"],
        },
        ":empty_test_slot_b_sec_ver_{}".format(sec_ver_b): {
            "key": "test_key_0",
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
    overlays = [
        "//hw/ip/otp_ctrl/data:otp_json_creator_sw_cfg",
        "//hw/ip/otp_ctrl/data:otp_json_owner_sw_cfg",
        "//hw/ip/otp_ctrl/data:otp_json_hw_cfg",
    ],
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
        exit_success = t["exit_success"].format(hex(lc_state_val)),
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
    # TODO(#14473): Enable after OTP splicing is ready.
    # {
    #     "a": 0,
    #     "b": 0,
    #     "exit_success": MSG_TEMPLATE_BFV.format(hex(CONST.BFV.BOOT_POLICY.ROLLBACK)),
    # },
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

[opentitan_functest(
    name = "boot_policy_rollback_a_{}_b_{}".format(
        t["a"],
        t["b"],
    ),
    cw310 = cw310_params(
        exit_success = t["exit_success"],
    ),
    key = "multislot",
    ot_flash_binary = ":sec_ver_{}_{}_image".format(
        t["a"],
        t["b"],
    ),
    targets = ["cw310_rom"],
) for t in BOOT_POLICY_ROLLBACK_CASES]

test_suite(
    name = "boot_policy_rollback",
    tags = ["manual"],
    tests = ["boot_policy_rollback_a_{}_b_{}".format(
        t["a"],
        t["b"],
    ) for t in BOOT_POLICY_ROLLBACK_CASES],
)

SIGVERIFY_MOD_EXP_CASES = [
    {
        "name": "sw",
        "use_sw_rsa_verify": CONST.TRUE,
        "exit_success": {lc_state.lower(): "use_sw_rsa_verify=0x00000739" for lc_state in structs.to_dict(CONST.LCV)},
    },
    {
        "name": "otbn",
        "use_sw_rsa_verify": CONST.FALSE,
        "exit_success": {lc_state.lower(): "use_sw_rsa_verify=0x000001d4" for lc_state in structs.to_dict(CONST.LCV)},
    },
    {
        "name": "invalid",
        "use_sw_rsa_verify": 0,
        "exit_success": {
            lc_state.lower(): MSG_TEMPLATE_BFV.format(hex(CONST.BFV.INTERRUPT.ILLEGAL_INSTRUCTION)) if lc_state_val != CONST.LCV.TEST_UNLOCKED0 else "use_sw_rsa_verify=0x00000000"
            for lc_state, lc_state_val in structs.to_dict(CONST.LCV).items()
        },
    },
]

opentitan_flash_binary(
    name = "empty_test_sigverify_mod_exp",
    srcs = ["empty_test.c"],
    devices = ["fpga_cw310"],
    local_defines = [
        shell.quote("EMPTY_TEST_MSG=\"use_sw_rsa_verify=0x%08x\", otp_read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_USE_SW_RSA_VERIFY_OFFSET)"),
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
                items = {"CREATOR_SW_CFG_USE_SW_RSA_VERIFY": "0x{}".format(hex(t["use_sw_rsa_verify"]))},
            ),
        ],
    )
    for t in SIGVERIFY_MOD_EXP_CASES
]

[
    otp_image(
        name = "otp_img_sigverify_mod_exp_{}_{}".format(
            lc_state.lower(),
            t["name"],
        ),
        src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state.lower()),
        overlays = [
            "//hw/ip/otp_ctrl/data:otp_json_creator_sw_cfg",
            "//hw/ip/otp_ctrl/data:otp_json_owner_sw_cfg",
            "//hw/ip/otp_ctrl/data:otp_json_hw_cfg",
            ":otp_json_sigverify_mod_exp_{}".format(t["name"]),
        ],
        visibility = ["//visibility:private"],
    )
    for lc_state in structs.to_dict(CONST.LCV)
    for t in SIGVERIFY_MOD_EXP_CASES
]

[
    bitstream_splice(
        name = "bitstream_sigverify_mod_exp_{}_{}".format(
            lc_state.lower(),
            t["name"],
        ),
        src = "//hw/bitstream:rom",
        data = ":otp_img_sigverify_mod_exp_{}_{}".format(
            lc_state.lower(),
            t["name"],
        ),
        meminfo = "//hw/bitstream:otp_mmi",
        tags = ["vivado"],
        update_usr_access = True,
        visibility = ["//visibility:private"],
    )
    for lc_state in structs.to_dict(CONST.LCV)
    for t in SIGVERIFY_MOD_EXP_CASES
]

[
    opentitan_functest(
        name = "sigverify_mod_exp_{}_{}".format(
            lc_state.lower(),
            t["name"],
        ),
        cw310 = cw310_params(
            bitstream = ":bitstream_sigverify_mod_exp_{}_{}".format(
                lc_state.lower(),
                t["name"],
            ),
            exit_success = t["exit_success"][lc_state.lower()],
            tags = ["vivado"] + maybe_skip_in_ci(lc_state_val),
        ),
        ot_flash_binary = ":empty_test_sigverify_mod_exp",
        targets = ["cw310_rom"],
    )
    for lc_state, lc_state_val in structs.to_dict(CONST.LCV).items()
    for t in SIGVERIFY_MOD_EXP_CASES
]

test_suite(
    name = "rom_e2e_sigverify_mod_exp",
    tags = ["manual"],
    tests = ["sigverify_mod_exp_{}_{}".format(
        lc_state.lower(),
        t["name"],
    ) for lc_state in structs.to_dict(CONST.LCV) for t in SIGVERIFY_MOD_EXP_CASES],
)

BOOT_POLICY_BAD_MANIFEST_CASES = [
    {
        "name": "bad_identifier",
        "manifest": {
            "identifier": 0,
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex(CONST.BFV.BOOT_POLICY.BAD_IDENTIFIER)),
    },
    {
        "name": "too_small",
        "manifest": {
            "identifier": CONST.ROM_EXT,
            "length": CONST.ROM_EXT_SIZE_MIN - 1,
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex(CONST.BFV.BOOT_POLICY.BAD_LENGTH)),
    },
    {
        "name": "too_large",
        "manifest": {
            "identifier": CONST.ROM_EXT,
            "length": CONST.ROM_EXT_SIZE_MAX + 1,
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex(CONST.BFV.BOOT_POLICY.BAD_LENGTH)),
    },
    {
        "name": "empty_code",
        "manifest": {
            # Note: `length` is filled automatically unless overriden here.
            "identifier": CONST.ROM_EXT,
            "code_start": CONST.MANIFEST_SIZE + 12,
            "code_end": CONST.MANIFEST_SIZE + 12,
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex(CONST.BFV.MANIFEST.BAD_CODE_REGION)),
    },
    {
        "name": "code_in_manifest",
        "manifest": {
            "identifier": CONST.ROM_EXT,
            "code_start": CONST.MANIFEST_SIZE - 4,
            "code_end": CONST.MANIFEST_SIZE + 12,
            "entry_point": CONST.MANIFEST_SIZE + 8,
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex(CONST.BFV.MANIFEST.BAD_CODE_REGION)),
    },
    {
        "name": "code_outside_image",
        "manifest": {
            "identifier": CONST.ROM_EXT,
            "code_start": CONST.ROM_EXT_SIZE_MAX,
            "code_end": CONST.MANIFEST_SIZE + 12,
            "entry_point": CONST.MANIFEST_SIZE + 8,
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex(CONST.BFV.MANIFEST.BAD_CODE_REGION)),
    },
    {
        "name": "code_start_unaligned",
        "manifest": {
            "identifier": CONST.ROM_EXT,
            "code_start": CONST.MANIFEST_SIZE + 6,
            "code_end": CONST.MANIFEST_SIZE + 12,
            "entry_point": CONST.MANIFEST_SIZE + 8,
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex(CONST.BFV.MANIFEST.BAD_CODE_REGION)),
    },
    {
        "name": "code_end_unaligned",
        "manifest": {
            "identifier": CONST.ROM_EXT,
            "code_start": CONST.MANIFEST_SIZE + 8,
            "code_end": CONST.MANIFEST_SIZE + 10,
            "entry_point": CONST.MANIFEST_SIZE + 8,
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex(CONST.BFV.MANIFEST.BAD_CODE_REGION)),
    },
    {
        "name": "entry_before_code_start",
        "manifest": {
            "identifier": CONST.ROM_EXT,
            "code_start": CONST.MANIFEST_SIZE + 8,
            "code_end": CONST.MANIFEST_SIZE + 12,
            "entry_point": CONST.MANIFEST_SIZE + 4,
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex(CONST.BFV.MANIFEST.BAD_ENTRY_POINT)),
    },
    {
        "name": "entry_at_code_end",
        "manifest": {
            "identifier": CONST.ROM_EXT,
            "code_start": CONST.MANIFEST_SIZE + 8,
            "code_end": CONST.MANIFEST_SIZE + 12,
            "entry_point": CONST.MANIFEST_SIZE + 12,
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex(CONST.BFV.MANIFEST.BAD_ENTRY_POINT)),
    },
    {
        "name": "entry_unaligned",
        "manifest": {
            "identifier": CONST.ROM_EXT,
            "code_start": CONST.MANIFEST_SIZE + 8,
            "code_end": CONST.MANIFEST_SIZE + 12,
            "entry_point": CONST.MANIFEST_SIZE + 10,
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex(CONST.BFV.MANIFEST.BAD_ENTRY_POINT)),
    },
    {
        "name": "rollback",
        "manifest": {
            "identifier": CONST.ROM_EXT,
            "code_start": CONST.MANIFEST_SIZE + 8,
            "code_end": CONST.MANIFEST_SIZE + 12,
            "entry_point": CONST.MANIFEST_SIZE + 8,
            "security_version": 0,
        },
        "exit_success": MSG_TEMPLATE_BFV.format(hex(CONST.BFV.BOOT_POLICY.ROLLBACK)),
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
            "key": "test_key_0",
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
            lc_state.lower(),
            sec_ver,
        ),
        src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state.lower()),
        overlays = [
            "//hw/ip/otp_ctrl/data:otp_json_creator_sw_cfg",
            "//hw/ip/otp_ctrl/data:otp_json_owner_sw_cfg",
            "//hw/ip/otp_ctrl/data:otp_json_hw_cfg",
            ":otp_json_sec_ver_{}".format(sec_ver),
        ],
        visibility = ["//visibility:private"],
    )
    for lc_state in structs.to_dict(CONST.LCV)
    for sec_ver in [
        0,
        1,
    ]
]

[
    bitstream_splice(
        name = "bitstream_boot_policy_bad_manifest_{}_sec_ver_{}".format(
            lc_state.lower(),
            sec_ver,
        ),
        src = "//hw/bitstream:rom",
        data = ":otp_img_boot_policy_bad_manifest_{}_sec_ver_{}".format(
            lc_state.lower(),
            sec_ver,
        ),
        meminfo = "//hw/bitstream:otp_mmi",
        tags = ["vivado"],
        update_usr_access = True,
        visibility = ["//visibility:private"],
    )
    for lc_state in structs.to_dict(CONST.LCV)
    for sec_ver in [
        0,
        1,
    ]
]

[
    opentitan_functest(
        name = "boot_policy_bad_manifest_{}_{}_{}".format(
            lc_state.lower(),
            t["name"],
            slot,
        ),
        cw310 = cw310_params(
            bitstream = "bitstream_boot_policy_bad_manifest_{}_sec_ver_{}".format(
                lc_state.lower(),
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
    )
    for lc_state, lc_state_val in structs.to_dict(CONST.LCV).items()
    for t in BOOT_POLICY_BAD_MANIFEST_CASES
    for slot in SLOTS
]

test_suite(
    name = "rom_e2e_boot_policy_bad_manifest",
    tags = ["manual"],
    tests = [
        "boot_policy_bad_manifest_{}_{}_{}".format(
            lc_state.lower(),
            t["name"],
            slot,
        )
        for lc_state in structs.to_dict(CONST.LCV)
        for t in BOOT_POLICY_BAD_MANIFEST_CASES
        for slot in SLOTS
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
                items = {"OWNER_SW_CFG_ROM_WATCHDOG_BITE_THRESHOLD_CYCLES": "0x{}".format(hex(t["bite_threshold"]))},
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
        overlays = [
            "//hw/ip/otp_ctrl/data:otp_json_creator_sw_cfg",
            "//hw/ip/otp_ctrl/data:otp_json_owner_sw_cfg",
            "//hw/ip/otp_ctrl/data:otp_json_hw_cfg",
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

[genrule(
    name = "empty_test_slot_{}_corrupted_{}_bin_signed_{}".format(slot, device, key),
    srcs = ["empty_test_slot_{}_{}_bin_signed_{}".format(slot, device, key)],
    outs = ["empty_test_slot_{}_bad_signature_{}_bin_signed_{}".format(slot, device, key)],
    cmd_bash = "cat $(SRCS) > $(OUTS) && dd if=/dev/zero of=$(OUTS) bs=4 seek=7 count=1 conv=notrunc status=none".format(slot),
) for slot in SLOTS for device in ["fpga_cw310"] for key in ["test_key_0"]]

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
                "key": "test_key_0",
                "offset": SLOTS["a"],
            },
            ":empty_test_slot_b{}".format(b["suffix"]): {
                "key": "test_key_0",
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
        overlays = [
            "//hw/ip/otp_ctrl/data:otp_json_creator_sw_cfg",
            "//hw/ip/otp_ctrl/data:otp_json_owner_sw_cfg",
            "//hw/ip/otp_ctrl/data:otp_json_hw_cfg",
        ],
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
            lc_state.lower(),
            a["desc"],
            b["desc"],
        ),
        cw310 = cw310_params(
            bitstream = "bitstream_boot_policy_valid_{}".format(lc_state.lower()),
            exit_failure = MSG_PASS if a["desc"] == b["desc"] and a["desc"] == "bad" else DEFAULT_TEST_FAILURE_MSG,
            exit_success = MSG_TEMPLATE_BFV.format(hex(CONST.BFV.SIGVERIFY.BAD_ENCODED_MSG)) if a["desc"] == b["desc"] and a["desc"] == "bad" else MSG_PASS,
            tags = ["vivado"] + maybe_skip_in_ci(lc_state_val),
        ),
        key = "multislot",
        ot_flash_binary = ":boot_policy_valid_img_a_{}_b_{}".format(
            a["desc"],
            b["desc"],
        ),
        targets = ["cw310_rom"],
    )
    for lc_state, lc_state_val in structs.to_dict(CONST.LCV).items()
    for a in BOOT_POLICY_VALID_CASES
    for b in BOOT_POLICY_VALID_CASES
]

test_suite(
    name = "rom_e2e_boot_policy_valid",
    tags = ["manual"],
    tests = [
        "boot_policy_valid_{}_a_{}_b_{}".format(
            lc_state.lower(),
            a["desc"],
            b["desc"],
        )
        for lc_state in structs.to_dict(CONST.LCV)
        for a in BOOT_POLICY_VALID_CASES
        for b in BOOT_POLICY_VALID_CASES
    ],
)

# Names of OTP configs shared by tests that require execution to be disabled.
OTP_CFGS_EXEC_DISABLED = [
    "test_unlocked0",
    "dev",
    "rma",
]

# Apply an overlay that disables ROM execution on top of the base OTP configs
# derived from `OTP_CFGS_EXEC_DISABLED`.
[
    otp_image(
        name = "img_{}_exec_disabled".format(otp_name),
        src = "//hw/ip/otp_ctrl/data:otp_json_" + otp_name,
        overlays = [
            "//hw/ip/otp_ctrl/data:otp_json_creator_sw_cfg",
            "//hw/ip/otp_ctrl/data:otp_json_owner_sw_cfg",
            "//hw/ip/otp_ctrl/data:otp_json_hw_cfg",
            "//hw/ip/otp_ctrl/data:otp_json_exec_disabled",
        ],
        visibility = ["//visibility:private"],
    )
    for otp_name in OTP_CFGS_EXEC_DISABLED
]

# Splice each execution-disabled OTP image into the ROM bitstream.
[
    bitstream_splice(
        name = "rom_otp_{}_exec_disabled".format(otp_name),
        src = "//hw/bitstream:rom",
        data = "img_{}_exec_disabled".format(otp_name),
        meminfo = "//hw/bitstream:otp_mmi",
        tags = [
            "manual",
            "vivado",
        ],
        update_usr_access = True,
        visibility = ["//visibility:private"],
    )
    for otp_name in OTP_CFGS_EXEC_DISABLED
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
        name = "sram_program_fpga_cw310_test_otp_" + otp_name,
        timeout = "short",
        exit_success_pattern = "sram_program\\.c:\\d+\\] PC: 0x100020e0, SRAM: \\[0x10000000, 0x10020000\\)",
        gdb_script = SRAM_JTAG_INJECTION_GDB_SCRIPT,
        gdb_script_symlinks = {
            "//sw/device/examples/sram_program:sram_program_fpga_cw310.elf": "sram_program.elf",
        },
        rom_bitstream = ":rom_otp_{}_exec_disabled".format(otp_name),
        rom_kind = "Rom",
        tags = [
            "cw310",
            "vivado",
        ],
    )
    for otp_name in OTP_CFGS_EXEC_DISABLED
]

test_suite(
    name = "rom_e2e_jtag_inject_tests",
    tags = [
        "cw310",
        "vivado",
    ],
    tests = ["sram_program_fpga_cw310_test_otp_" + otp_name for otp_name in OTP_CFGS_EXEC_DISABLED],
)

[
    opentitan_gdb_fpga_cw310_test(
        name = "asm_interrupt_handler_fpga_cw310_test_otp_" + otp_name,
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
            "//sw/device/silicon_creator/rom:rom_fpga_cw310.elf": "rom.elf",
        },
        rom_bitstream = ":rom_otp_{}_exec_disabled".format(otp_name),
        rom_kind = "Rom",
        tags = [
            "cw310",
            "vivado",
        ],
    )
    for otp_name in OTP_CFGS_EXEC_DISABLED
]

test_suite(
    name = "rom_e2e_asm_interrupt_handler",
    tags = [
        "cw310",
        "vivado",
    ],
    tests = ["asm_interrupt_handler_fpga_cw310_test_otp_" + otp_name for otp_name in OTP_CFGS_EXEC_DISABLED],
)

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
                    "OWNER_SW_CFG_ROM_ERROR_REPORTING": "0x{}".format(hex(v)),
                },
            ),
        ],
    )
    for k, v in REDACT.items()
]

[
    otp_image(
        name = "img_{}_{}".format(
            lc_state.lower(),
            redact.lower(),
        ),
        src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state.lower()),
        overlays = [
            "//hw/ip/otp_ctrl/data:otp_json_creator_sw_cfg",
            "//hw/ip/otp_ctrl/data:otp_json_owner_sw_cfg",
            "//hw/ip/otp_ctrl/data:otp_json_hw_cfg",
            ":otp_json_{}_overlay".format(redact.lower()),
        ],
        visibility = ["//visibility:private"],
    )
    for lc_state in structs.to_dict(CONST.LCV)
    for redact in REDACT
]

[
    bitstream_splice(
        name = "bitstream_{}_{}".format(
            lc_state.lower(),
            redact.lower(),
        ),
        src = "//hw/bitstream:rom",
        data = ":img_{}_{}".format(
            lc_state.lower(),
            redact.lower(),
        ),
        meminfo = "//hw/bitstream:otp_mmi",
        tags = ["vivado"],
        update_usr_access = True,
        visibility = ["//visibility:private"],
    )
    for lc_state in structs.to_dict(CONST.LCV)
    for redact in REDACT
]

[
    opentitan_functest(
        name = "e2e_shutdown_redact_{}_{}".format(
            lc_state.lower(),
            redact.lower(),
        ),
        srcs = ["empty_test.c"],
        cw310 = cw310_params(
            bitstream = "bitstream_{}_{}".format(
                lc_state.lower(),
                redact.lower(),
            ),
            exit_failure = MSG_PASS,
            exit_success = MSG_TEMPLATE_BFV.format(hex(error_redact(
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
    for lc_state, lc_state_val in structs.to_dict(CONST.LCV).items()
    for redact, redact_val in REDACT.items()
]

test_suite(
    name = "rom_e2e_shutdown_redact",
    tags = ["manual"],
    tests = ["e2e_shutdown_redact_{}_{}".format(
        lc_state.lower(),
        redact.lower(),
    ) for lc_state in structs.to_dict(CONST.LCV) for redact in REDACT],
)
