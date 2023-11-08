# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "opentitan_binary",
)
load(
    "//rules:opentitan_test.bzl",
    "cw310_params",
    "dv_params",
    "opentitan_functest",
    "verilator_params",
)
load(
    "//rules:const.bzl",
    "CONST",
    "hex_digits",
)
load(
    "//rules:opentitan.bzl",
    "RSA_ONLY_KEY_STRUCTS",
    "bin_to_vmem",
    "opentitan_flash_binary",
    "scramble_flash_vmem",
)
load(
    "//rules:otp.bzl",
    "otp_image",
    "otp_json",
    "otp_partition",
)
load(
    "//rules:rom_e2e.bzl",
    "maybe_skip_in_ci",
)
load(
    "//rules:splice.bzl",
    "bitstream_splice",
)
load(
    "//sw/device/silicon_creator/rom/e2e:defs.bzl",
    "MSG_PASS",
    "MSG_TEMPLATE_BFV",
    "SIGVERIFY_LC_KEYS",
    "SLOTS",
)

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "empty_test",
    srcs = ["empty_test.c"],
)

# Default OTP in TEST_UNLOCKED state
otp_json(
    name = "otp_json_default",
    partitions = [
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {
                "CREATOR_SW_CFG_ROM_EXEC_EN": "0xffffffff",
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
    src = "//hw/bitstream/hyperdebug:rom_with_fake_keys",
    data = ":otp_img_default",
    meminfo = "//hw/bitstream/hyperdebug:otp_mmi",
    tags = maybe_skip_in_ci(CONST.LCV.RMA),
    update_usr_access = True,
    visibility = ["//visibility:private"],
)

opentitan_functest(
    name = "rom_e2e_default_otp_bootup",
    srcs = ["//sw/device/silicon_creator/rom/e2e:empty_test"],
    cw310 = cw310_params(
        bitstream = ":bitstream_default_otp",
        interface = "hyper310",
        tags = maybe_skip_in_ci(CONST.LCV.RMA),
    ),
    signed = True,
    targets = [
        "cw310_rom_with_fake_keys",
    ],
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/silicon_creator/lib/sigverify:spx_verify",
    ],
)

[
    opentitan_flash_binary(
        name = "empty_test_slot_{}".format(slot),
        testonly = True,
        srcs = ["//sw/device/silicon_creator/rom/e2e:empty_test"],
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
            "//sw/device/silicon_creator/lib/sigverify:spx_verify",
        ],
    )
    for slot in SLOTS
]

[
    # TODO(#19923): This target has been temporarily added until the original
    # target and its dependencies are migrated to the new build and test rules.
    opentitan_binary(
        name = "new_empty_test_slot_{}".format(slot),
        testonly = True,
        srcs = ["//sw/device/silicon_creator/rom/e2e:empty_test"],
        exec_env = [
            "//hw/top_earlgrey:fpga_cw310",
            "//hw/top_earlgrey:sim_dv",
            "//hw/top_earlgrey:sim_verilator",
        ],
        linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_{}".format(slot),
        deps = [
            "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib/drivers:lifecycle",
            "//sw/device/silicon_creator/lib/drivers:otp",
            "//sw/device/silicon_creator/lib/sigverify:spx_verify",
        ],
    )
    for slot in SLOTS
]

[
    genrule(
        name = "empty_test_slot_{}_corrupted_{}_bin_signed_{}".format(slot, device, key),
        testonly = True,
        srcs = [":empty_test_slot_{}_{}_bin_signed_{}".format(slot, device, key)],
        outs = ["empty_test_slot_{}_corrupted_{}.{}.signed.bin".format(slot, device, key)],
        cmd_bash = "cat $(SRCS) > $(OUTS) && dd if=/dev/zero of=$(OUTS) bs=4 seek=1971 count=1 conv=notrunc status=none".format(slot),
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

opentitan_functest(
    name = "rom_e2e_flash_ctrl_init",
    srcs = ["rom_e2e_flash_ctrl_init_test.c"],
    cw310 = cw310_params(
        interface = "hyper310",
    ),
    signed = True,
    targets = [
        "cw310_rom_with_fake_keys",
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
        interface = "hyper310",
    ),
    dv = dv_params(
        rom = "//sw/device/silicon_creator/rom:rom_with_fake_keys",
    ),
    signed = True,
    targets = [
        "dv",
        "cw310_rom_with_fake_keys",
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
        "//sw/device/silicon_creator/lib/base:static_critical",
    ],
)

opentitan_functest(
    name = "rom_e2e_smoke",
    cw310 = cw310_params(
        bitstream = "//hw/bitstream/hyperdebug:rom_with_fake_keys",
        interface = "hyper310",
    ),
    dv = dv_params(
        rom = "//sw/device/silicon_creator/rom:rom_with_fake_keys",
    ),
    key_struct = RSA_ONLY_KEY_STRUCTS[0],
    ot_flash_binary = ":empty_test_slot_a",
    targets = [
        "cw310_rom_with_fake_keys",
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
    cw310 = cw310_params(
        interface = "hyper310",
    ),
    dv = dv_params(
        rom = "//sw/device/silicon_creator/rom:rom_with_fake_keys",
    ),
    signed = True,
    targets = [
        "dv",
        "cw310_rom_with_fake_keys",
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

opentitan_functest(
    name = "rom_e2e_c_init",
    srcs = ["rom_e2e_c_init_test.c"],
    cw310 = cw310_params(
        exit_failure = CONST.SHUTDOWN.PREFIX.BFV,
        exit_success = MSG_PASS,
        interface = "hyper310",
    ),
    signed = True,
    targets = [
        "cw310_rom_with_fake_keys",
    ],
    deps = [
        "//hw/ip/uart/data:uart_regs",
        "//hw/top_earlgrey/ip/pinmux/data/autogen:pinmux_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/silicon_creator/lib:manifest_def",
        "//sw/device/silicon_creator/lib/base:static_critical",
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
        bitstream = "//hw/bitstream/hyperdebug:rom_with_fake_keys_otp_dev",
        interface = "hyper310",
        # TODO(lowRISC/opentitan#13603): Remove this "manual" tag when the
        # bitstream target can fetch pre-spliced bitstream from GCP.
        tags = ["manual"],
    ),
    key_struct = RSA_ONLY_KEY_STRUCTS[0],
    ot_flash_binary = ":empty_test_slot_a",
    targets = ["cw310_rom_with_fake_keys"],
)

opentitan_functest(
    name = "sigverify_key_auth",
    cw310 = cw310_params(
        exit_failure = MSG_PASS,
        exit_success = MSG_TEMPLATE_BFV.format(hex_digits(CONST.BFV.SIGVERIFY.BAD_RSA_KEY)),
        interface = "hyper310",
    ),
    key_struct = "rsa_unauthorized_0",
    ot_flash_binary = ":empty_test_slot_a",
    targets = ["cw310_rom_with_fake_keys"],
)

opentitan_flash_binary(
    name = "rom_ext_upgrade_test",
    testonly = True,
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
        interface = "hyper310",
        test_cmds = [
            "--exec=\"fpga load-bitstream $(rootpath {bitstream})\"",
            "--exec=\"transport init\"",
            "--exec=\"bootstrap --clear-uart=true $(rootpath {flash})\"",
            "--exec=\"console --exit-success={exit_success} --exit-failure={exit_failure}\"",
            # We clear the bitstream to force any subsequent test to load a
            # fresh bitstream and clear all memories (ie: flash-based boot policy).
            "--exec=\"fpga clear-bitstream\"",
            "no-op",
        ],
    ),
    ot_flash_binary = "rom_ext_upgrade_test",
    targets = [
        "cw310_rom_with_fake_keys",
    ],
)
