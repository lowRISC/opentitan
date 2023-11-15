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
load(
    "//rules/opentitan:defs.bzl",
    "opentitan_binary",
    "opentitan_test",
    "rsa_key_by_name",
    new_cw310_params = "cw310_params",
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
    src = "//hw/bitstream:rom_with_fake_keys",
    data = ":otp_img_default",
    meminfo = "//hw/bitstream:otp_mmi",
    tags = maybe_skip_in_ci(CONST.LCV.RMA),
    update_usr_access = True,
    visibility = ["//visibility:private"],
)

opentitan_functest(
    name = "rom_e2e_default_otp_bootup",
    srcs = ["//sw/device/silicon_creator/rom/e2e:empty_test"],
    cw310 = cw310_params(
        bitstream = ":bitstream_default_otp",
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
    opentitan_binary(
        name = "empty_test_slot_{}_{}".format(slot, key),
        testonly = True,
        srcs = ["//sw/device/silicon_creator/rom/e2e:empty_test"],
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
            "//hw/top_earlgrey:sim_dv": None,
            "//hw/top_earlgrey:sim_verilator": None,
        },
        linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_{}".format(slot),
        # We need to specify the manifest because the simulation environments do not
        # specify one by default.
        manifest = "//sw/device/silicon_creator/rom_ext:manifest_standard",
        rsa_key = rsa_key_by_name(RSA_ONLY_KEY_STRUCTS, key),
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
    for key in SIGVERIFY_LC_KEYS
]

# Extract the various signed binaries for corruption
[
    filegroup(
        name = "empty_test_slot_{}_{}_{}_signed_bin".format(slot, key, group),
        testonly = True,
        srcs = [":empty_test_slot_{}_{}".format(slot, key)],
        output_group = "{}_signed_bin".format(group),
    )
    for slot in SLOTS
    for key in SIGVERIFY_LC_KEYS
    for group in [
        "fpga_cw310_rom_with_fake_keys",
        "sim_dv",
    ]
]

# Corrupt binaries
# Note: the naming of the files is important for dvsim. The code expects fiel to be named:
# - binary: <something>.<key_name>.signed.bin
# - vmem: <something>.<key_name>.signed.64.vmem
# - flash vmem: <something>.<key_name>.signed.64.scr.vmem
[
    genrule(
        name = "empty_test_slot_{}_{}_corrupted_{}_signed_bin".format(slot, key, group),
        testonly = True,
        srcs = [":empty_test_slot_{}_{}_{}_signed_bin".format(slot, key, group)],
        outs = ["empty_test_slot_{}_corrupted_{}.{}.signed.bin".format(slot, group, key)],
        cmd_bash = "cat $(SRCS) > $(OUTS) && dd if=/dev/zero of=$(OUTS) bs=4 seek=1971 count=1 conv=notrunc status=none",
    )
    for slot in SLOTS
    for key in SIGVERIFY_LC_KEYS
    for group in [
        "fpga_cw310_rom_with_fake_keys",
        "sim_dv",
    ]
]

# The below three rule sets (bin_to_vmem, scramble_flash_vmem, and filegroup)
# are needed to run `sigverify_always` tests in DV.
[
    bin_to_vmem(
        name = "empty_test_slot_{}_{}_corrupted_sim_dv_vmem64_signed".format(slot, key),
        testonly = True,
        bin = "empty_test_slot_{}_{}_corrupted_sim_dv_signed_bin".format(slot, key),
        word_size = 64,  # Backdoor-load VMEM image uses 64-bit words
    )
    for slot in SLOTS
    for key in SIGVERIFY_LC_KEYS
]

[
    scramble_flash_vmem(
        name = "empty_test_slot_{}_{}_corrupted_sim_dv_scr_vmem64_signed".format(slot, key),
        testonly = True,
        vmem = "empty_test_slot_{}_{}_corrupted_sim_dv_vmem64_signed".format(slot, key),
    )
    for slot in SLOTS
    for key in SIGVERIFY_LC_KEYS
]

# This file group is here to simplify the naming of the files in the hjson testplan:
# the file group contains the files for all possible keys that follow the expected
# name format specified by the tags.
[
    filegroup(
        name = "empty_test_slot_{}_corrupted_sim_dv".format(slot),
        testonly = True,
        srcs = [
            "empty_test_slot_{}_{}_corrupted_sim_dv_{}".format(slot, key, file_type)
            for file_type in [
                "signed_bin",
                "vmem64_signed",
                "scr_vmem64_signed",
            ]
            for key in SIGVERIFY_LC_KEYS
        ],
    )
    for slot in SLOTS
]

opentitan_functest(
    name = "rom_e2e_flash_ctrl_init",
    srcs = ["rom_e2e_flash_ctrl_init_test.c"],
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
        bitstream = "//hw/bitstream:rom_with_fake_keys",
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
        bitstream = "//hw/bitstream:rom_with_fake_keys_otp_dev",
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
        test_cmds = [
            "--exec=\"transport init\"",
            "--exec=\"fpga load-bitstream $(rootpath {bitstream})\"",
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
