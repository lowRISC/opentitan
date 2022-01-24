# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "OPENTITAN_CPU", "opentitan_rom_binary")
load("//rules:linker.bzl", "ld_library")
load(
    "//rules:opentitan_test.bzl",
    "cw310_params",
    "opentitan_functest",
    "verilator_params",
)
load("//rules:cross_platform.bzl", "dual_cc_device_library_of", "dual_cc_library", "dual_inputs")

package(default_visibility = ["//visibility:public"])

dual_cc_library(
    name = "boot_policy_ptrs",
    srcs = dual_inputs(
        host = ["mock_boot_policy_ptrs.cc"],
        shared = ["boot_policy_ptrs.c"],
    ),
    hdrs = dual_inputs(
        host = ["mock_boot_policy_ptrs.h"],
        shared = ["boot_policy_ptrs.h"],
    ),
    deps = dual_inputs(
        host = [
            "//sw/device/lib/base/testing:global_mock",
            "//sw/device/silicon_creator/testing:mask_rom_test",
            "@googletest//:gtest",
        ],
        shared = [
            "//sw/device/silicon_creator/lib:manifest",
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        ],
    ),
)

cc_library(
    name = "boot_policy",
    srcs = ["boot_policy.c"],
    hdrs = ["boot_policy.h"],
    deps = [
        ":boot_policy_ptrs",
        "//sw/device/lib/base:hardened",
        "//sw/device/silicon_creator/lib:boot_data",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib:manifest",
        "//sw/device/silicon_creator/lib:shutdown",
    ],
)

cc_test(
    name = "boot_policy_unittest",
    srcs = ["boot_policy_unittest.cc"],
    deps = [
        ":boot_policy",
        "//sw/device/silicon_creator/testing:mask_rom_test",
        "@googletest//:gtest_main",
    ],
)

ld_library(
    name = "linker_script",
    script = "mask_rom.ld",
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey_memory",
        "//sw/device:info_sections",
        "//sw/device/silicon_creator/lib/base:static_critical_sections",
    ],
)

opentitan_rom_binary(
    name = "mask_rom",
    srcs = [
        "mask_rom.c",
        "mask_rom.h",
        "mask_rom_start.S",
    ],
    # Mask ROM does not permit the DV simulation backdoor logging mechanism that
    # test ROM does, for obvious security reasons.
    extract_sw_logs_db = False,
    deps = [
        ":boot_policy",
        ":bootstrap",
        ":linker_script",
        ":mask_rom_epmp",
        ":sigverify_keys",
        "//hw/ip/aon_timer/data:aon_timer_regs",
        "//hw/ip/csrng/data:csrng_regs",
        "//hw/ip/edn/data:edn_regs",
        "//hw/ip/entropy_src/data:entropy_src_regs",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/ip/sram_ctrl/data:sram_ctrl_regs",
        "//hw/top_earlgrey/ip/ast/data:ast_regs",
        "//hw/top_earlgrey/ip/clkmgr/data/autogen:clkmgr_regs",
        "//hw/top_earlgrey/ip/pwrmgr/data/autogen:pwrmgr_regs",
        "//hw/top_earlgrey/ip/sensor_ctrl/data:sensor_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:stdasm",
        "//sw/device/lib/crt",
        "//sw/device/lib/runtime:hart",
        "//sw/device/silicon_creator/lib:cfi",
        "//sw/device/silicon_creator/lib:epmp",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib:irq_asm",
        "//sw/device/silicon_creator/lib:manifest",
        "//sw/device/silicon_creator/lib:rom_print",
        "//sw/device/silicon_creator/lib:shutdown",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
        "//sw/device/silicon_creator/lib/base:static_critical_sec_mmio",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:ibex",
        "//sw/device/silicon_creator/lib/drivers:keymgr",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:pinmux",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/drivers:rnd",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
        "//sw/device/silicon_creator/lib/drivers:uart",
        "//sw/device/silicon_creator/lib/drivers:watchdog",
        "//sw/device/silicon_creator/lib/sigverify",
    ],
)

cc_library(
    name = "mask_rom_epmp",
    srcs = [
        "mask_rom_epmp.c",
        "mask_rom_epmp_init.S",
    ],
    hdrs = ["mask_rom_epmp.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:csr",
        "//sw/device/silicon_creator/lib:epmp",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
    ],
)

opentitan_functest(
    name = "mask_rom_epmp_test",
    srcs = [
        "mask_rom_epmp_test.c",
        "mask_rom_start.S",
    ],
    # This test doesn't use the OTTF.
    targets = ["verilator"],  # Can only run in verilator right now.
    # This test is designed to run and complete entirely in the ROM boot stage.
    # Setting the `test_in_rom` flag makes the `opentitan_functest` rule aware
    # of this, and instructs it to load the test image into ROM (rather than
    # loading the default test ROM, or any other ROM that may be specified via
    # Verilator or CW310 params).
    test_in_rom = True,
    deps = [
        ":linker_script",
        ":mask_rom_epmp",
        "//hw/ip/aon_timer/data:aon_timer_regs",
        "//hw/ip/csrng/data:csrng_regs",
        "//hw/ip/edn/data:edn_regs",
        "//hw/ip/entropy_src/data:entropy_src_regs",
        "//hw/ip/flash_ctrl/data:flash_ctrl_regs",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/ip/sram_ctrl/data:sram_ctrl_regs",
        "//hw/top_earlgrey/ip/ast/data:ast_regs",
        "//hw/top_earlgrey/ip/clkmgr/data/autogen:clkmgr_regs",
        "//hw/top_earlgrey/ip/pwrmgr/data/autogen:pwrmgr_regs",
        "//hw/top_earlgrey/ip/sensor_ctrl/data:sensor_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/crt",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:status",
        "//sw/device/silicon_creator/lib:epmp",
        "//sw/device/silicon_creator/lib:epmp_test_unlock",
        "//sw/device/silicon_creator/lib:irq_asm",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:uart",
    ],
)

cc_library(
    name = "bootstrap",
    srcs = ["bootstrap.c"],
    hdrs = ["bootstrap.h"],
    deps = [
        "//hw/ip/flash_ctrl/data:flash_ctrl_regs",
        "//hw/ip/gpio/data:gpio_regs",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:hardened",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
        "//sw/device/silicon_creator/lib/drivers:spi_device",
    ],
)

cc_test(
    name = "bootstrap_unittest",
    srcs = ["bootstrap_unittest.cc"],
    deps = [
        ":bootstrap",
        "//hw/ip/flash_ctrl/data:flash_ctrl_regs",
        "//hw/ip/gpio/data:gpio_regs",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "@googletest//:gtest_main",
    ],
)

dual_cc_library(
    name = "sigverify_keys_ptrs",
    srcs = dual_inputs(
        host = ["mock_sigverify_keys_ptrs.cc"],
        shared = ["sigverify_keys_ptrs.c"],
    ),
    hdrs = dual_inputs(
        host = ["mock_sigverify_keys_ptrs.h"],
        shared = ["sigverify_keys_ptrs.h"],
    ),
    deps = dual_inputs(
        host = [
            "//sw/device/lib/base/testing:global_mock",
            "//sw/device/silicon_creator/testing:mask_rom_test",
            "@googletest//:gtest",
        ],
        shared = [
            "//sw/device/lib/base:macros",
            "//sw/device/silicon_creator/lib/sigverify:rsa_key",
        ],
    ),
)

cc_library(
    name = "sigverify_keys",
    srcs = ["sigverify_keys.c"],
    hdrs = ["sigverify_keys.h"],
    deps = [
        ":sigverify_keys_ptrs",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:macros",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/silicon_creator/lib/drivers:rnd",
        "//sw/device/silicon_creator/lib/sigverify:rsa_key",
        "//sw/device/silicon_creator/lib/sigverify:sigverify_without_mod_exp_ibex_mock",
        "//sw/device/silicon_creator/mask_rom/keys:test_public_keys",
    ],
)

cc_test(
    name = "sigverify_keys_unittest",
    srcs = ["sigverify_keys_unittest.cc"],
    deps = [
        ":sigverify_keys",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/silicon_creator/mask_rom/keys:test_public_keys",
        "//sw/device/silicon_creator/testing:mask_rom_test",
        "@googletest//:gtest_main",
    ],
)

# MASK ROM E2E TESTS

# Bootup tests
BOOT_FAILURE_MSG = "BFV:[0-9a-z]{{8}}\r\nLCV:[0-9a-z]{{8}}\r\n"

opentitan_functest(
    name = "e2e_bootup_success",
    srcs = ["mask_rom_test.c"],
    cw310 = cw310_params(
        bitstream = "//hw/bitstream:mask_rom",
        tags = ["broken"],
    ),
    signed = True,
    targets = [
        "verilator",
        "cw310",
    ],
    verilator = verilator_params(
        rom = ":mask_rom_sim_verilator_scr_vmem",
        tags = [
            "broken",
            "cpu:4",
        ],
    ),
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

# TODO: Add verilator test
opentitan_functest(
    name = "e2e_bootup_no_rom_ext_signature",
    srcs = ["mask_rom_test.c"],
    cw310 = cw310_params(
        args = [
            "--exec=\"load-bitstream --rom-kind={rom_kind} $(location {bitstream})\"",
            "--exec=\"bootstrap --protocol {bootstrap_protocol} $(location {flash})\"",
            "console",
            "--timeout=3600s",
            "--exit-success='{}'".format(BOOT_FAILURE_MSG),
            "--exit-failure='PASS!'",
        ],
        bitstream = "//hw/bitstream:mask_rom",
        tags = ["broken"],
    ),
    signed = False,
    targets = ["cw310"],
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)
