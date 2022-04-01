# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "OPENTITAN_CPU", "opentitan_rom_binary")
load(
    "//rules:opentitan_test.bzl",
    "cw310_params",
    "opentitan_functest",
    "verilator_params",
)

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "boot_policy",
    srcs = ["boot_policy.c"],
    hdrs = [
        "boot_policy.h",
        "boot_policy_ptrs.h",
    ],
    deps = [
        "//sw/device/lib/base:hardened",
        "//sw/device/silicon_creator/lib:boot_data",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib:manifest_intf",
        "//sw/device/silicon_creator/lib:shutdown",
    ],
)

cc_library(
    name = "mock_boot_policy_ptrs",
    testonly = True,
    hdrs = ["mock_boot_policy_ptrs.h"],
    deps = [
        "//sw/device/lib/base/testing:global_mock",
        "//sw/device/silicon_creator/testing:mask_rom_test",
        "@googletest//:gtest",
    ],
)

cc_test(
    name = "boot_policy_unittest",
    srcs = [
        "boot_policy.c",
        "boot_policy.h",
        "boot_policy_ptrs.h",
        "boot_policy_unittest.cc",
    ],
    defines = ["OT_OFF_TARGET_TEST"],
    deps = [
        ":mock_boot_policy_ptrs",
        "//sw/device/lib/base:hardened",
        "//sw/device/silicon_creator/lib:mock_boot_data",
        "//sw/device/silicon_creator/lib:mock_manifest",
        "//sw/device/silicon_creator/lib:mock_shutdown",
        "//sw/device/silicon_creator/testing:mask_rom_test",
        "@googletest//:gtest_main",
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
    linkopts = [
        "-T $(location mask_rom.ld)",
    ],
    deps = [
        "mask_rom.ld",
        ":boot_policy",
        ":mask_rom_epmp",
        ":primitive_bootstrap",
        ":sigverify_keys",
        "//hw/ip/aon_timer/data:aon_timer_regs",
        "//hw/ip/csrng/data:csrng_regs",
        "//hw/ip/edn/data:edn_regs",
        "//hw/ip/entropy_src/data:entropy_src_regs",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/ip/sram_ctrl/data:sram_ctrl_regs",
        "//hw/top_earlgrey/ip/ast/data:ast_regs",
        "//hw/top_earlgrey/ip/pwrmgr/data/autogen:pwrmgr_regs",
        "//hw/top_earlgrey/ip/sensor_ctrl/data:sensor_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:linker_script",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device:info_sections",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:csr",
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
        "//sw/device/silicon_creator/lib:shutdown",
        "//sw/device/silicon_creator/lib:sigverify",
        "//sw/device/silicon_creator/lib:sigverify_intf",
        "//sw/device/silicon_creator/lib:sigverify_mod_exp_ibex",
        "//sw/device/silicon_creator/lib:sigverify_mod_exp_otbn",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
        "//sw/device/silicon_creator/lib/base:static_critical.ld",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:keymgr",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:pinmux",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/drivers:rnd",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
        "//sw/device/silicon_creator/lib/drivers:uart",
        "//sw/device/silicon_creator/lib/drivers:watchdog",
    ],
)

cc_library(
    name = "mask_rom_epmp",
    srcs = [
        "mask_rom_epmp.S",
        "mask_rom_epmp.c",
    ],
    hdrs = ["mask_rom_epmp.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:csr",
        "//sw/device/silicon_creator/lib:epmp_intf",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
    ],
)

opentitan_functest(
    name = "mask_rom_epmp_test",
    srcs = [
        "mask_rom_epmp_test.c",
        "mask_rom_start.S",
    ],
    linkopts = [
        "-T $(location mask_rom.ld)",
    ],
    # This test doesn't use the OTTF.
    ottf = [],
    targets = ["verilator"],  # Can only run in verilator right now.
    # This test is designed to run and complete entirely in the ROM boot stage.
    # Setting the `test_in_rom` flag makes the `opentitan_functest` rule aware
    # of this, and instructs it to load the test image into ROM (rather than
    # loading the default test ROM, or any other ROM that may be specified via
    # Verilator or CW310 params).
    test_in_rom = True,
    deps = [
        "mask_rom.ld",
        ":mask_rom_epmp",
        "//hw/ip/aon_timer/data:aon_timer_regs",
        "//hw/ip/csrng/data:csrng_regs",
        "//hw/ip/edn/data:edn_regs",
        "//hw/ip/entropy_src/data:entropy_src_regs",
        "//hw/ip/flash_ctrl/data:flash_ctrl_regs",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/ip/sram_ctrl/data:sram_ctrl_regs",
        "//hw/top_earlgrey/ip/ast/data:ast_regs",
        "//hw/top_earlgrey/ip/pwrmgr/data/autogen:pwrmgr_regs",
        "//hw/top_earlgrey/ip/sensor_ctrl/data:sensor_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:linker_script",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device:info_sections",
        "//sw/device/lib:pinmux",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/crt",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing/test_framework",
        "//sw/device/silicon_creator/lib:epmp",
        "//sw/device/silicon_creator/lib:epmp_test_unlock",
        "//sw/device/silicon_creator/lib:irq_asm",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
        "//sw/device/silicon_creator/lib/base:static_critical.ld",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:uart",
    ],
)

cc_library(
    name = "primitive_bootstrap",
    srcs = ["primitive_bootstrap.c"],
    hdrs = ["primitive_bootstrap.h"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib:flash_ctrl",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:spi_device",
        "//sw/device/lib/testing/test_rom:bootstrap",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib:log",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
        "//sw/device/silicon_creator/lib/drivers:hmac",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:watchdog",
    ],
)

cc_library(
    name = "sigverify_keys_ptrs",
    hdrs = ["sigverify_keys_ptrs.h"],
)

cc_library(
    name = "mock_sigverify_keys_ptrs",
    testonly = True,
    hdrs = ["mock_sigverify_keys_ptrs.h"],
    deps = [
        ":sigverify_keys_ptrs",
        "//sw/device/silicon_creator/testing:mask_rom_test",
        "@googletest//:gtest",
    ],
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
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib:sigverify_internal",
        "//sw/device/silicon_creator/lib:sigverify_intf",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/silicon_creator/lib/drivers:rnd",
        "//sw/device/silicon_creator/mask_rom/keys:test_public_keys",
    ],
)

cc_test(
    name = "sigverify_keys_unittest",
    srcs = [
        "sigverify_keys.c",
        "sigverify_keys.h",
        "sigverify_keys_unittest.cc",
        "//sw/device/silicon_creator/lib:sigverify_src_for_keys_unittest",
    ],
    defines = ["OT_OFF_TARGET_TEST"],
    deps = [
        ":mock_sigverify_keys_ptrs",
        ":sigverify_keys_ptrs",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:hardened",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib:mock_sigverify",
        "//sw/device/silicon_creator/lib:sigverify_internal",
        "//sw/device/silicon_creator/lib:sigverify_intf",
        "//sw/device/silicon_creator/lib:sigverify_mod_exp_ibex",
        "//sw/device/silicon_creator/lib/drivers:mock_lifecycle",
        "//sw/device/silicon_creator/lib/drivers:mock_otp",
        "//sw/device/silicon_creator/lib/drivers:mock_rnd",
        "//sw/device/silicon_creator/mask_rom/keys:test_public_keys",
        "//sw/device/silicon_creator/testing:mask_rom_test",
        "@googletest//:gtest_main",
    ],
)

# MASK ROM E2E TESTS

# Bootup tests
BOOT_FAILURE_MSG = "BFV_[0-9a-z]{{8}}\nLCV_[0-9a-z]{{8}}\n"

opentitan_functest(
    name = "e2e_bootup_success",
    srcs = ["mask_rom_test.c"],
    signed = True,
    targets = [
        "verilator",
        "cw310",
    ],
    verilator = verilator_params(
        rom = ":mask_rom_sim_verilator_scr_vmem",
        tags = [
            "cpu:4",
            "failing_verilator",
        ],
    ),
)

# TODO: Add verilator test
opentitan_functest(
    name = "e2e_bootup_no_rom_ext_signature",
    srcs = ["mask_rom_test.c"],
    cw310 = cw310_params(
        args = [
            "--exec=\"console -q -t0\"",
            "--exec=\"bootstrap $(location {flash})\"",
            "console",
            "--timeout=3600",
            "--exit-success='{}'".format(BOOT_FAILURE_MSG),
            "--exit-failure='PASS!'",
        ],
    ),
    signed = False,
    targets = ["cw310"],
)
