# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "OPENTITAN_CPU", "OPENTITAN_PLATFORM", "elf_to_scrambled_rom_vmem", "opentitan_rom_binary")
load("//rules:exclude_files.bzl", "exclude_files")
load("//rules:linker.bzl", "ld_library")
load(
    "//rules:opentitan_test.bzl",
    "manual_test",
    "opentitan_functest",
)
load("//rules:cross_platform.bzl", "dual_cc_library", "dual_inputs")
load("@rules_pkg//pkg:mappings.bzl", "pkg_files")

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
            "//sw/lib/sw/device/silicon_creator/testing:rom_test",
            "//sw/lib/sw/device/base:global_mock",
            "@googletest//:gtest",
        ],
        shared = [
            "//hw/top_darjeeling/sw/autogen:top_darjeeling",
            "//sw/top_darjeeling/sw/device/silicon_creator:manifest",
        ],
    ),
)

cc_library(
    name = "boot_policy",
    srcs = ["boot_policy.c"],
    hdrs = ["boot_policy.h"],
    deps = [
        ":boot_policy_ptrs",
        "//sw/lib/sw/device/base:hardened",
        "//sw/lib/sw/device/silicon_creator:error",
        "//sw/lib/sw/device/silicon_creator/base:chip",
        "//sw/top_darjeeling/sw/device/silicon_creator:boot_data",
        "//sw/top_darjeeling/sw/device/silicon_creator:manifest",
        "//sw/top_darjeeling/sw/device/silicon_creator:shutdown",
    ],
)

cc_test(
    name = "boot_policy_unittest",
    srcs = ["boot_policy_unittest.cc"],
    deps = [
        ":boot_policy",
        "//sw/lib/sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

ld_library(
    name = "linker_script",
    script = "rom.ld",
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling_memory",
        "//sw/device:info_sections",
    ],
)

ld_library(
    name = "base_rom_linker_script",
    script = "base_rom.ld",
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling_memory",
        "//sw/device:info_sections",
        "//sw/lib/sw/device/silicon_creator/base:static_critical_sections",
    ],
)

ld_library(
    name = "second_rom_linker_script",
    script = "second_rom.ld",
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling_memory",
        "//sw/device:info_sections",
        "//sw/lib/sw/device/silicon_creator/base:static_critical_sections",
    ],
)

cc_library(
    name = "rom_without_keys",
    srcs = [
        "rom_start.S",
    ],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":linker_script",
        ":rom_common",
        ":rom_epmp",
        "//hw/ip/aon_timer/data:aon_timer_regs",
        "//hw/ip/csrng/data:csrng_regs",
        "//hw/ip/edn/data:edn_regs",
        "//hw/ip/gpio/data:gpio_regs",
        "//hw/ip/lc_ctrl/data:lc_ctrl_regs",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/ip/rv_core_ibex/data:rv_core_ibex_regs",
        "//hw/ip/sram_ctrl/data:sram_ctrl_regs",
        "//hw/top_darjeeling/ip/ast/data:ast_regs",
        "//hw/top_darjeeling/ip/clkmgr/data/autogen:clkmgr_regs",
        "//hw/top_darjeeling/ip/pinmux/data/autogen:pinmux_regs",
        "//hw/top_darjeeling/ip/pwrmgr/data/autogen:pwrmgr_regs",
        "//hw/top_darjeeling/ip/rstmgr/data/autogen:rstmgr_regs",
        "//hw/top_darjeeling/ip/sensor_ctrl/data:sensor_ctrl_regs",
        "//sw/lib/sw/device/base:hardened",
        "//sw/lib/sw/device/base:multibits",
        "//sw/lib/sw/device/silicon_creator/base:chip",
    ],
    alwayslink = True,
)

cc_library(
    name = "base_rom_without_keys",
    srcs = [
        "base_rom_start.S",
    ],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":base_rom",
        ":base_rom_linker_script",
        "//hw/ip/csrng/data:csrng_regs",
        "//hw/ip/edn/data:edn_regs",
        "//hw/ip/entropy_src/data:entropy_src_regs",
        "//hw/ip/gpio/data:gpio_regs",
        "//hw/ip/lc_ctrl/data:lc_ctrl_regs",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/ip/rv_core_ibex/data:rv_core_ibex_regs",
        "//hw/ip/sram_ctrl/data:sram_ctrl_regs",
        "//hw/top_darjeeling/ip/ast/data:ast_regs",
        "//hw/top_darjeeling/ip/clkmgr/data/autogen:clkmgr_regs",
        "//hw/top_darjeeling/ip/pinmux/data/autogen:pinmux_regs",
        "//hw/top_darjeeling/ip/pwrmgr/data/autogen:pwrmgr_regs",
        "//hw/top_darjeeling/ip/sensor_ctrl/data:sensor_ctrl_regs",
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/lib/sw/device/base:hardened",
        "//sw/lib/sw/device/base:multibits",
        "//sw/lib/sw/device/silicon_creator/base:chip",
    ],
    alwayslink = True,
)

cc_library(
    name = "second_rom_without_keys",
    srcs = [
        "second_rom_start.S",
    ],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":second_rom",
        ":second_rom_epmp",
        ":second_rom_linker_script",
        "//hw/ip/aon_timer/data:aon_timer_regs",
        "//hw/ip/csrng/data:csrng_regs",
        "//hw/ip/edn/data:edn_regs",
        "//hw/ip/entropy_src/data:entropy_src_regs",
        "//hw/ip/gpio/data:gpio_regs",
        "//hw/ip/lc_ctrl/data:lc_ctrl_regs",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/ip/rv_core_ibex/data:rv_core_ibex_regs",
        "//hw/ip/sram_ctrl/data:sram_ctrl_regs",
        "//hw/top_darjeeling/ip/ast/data:ast_regs",
        "//hw/top_darjeeling/ip/clkmgr/data/autogen:clkmgr_regs",
        "//hw/top_darjeeling/ip/pinmux/data/autogen:pinmux_regs",
        "//hw/top_darjeeling/ip/pwrmgr/data/autogen:pwrmgr_regs",
        "//hw/top_darjeeling/ip/sensor_ctrl/data:sensor_ctrl_regs",
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/lib/sw/device/base:hardened",
        "//sw/lib/sw/device/base:multibits",
        "//sw/lib/sw/device/silicon_creator/base:chip",
    ],
    alwayslink = True,
)

cc_library(
    name = "rom_common",
    srcs = [
        "rom.c",
        "rom.h",
    ],
    deps = [
        ":boot_policy",
        ":bootstrap",
        ":rom_epmp",
        ":sigverify_keys",
        ":sigverify_keys_rsa",
        ":sigverify_keys_spx",
        "//hw/ip/aon_timer/data:aon_timer_regs",
        "//sw/device/silicon_creator/lib/drivers:alert",
        "//sw/device/silicon_creator/lib/drivers:ast",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:ibex",
        "//sw/device/silicon_creator/lib/drivers:keymgr",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/silicon_creator/lib/drivers:pinmux",
        "//sw/device/silicon_creator/lib/drivers:pwrmgr",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/drivers:rnd",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
        "//sw/device/silicon_creator/lib/drivers:uart",
        "//sw/device/silicon_creator/lib/drivers:watchdog",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:csr",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:stdasm",
        "//sw/lib/sw/device/crt",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/lib/sw/device/silicon_creator:cfi",
        "//sw/lib/sw/device/silicon_creator:epmp_state",
        "//sw/lib/sw/device/silicon_creator:error",
        "//sw/lib/sw/device/silicon_creator/base:chip",
        "//sw/lib/sw/device/silicon_creator/base:sec_mmio",
        "//sw/lib/sw/device/silicon_creator/base:static_critical",
        "//sw/lib/sw/device/silicon_creator/sigverify",
        "//sw/top_darjeeling/sw/device/silicon_creator:irq_asm",
        "//sw/top_darjeeling/sw/device/silicon_creator:manifest",
        "//sw/top_darjeeling/sw/device/silicon_creator:shutdown",
    ],
)

cc_library(
    name = "base_rom",
    srcs = [
        "base_rom.c",
        "base_rom.h",
    ],
    deps = [
        ":base_rom_epmp",
        ":sigverify_keys",
        ":sigverify_keys_rsa",
        ":sigverify_keys_spx",
        "//sw/device/silicon_creator/lib/drivers:alert",
        "//sw/device/silicon_creator/lib/drivers:ast",
        "//sw/device/silicon_creator/lib/drivers:ibex",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/silicon_creator/lib/drivers:pinmux",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/drivers:rnd",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
        "//sw/device/silicon_creator/lib/drivers:uart",
        "//sw/device/silicon_creator/lib/drivers:watchdog",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:csr",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:stdasm",
        "//sw/lib/sw/device/crt",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/lib/sw/device/silicon_creator:cfi",
        "//sw/lib/sw/device/silicon_creator:dbg_print",
        "//sw/lib/sw/device/silicon_creator:epmp_state",
        "//sw/lib/sw/device/silicon_creator:error",
        "//sw/lib/sw/device/silicon_creator:rom_patch",
        "//sw/lib/sw/device/silicon_creator/base:chip",
        "//sw/lib/sw/device/silicon_creator/base:sec_mmio",
        "//sw/lib/sw/device/silicon_creator/base:static_critical",
        "//sw/lib/sw/device/silicon_creator/sigverify",
        "//sw/top_darjeeling/sw/device/silicon_creator:irq_asm",
        "//sw/top_darjeeling/sw/device/silicon_creator:shutdown",
    ],
)

cc_library(
    name = "second_rom",
    srcs = [
        "second_rom.c",
        "second_rom.h",
    ],
    deps = [
        ":boot_policy",
        ":bootstrap",
        ":second_rom_epmp",
        ":sigverify_keys",
        ":sigverify_keys_rsa",
        ":sigverify_keys_spx",
        "//hw/ip/aon_timer/data:aon_timer_regs",
        "//sw/device/silicon_creator/lib/drivers:alert",
        "//sw/device/silicon_creator/lib/drivers:ast",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:ibex",
        "//sw/device/silicon_creator/lib/drivers:keymgr",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/silicon_creator/lib/drivers:pinmux",
        "//sw/device/silicon_creator/lib/drivers:pwrmgr",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/drivers:rnd",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
        "//sw/device/silicon_creator/lib/drivers:uart",
        "//sw/device/silicon_creator/lib/drivers:watchdog",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:csr",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:stdasm",
        "//sw/lib/sw/device/crt",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/lib/sw/device/silicon_creator:cfi",
        "//sw/lib/sw/device/silicon_creator:dbg_print",
        "//sw/lib/sw/device/silicon_creator:epmp_state",
        "//sw/lib/sw/device/silicon_creator:error",
        "//sw/lib/sw/device/silicon_creator/base:chip",
        "//sw/lib/sw/device/silicon_creator/base:sec_mmio",
        "//sw/lib/sw/device/silicon_creator/base:static_critical",
        "//sw/lib/sw/device/silicon_creator/sigverify",
        "//sw/top_darjeeling/sw/device/silicon_creator:irq_asm",
        "//sw/top_darjeeling/sw/device/silicon_creator:manifest",
        "//sw/top_darjeeling/sw/device/silicon_creator:shutdown",
    ],
)

opentitan_rom_binary(
    name = "rom_with_fake_keys",
    testonly = True,
    mode = "base-rom",
    deps = [
        ":rom_without_keys",
        "//sw/device/silicon_creator/rom/keys/fake/rsa",
        "//sw/device/silicon_creator/rom/keys/fake/spx",
    ],
)

opentitan_rom_binary(
    name = "rom_with_real_keys_from_src",
    mode = "base-rom",
    deps = [
        ":rom_without_keys",
        "//sw/device/silicon_creator/rom/keys/real/rsa",
        "//sw/device/silicon_creator/rom/keys/real/spx",
    ],
)

opentitan_rom_binary(
    name = "base_rom_with_fake_keys",
    testonly = True,
    mode = "base-rom",
    deps = [
        ":base_rom_without_keys",
        "//sw/device/silicon_creator/rom/keys/fake/rsa",
        "//sw/device/silicon_creator/rom/keys/fake/spx",
    ],
)

opentitan_rom_binary(
    name = "base_rom_with_real_keys_from_src",
    mode = "base-rom",
    deps = [
        ":base_rom_without_keys",
        "//sw/device/silicon_creator/rom/keys/real/rsa",
        "//sw/device/silicon_creator/rom/keys/real/spx",
    ],
)

opentitan_rom_binary(
    name = "second_rom_with_fake_keys",
    testonly = True,
    mode = "second-rom",
    deps = [
        ":second_rom_without_keys",
        "//sw/device/silicon_creator/rom/keys/fake/rsa",
        "//sw/device/silicon_creator/rom/keys/fake/spx",
    ],
)

opentitan_rom_binary(
    name = "second_rom_with_real_keys_from_src",
    mode = "second-rom",
    deps = [
        ":second_rom_without_keys",
        "//sw/device/silicon_creator/rom/keys/real/rsa",
        "//sw/device/silicon_creator/rom/keys/real/spx",
    ],
)

_ROM_DEVICES = [
    "sim_dv",
    "sim_verilator",
    "fpga_cw310",
]

[
    elf_to_scrambled_rom_vmem(
        name = "rom_with_real_keys_{}_scr_vmem".format(dev),
        srcs = ["//sw/device/silicon_creator/rom/binaries:rom_with_real_keys_{}.elf".format(dev)],
        mode = "base-rom",
        platform = OPENTITAN_PLATFORM,
    )
    for dev in _ROM_DEVICES
]

# We use a filegroup here that points to the scrambled ROM VMEM file because
# dvsim invokes a `bazel cquery ...` command to locate the ROM VMEM file it
# built using the device-specific label name.
[
    filegroup(
        name = "rom_with_real_keys_{}".format(dev),
        srcs = [":rom_with_real_keys_{}_scr_vmem".format(dev)],
    )
    for dev in _ROM_DEVICES
]

filegroup(
    name = "rom_with_real_keys",
    srcs = [
        ":rom_with_real_keys_fpga_cw310_scr_vmem",
        ":rom_with_real_keys_sim_dv_scr_vmem",
        ":rom_with_real_keys_sim_verilator_scr_vmem",
    ],
)

cc_library(
    name = "rom_epmp",
    srcs = [
        "rom_epmp.c",
        "rom_epmp_init.S",
    ],
    hdrs = ["rom_epmp.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:csr",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/silicon_creator:epmp_state",
    ],
)

cc_library(
    name = "base_rom_epmp",
    srcs = [
        "base_rom_epmp.c",
        "base_rom_epmp_init.S",
    ],
    hdrs = ["base_rom_epmp.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/lib/sw/device/silicon_creator:epmp_state",
    ],
)

cc_library(
    name = "second_rom_epmp",
    srcs = [
        "second_rom_epmp.c",
    ],
    hdrs = ["second_rom_epmp.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:csr",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/silicon_creator:dbg_print",
        "//sw/lib/sw/device/silicon_creator:epmp_state",
    ],
)

opentitan_functest(
    name = "rom_epmp_test",
    srcs = [
        "rom_epmp_test.c",
    ],
    linkopts = [
        "-Wl,--defsym=rom_test=1",
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
        ":rom_without_keys",
        "//hw/top_darjeeling/ip/flash_ctrl/data/autogen:flash_ctrl_regs",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:status",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:uart",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:abs_mmio",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:csr",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/crt",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/runtime:log",
        "//sw/lib/sw/device/silicon_creator:epmp_state",
        "//sw/lib/sw/device/silicon_creator:epmp_test_unlock",
        "//sw/lib/sw/device/silicon_creator/base:chip",
        "//sw/lib/sw/device/silicon_creator/base:sec_mmio",
        "//sw/lib/sw/device/silicon_creator/base:static_critical",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/device/silicon_creator:irq_asm",
        "//sw/top_darjeeling/sw/dif:pinmux",
        "//sw/top_darjeeling/sw/dif:sram_ctrl",
        "//sw/top_darjeeling/sw/test/utils:pinmux_testutils",
    ],
)

filegroup(
    name = "english_breakfast_test_rom_bootstrap_srcs",
    srcs = [
        "bootstrap.c",
        "bootstrap.h",
    ],
)

cc_library(
    name = "bootstrap",
    srcs = ["bootstrap.c"],
    hdrs = ["bootstrap.h"],
    deps = [
        "//hw/ip/gpio/data:gpio_regs",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_darjeeling/ip/flash_ctrl/data/autogen:flash_ctrl_regs",
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/silicon_creator/lib/drivers:ctn_sram",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
        "//sw/device/silicon_creator/lib/drivers:spi_device",
        "//sw/lib/sw/device/base:abs_mmio",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:hardened",
        "//sw/lib/sw/device/silicon_creator:error",
        "//sw/lib/sw/device/silicon_creator/base:chip",
    ],
)

cc_test(
    name = "bootstrap_unittest",
    srcs = ["bootstrap_unittest.cc"],
    deps = [
        ":bootstrap",
        "//hw/ip/gpio/data:gpio_regs",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_darjeeling/ip/flash_ctrl/data/autogen:flash_ctrl_regs",
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "sigverify_keys",
    srcs = [
        "sigverify_keys.c",
        "sigverify_keys_rsa.h",
        "sigverify_keys_spx.h",
    ],
    hdrs = [
        "sigverify_keys.h",
    ],
    deps = [
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/silicon_creator/lib/drivers:rnd",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:hardened",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/silicon_creator:error",
        "//sw/lib/sw/device/silicon_creator/sigverify:rsa_key",
        "//sw/lib/sw/device/silicon_creator/sigverify:spx_key",
    ],
)

cc_library(
    name = "sigverify_keys_rsa",
    srcs = [
        "sigverify_keys_rsa.c",
    ],
    hdrs = [
        "sigverify_keys_rsa.h",
    ],
    deps = [
        ":sigverify_keys",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/silicon_creator:error",
        "//sw/lib/sw/device/silicon_creator/sigverify:rsa_key",
    ],
)

cc_library(
    name = "sigverify_keys_spx",
    srcs = [
        "sigverify_keys_spx.c",
    ],
    hdrs = [
        "sigverify_keys_spx.h",
    ],
    deps = [
        ":sigverify_keys",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/silicon_creator:error",
        "//sw/lib/sw/device/silicon_creator/sigverify",
        "//sw/lib/sw/device/silicon_creator/sigverify:spx_key",
    ],
)

cc_test(
    name = "sigverify_keys_unittest",
    srcs = ["sigverify_keys_unittest.cc"],
    deps = [
        ":sigverify_keys",
        ":sigverify_keys_rsa",
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/lib/sw/device/silicon_creator/testing:rom_test",
        "@googletest//:gtest_main",
    ],
)

[exclude_files(
    name = "pre_package_{}".format(authenticity),
    testonly = testonly,
    srcs = [":rom_with_{}_keys".format(authenticity)],
    exclude_suffix = [
        ".ll",
        ".i",
        ".s",
    ],
) for authenticity, testonly in (
    ("fake", True),
    # FIXME: remove testonly after adding the real keys
    ("real", True),
)]

[pkg_files(
    name = "package_{}".format(authenticity),
    testonly = testonly,
    srcs = [":pre_package_{}".format(authenticity)],
    prefix = "darjeeling/rom",
) for authenticity, testonly in (
    ("fake", True),
    # FIXME: remove testonly after adding the real keys
    ("real", True),
)]

manual_test(
    name = "manual_test",
    tags = [
        "manual",
        "no-cache",
    ],
    testplan = "//sw/device/silicon_creator/rom/data:rom_manual_testplan.hjson",
)

genrule(
    name = "rom_hashes",
    testonly = True,
    srcs = [
        ":rom_with_real_keys_from_src",
    ],
    outs = ["rom_hashes.txt"],
    cmd = """
        echo "SHA256 of rom with real keys" > $@
	for f in $(locations :rom_with_real_keys_from_src); do
	    if [[ "$$f" == *bin ]]; then
	        name=$$(basename $$f)
		echo $$f >> $@
		size=$$(stat -L -c %s $$f)
		full=$$(sha256sum $$f | cut -f1 -d' ')
		without_chip_info=$$(head -c -12 $$f | sha256sum | cut -f1 -d' ')
		code=$$(echo $$without_chip_info | sed -E s'/(.{8})(.{8})(.{8})(.{8})(.{8})(.{8})(.{8})(.{8})/0x\\8,0x\\7,0x\\6,0x\\5,0x\\4,0x\\3,0x\\2,0x\\1,/g')

		echo "              size: $$size" >> $@
		echo "     complete hash: $$full" >> $@
		echo " without chip_info: $$without_chip_info" >> $@
		echo "w/o chip_info le32: $$code" >> $@
		echo >> $@
	    fi
	done
    """,
)
