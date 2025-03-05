# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//hw/top:defs.bzl", "opentitan_if_ip", "opentitan_require_top", "opentitan_select_top")
load(
    "//rules/opentitan:defs.bzl",
    "OPENTITAN_CPU",
    "opentitan_binary",
    "opentitan_test",
)
load("//rules/opentitan:legacy.bzl", "legacy_rom_targets")
load("//rules:files.bzl", "output_groups")
load("//rules:linker.bzl", "ld_library")
load("@rules_pkg//pkg:mappings.bzl", "pkg_files")

package(default_visibility = ["//visibility:public"])

ld_library(
    name = "linker_script",
    script = "test_rom.ld",
    deps = [
        "//hw/top:top_ld",
        "//sw/device:info_sections",
        "//sw/device/lib/testing/test_framework:ottf_ld_top_config",
        "//sw/device/silicon_creator/lib/base:static_critical_sections",
    ],
)

opentitan_binary(
    name = "test_rom",
    exec_env = [
        "//hw/top_earlgrey:fpga_cw310",
        "//hw/top_earlgrey:fpga_cw305",
        "//hw/top_earlgrey:fpga_cw340",
        "//hw/top_earlgrey:sim_dv_base",
        "//hw/top_earlgrey:sim_verilator_base",
        "//hw/top_darjeeling:sim_dv_base",
    ],
    features = ["use_lld"],
    kind = "rom",
    linker_script = ":linker_script",
    deps = [
        ":test_rom_lib",
    ],
)

[
    # Generate targets with `sim_dv` and `sim_verilator` suffixes as expected
    # by dvsim.
    alias(
        name = "test_rom_{}".format(env),
        actual = ":test_rom",
    )
    for env in [
        "sim_dv",
        "sim_verilator",
    ]
]

# Create the legacy ROM target names so that existing splicing rules
# can find the test_rom VMEM files.
legacy_rom_targets(
    suffixes = [
        "fpga_cw310",
        "fpga_cw305",
        "fpga_cw340",
    ],
    target = "test_rom",
)

[
    filegroup(
        name = "test_rom_{}_hashfile".format(dev),
        srcs = [":test_rom"],
        output_group = "{}_hashfile".format(dev),
    )
    for dev in [
        "sim_dv",
        "sim_verilator",
        "fpga_cw305",
        "fpga_cw310",
        "fpga_cw340",
    ]
]

# TODO(#12905): Use a slightly hollowed out version of the silicon_creator bootstrap
# and other functions necessary to build the test_rom for the english breakfast top level.
cc_library(
    name = "english_breakfast_test_rom_lib",
    srcs = [
        "english_breakfast_fake_driver_funcs.c",
        "//sw/device/silicon_creator/lib/drivers:english_breakfast_test_rom_driver_srcs",
        "//sw/device/silicon_creator/rom:english_breakfast_test_rom_bootstrap_srcs",
    ],
    # This should be built only for english breakfast and skipped if using wildcards.
    tags = ["manual"],
    deps = [
        "//hw/top:flash_ctrl_c_regs",
        "//hw/top:gpio_c_regs",
        "//hw/top:spi_device_c_regs",
        "//hw/top:top_lib",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/dif:rstmgr_intf",
        "//sw/device/silicon_creator/lib:stack_utilization",
        "//sw/device/silicon_creator/lib/base:chip",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
    ],
)

cc_library(
    name = "earl_grey_test_rom_lib",
    deps = [
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/rom:bootstrap",
    ],
)

cc_library(
    name = "darjeeling_test_rom_lib",
    srcs = [
        "darjeeling_fake_driver_funcs.c",
    ],
    deps = [
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
    ],
)

alias(
    name = "target_test_rom_lib",
    actual = opentitan_select_top(
        {
            "darjeeling": ":darjeeling_test_rom_lib",
            "englishbreakfast": ":english_breakfast_test_rom_lib",
        },
        ":earl_grey_test_rom_lib",
    ),
    visibility = ["//visibility:private"],
)

# TODO(#12905): Use a slightly hollowed out version of the silicon_creator manifest
# implementation when building the test_rom for the english breakfast top level.
cc_library(
    name = "english_breakfast_test_rom_manifest",
    srcs = [
        "//sw/device/silicon_creator/lib:english_breakfast_test_rom_manifest_srcs",
        "//sw/device/silicon_creator/lib/drivers:english_breakfast_test_rom_driver_srcs",
    ],
    # This should be built only for english breakfast and skipped if using wildcards.
    tags = ["manual"],
    deps = [
        "//hw/top:flash_ctrl_c_regs",
        "//hw/top:spi_device_c_regs",
        "//hw/top:top_lib",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:multibits",
        "//sw/device/silicon_creator/lib:epmp_state",
        "//sw/device/silicon_creator/lib:error",
        "//sw/device/silicon_creator/lib:keymgr_binding",
        "//sw/device/silicon_creator/lib/base:chip",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
        "//sw/device/silicon_creator/lib/sigverify:ecdsa_p256_key",
        "//sw/device/silicon_creator/lib/sigverify:rsa_key",
        "//sw/device/silicon_creator/lib/sigverify:spx_key",
    ],
)

alias(
    name = "test_rom_manifest",
    actual = opentitan_select_top(
        {
            "englishbreakfast": ":english_breakfast_test_rom_manifest",
        },
        "//sw/device/silicon_creator/lib:manifest",
    ),
)

cc_library(
    name = "test_rom_lib",
    srcs = [
        "test_rom.c",
        "test_rom_start.S",
    ],
    local_defines = opentitan_if_ip(
        "flash_ctrl",
        ["HAS_FLASH_CTRL"],
        [],
    ) + opentitan_if_ip(
        "otp_ctrl",
        ["HAS_OTP_CTRL"],
        [],
    ) + opentitan_select_top(
        {
            "englishbreakfast": [],
        },
        ["HAS_RETENTION_RAM"],
    ),
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":target_test_rom_lib",
        ":test_rom_manifest",
        "//hw/top:ast_c_regs",
        "//hw/top:clkmgr_c_regs",
        "//hw/top:sram_ctrl_c_regs",
        "//hw/top:top_lib",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/crt",
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:rv_core_ibex",
        "//sw/device/lib/dif:spi_device",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:status",
        "//sw/device/silicon_creator/lib:chip_info",
        "//sw/device/silicon_creator/lib/base:sec_mmio",
        "//sw/device/silicon_creator/lib/base:static_critical",
    ] + opentitan_if_ip(
        "entropy_src",
        ["//hw/top:entropy_src_c_regs"],
        [],
    ) + opentitan_if_ip(
        "csrng",
        ["//hw/top:csrng_c_regs"],
        [],
    ) + opentitan_if_ip(
        "edn",
        ["//hw/top:edn_c_regs"],
        [],
    ) + opentitan_if_ip(
        "flash_ctrl",
        [
            "//hw/top:flash_ctrl_c_regs",
            "//hw/top:dt_flash_ctrl",
            "//sw/device/lib/dif:flash_ctrl",
            "//sw/device/lib/testing:flash_ctrl_testutils",
        ],
        [],
    ) + opentitan_if_ip(
        "sensor_ctrl",
        ["//hw/top:sensor_ctrl_c_regs"],
        [],
    ) + opentitan_if_ip(
        "otp_ctrl",
        [
            "//hw/top:otp_ctrl_c_regs",
            "//hw/top:dt_otp_ctrl",
        ],
        [],
    ),
)

opentitan_test(
    name = "test_rom_test",
    srcs = ["test_rom_test.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        "//hw/top_earlgrey:sim_dv": None,
        "//hw/top_earlgrey:sim_verilator": None,
    },
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

output_groups(
    name = "pre_package",
    testonly = True,
    srcs = [":test_rom"],
    groups = [
        "fpga_cw305_binary",
        "fpga_cw305_elf",
        "fpga_cw305_rom32",
        "fpga_cw305_mapfile",
        "fpga_cw310_binary",
        "fpga_cw310_elf",
        "fpga_cw310_rom",
        "fpga_cw310_mapfile",
        "fpga_cw340_binary",
        "fpga_cw340_elf",
        "fpga_cw340_rom",
        "fpga_cw340_mapfile",
        "sim_dv_elf",
        "sim_dv_rom",
        "sim_dv_logs",
        "sim_dv_mapfile",
        "sim_verilator_elf",
        "sim_verilator_rom",
        "sim_verilator_mapfile",
    ],
    target_compatible_with = opentitan_require_top("earlgrey"),
)

pkg_files(
    name = "package",
    testonly = True,
    srcs = [":pre_package"],
    prefix = "earlgrey/test_rom",
)
