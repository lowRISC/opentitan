# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:doxygen.bzl", "doxygen_gather_all_package_cc")
load("//hw/top:defs.bzl", "opentitan_select_top")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "boot_stage",
    hdrs = ["boot_stage.h"],
)

cc_library(
    name = "boot_stage_rom",
    srcs = ["boot_stage_rom.c"],
    deps = [":boot_stage"],
)

cc_library(
    name = "boot_stage_rom_ext",
    srcs = ["boot_stage_rom_ext.c"],
    deps = [":boot_stage"],
)

cc_library(
    name = "boot_stage_owner",
    srcs = ["boot_stage_owner.c"],
    deps = [":boot_stage"],
)

cc_library(
    name = "device",
    hdrs = ["device.h"],
    deps = [
        "//sw/device/lib/base:macros",
    ],
)

cc_library(
    name = "fpga_cw305",
    srcs = ["device_fpga_cw305.c"],
    deps = [
        ":device",
        "//sw/device/lib/base:macros",
    ],
)

cc_library(
    name = "fpga_cw340",
    srcs = ["device_fpga_cw340.c"],
    deps = [
        ":device",
        "//sw/device/lib/base:macros",
    ],
)

cc_library(
    name = "silicon",
    srcs = ["device_silicon.c"],
    deps = [
        ":device",
    ],
)

cc_library(
    name = "sim_dv",
    # The DV clock frequencies differ per top; see hw/top_<top>/sw/dt/sim_dv.c.
    srcs = opentitan_select_top(
        {
            "darjeeling": ["device_sim_dv_darjeeling.c"],
        },
        ["device_sim_dv.c"],
    ),
    deps = [
        ":device",
        "//hw/top:rv_core_ibex_c_regs",
        "//hw/top/dt:rv_core_ibex",
    ],
)

cc_library(
    name = "sim_verilator",
    srcs = ["device_sim_verilator.c"],
    deps = [
        ":device",
        "//hw/top:rv_core_ibex_c_regs",
        "//hw/top/dt:rv_core_ibex",
    ],
)

cc_library(
    name = "sim_qemu",
    srcs = ["device_sim_qemu.c"],
    deps = [
        ":device",
        "//hw/top:rv_core_ibex_c_regs",
        "//hw/top/dt:rv_core_ibex",
        "//sw/device/lib/base:macros",
    ],
)

doxygen_gather_all_package_cc(
    name = "doxy_target",
)
