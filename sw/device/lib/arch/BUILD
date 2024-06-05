# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

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
        "//sw/device/silicon_creator/lib/drivers:ibex",
        "//sw/device/silicon_creator/lib/drivers:uart",
    ],
)

cc_library(
    name = "fpga_cw310",
    srcs = ["device_fpga_cw310.c"],
    deps = [
        ":device",
        "//sw/device/lib/base:macros",
        "//sw/device/silicon_creator/lib/drivers:ibex",
        "//sw/device/silicon_creator/lib/drivers:uart",
    ],
)

cc_library(
    name = "fpga_cw340",
    srcs = ["device_fpga_cw340.c"],
    deps = [
        ":device",
        "//sw/device/lib/base:macros",
        "//sw/device/silicon_creator/lib/drivers:ibex",
        "//sw/device/silicon_creator/lib/drivers:uart",
    ],
)

cc_library(
    name = "silicon",
    srcs = ["device_silicon.c"],
    deps = [
        ":device",
        "//hw/ip/rv_core_ibex/data:rv_core_ibex_c_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
    ],
)

cc_library(
    name = "sim_dv",
    srcs = ["device_sim_dv.c"],
    deps = [
        ":device",
        "//hw/ip/rv_core_ibex/data:rv_core_ibex_c_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
    ],
)

cc_library(
    name = "sim_verilator",
    srcs = ["device_sim_verilator.c"],
    deps = [
        ":device",
        "//hw/ip/rv_core_ibex/data:rv_core_ibex_c_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
    ],
)
