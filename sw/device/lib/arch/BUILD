# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

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
        "//sw/device/silicon_creator/lib:rom_print",
        "//sw/device/silicon_creator/lib/drivers:ibex",
    ],
)

cc_library(
    name = "fpga_cw310",
    srcs = ["device_fpga_cw310.c"],
    deps = [
        ":device",
        "//sw/device/lib/base:macros",
        "//sw/device/silicon_creator/lib:rom_print",
        "//sw/device/silicon_creator/lib/drivers:ibex",
    ],
)

cc_library(
    name = "fpga_cw340",
    srcs = ["device_fpga_cw340.c"],
    deps = [
        ":device",
        "//sw/device/lib/base:macros",
        "//sw/device/silicon_creator/lib:rom_print",
        "//sw/device/silicon_creator/lib/drivers:ibex",
    ],
)

cc_library(
    name = "sim_dv",
    srcs = ["device_sim_dv.c"],
    deps = [
        ":device",
        "//hw/ip/rv_core_ibex/data:rv_core_ibex_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
    ],
)

cc_library(
    name = "sim_verilator",
    srcs = ["device_sim_verilator.c"],
    deps = [
        ":device",
        "//hw/ip/rv_core_ibex/data:rv_core_ibex_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
    ],
)
