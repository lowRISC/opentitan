# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "drivers",
    srcs = ["drivers.c"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/top_darjeeling/sw/drivers:csrng",
        "//sw/top_darjeeling/sw/drivers:edn",
        "//sw/top_darjeeling/sw/drivers:entropy_src",
        "//sw/top_darjeeling/sw/drivers:flash_ctrl",
        "//sw/top_darjeeling/sw/drivers:keymgr",
        "//sw/top_darjeeling/sw/drivers:keymgr_dpe",
        "//sw/top_darjeeling/sw/drivers:kmac",
        "//sw/top_darjeeling/sw/drivers:lc_ctrl",
        "//sw/top_darjeeling/sw/drivers:otp_ctrl",
        "//sw/top_darjeeling/sw/drivers:pinmux",
        "//sw/top_darjeeling/sw/drivers:rstmgr",
        "//sw/top_darjeeling/sw/drivers:rv_core_ibex",
        "//sw/top_darjeeling/sw/drivers:sram_ctrl",
        "//sw/top_darjeeling/sw/drivers:uart",
    ],
)

cc_library(
    name = "fpga_cw305",
    srcs = ["device_fpga_cw305.c"],
    deps = [
        ":drivers",
        "//sw/device/silicon_creator/lib/drivers:ibex",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/silicon_creator:rom_print",
    ],
)

cc_library(
    name = "fpga_cw310",
    srcs = ["device_fpga_cw310.c"],
    deps = [
        ":drivers",
        "//sw/device/silicon_creator/lib/drivers:ibex",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/silicon_creator:rom_print",
    ],
)

cc_library(
    name = "sim_dv",
    srcs = ["device_sim_dv.c"],
    deps = [
        ":drivers",
        "//hw/ip/rv_core_ibex/data:rv_core_ibex_regs",
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/lib/sw/device/arch:device",
    ],
)

cc_library(
    name = "sim_verilator",
    srcs = ["device_sim_verilator.c"],
    deps = [
        ":drivers",
        "//hw/ip/rv_core_ibex/data:rv_core_ibex_regs",
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/lib/sw/device/arch:device",
    ],
)
