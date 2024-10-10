# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------#
# PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
# util/topgen.py -t hw/top_englishbreakfast/data/top_englishbreakfast.hjson
# -o hw/top_englishbreakfast

load("//rules:linker.bzl", "ld_library")
load("//rules:autogen.bzl", "autogen_top_dt")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "top_englishbreakfast",
    srcs = [
        "top_englishbreakfast.c",
    ],
    hdrs = [
        "top_englishbreakfast.h",
        "top_englishbreakfast_memory.h",
    ],
)

ld_library(
    name = "top_englishbreakfast_memory",
    includes = ["top_englishbreakfast_memory.ld"],
)

# This macro will generate two targets:
# - dt_api: this is a library that all DT-headers depends on
# - devicetables: this is the DT library that contains the top tables.
autogen_top_dt(
    topname = "top_englishbreakfast",
    # Top cfg.
    top_gen_cfg = "//hw/top_englishbreakfast/data:autogen/top_englishbreakfast.gen.hjson",
    # IP to hjson map.
    ip_to_hjson = {
        "//hw/ip/aes/data:aes.hjson": "aes",
        "//hw/ip/aon_timer/data:aon_timer.hjson": "aon_timer",
        "//hw/top_earlgrey/ip/ast/data:ast.hjson": "ast",
        "//hw/top_englishbreakfast/ip_autogen/clkmgr:data/clkmgr.hjson": "clkmgr",
        "//hw/top_englishbreakfast/ip_autogen/flash_ctrl:data/flash_ctrl.hjson": "flash_ctrl",
        "//hw/ip/gpio/data:gpio.hjson": "gpio",
        "//hw/top_englishbreakfast/ip/pinmux/data/autogen:pinmux.hjson": "pinmux",
        "//hw/top_englishbreakfast/ip_autogen/pwrmgr:data/pwrmgr.hjson": "pwrmgr",
        "//hw/ip/rom_ctrl/data:rom_ctrl.hjson": "rom_ctrl",
        "//hw/top_englishbreakfast/ip_autogen/rstmgr:data/rstmgr.hjson": "rstmgr",
        "//hw/ip/rv_core_ibex/data:rv_core_ibex.hjson": "rv_core_ibex",
        "//hw/top_englishbreakfast/ip_autogen:rv_plic/data/rv_plic.hjson": "rv_plic",
        "//hw/ip/rv_timer/data:rv_timer.hjson": "rv_timer",
        "//hw/ip/spi_device/data:spi_device.hjson": "spi_device",
        "//hw/ip/spi_host/data:spi_host.hjson": "spi_host",
        "//hw/ip/sram_ctrl/data:sram_ctrl.hjson": "sram_ctrl",
        "//hw/ip/uart/data:uart.hjson": "uart",
        "//hw/ip/usbdev/data:usbdev.hjson": "usbdev",
    },
    # Toplevel library.
    top_lib = ":top_englishbreakfast",
    # DT IP headers: we point to a target that has to be manually created at the moment.
    dt_ip_deps = ["//hw/top_englishbreakfast:dt_headers"],
)

filegroup(
    name = "all_files",
    srcs = glob(["**"]),
)
