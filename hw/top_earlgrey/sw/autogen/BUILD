# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------#
# PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
# util/topgen.py -t hw/top_earlgrey/data/top_earlgrey.hjson
# -o hw/top_earlgrey

load("//rules:linker.bzl", "ld_library")
load("//rules:autogen.bzl", "autogen_top_dt")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "top_earlgrey",
    srcs = [
        "top_earlgrey.c",
    ],
    hdrs = [
        "top_earlgrey.h",
        "top_earlgrey_memory.h",
    ],
)

ld_library(
    name = "top_earlgrey_memory",
    includes = ["top_earlgrey_memory.ld"],
)

# This macro will generate two targets:
# - dt_api: this is a library that all DT-headers depends on
# - devicetables: this is the DT library that contains the top tables.
autogen_top_dt(
    topname = "top_earlgrey",
    # Top cfg.
    top_gen_cfg = "//hw/top_earlgrey/data:autogen/top_earlgrey.gen.hjson",
    # IP to hjson map.
    ip_to_hjson = {
        "//hw/ip/adc_ctrl/data:adc_ctrl.hjson": "adc_ctrl",
        "//hw/ip/aes/data:aes.hjson": "aes",
        "//hw/top_earlgrey:ip_autogen/alert_handler/data/alert_handler.hjson": "alert_handler",
        "//hw/ip/aon_timer/data:aon_timer.hjson": "aon_timer",
        "//hw/top_earlgrey/ip/ast/data:ast.hjson": "ast",
        "//hw/top_earlgrey/ip_autogen/clkmgr:data/clkmgr.hjson": "clkmgr",
        "//hw/ip/csrng/data:csrng.hjson": "csrng",
        "//hw/ip/edn/data:edn.hjson": "edn",
        "//hw/ip/entropy_src/data:entropy_src.hjson": "entropy_src",
        "//hw/top_earlgrey/ip_autogen/flash_ctrl:data/flash_ctrl.hjson": "flash_ctrl",
        "//hw/ip/gpio/data:gpio.hjson": "gpio",
        "//hw/ip/hmac/data:hmac.hjson": "hmac",
        "//hw/ip/i2c/data:i2c.hjson": "i2c",
        "//hw/ip/keymgr/data:keymgr.hjson": "keymgr",
        "//hw/ip/kmac/data:kmac.hjson": "kmac",
        "//hw/ip/lc_ctrl/data:lc_ctrl.hjson": "lc_ctrl",
        "//hw/ip/otbn/data:otbn.hjson": "otbn",
        "//hw/ip/otp_ctrl/data:otp_ctrl.hjson": "otp_ctrl",
        "//hw/ip/pattgen/data:pattgen.hjson": "pattgen",
        "//hw/top_earlgrey/ip/pinmux/data/autogen:pinmux.hjson": "pinmux",
        "//hw/ip/pwm/data:pwm.hjson": "pwm",
        "//hw/top_earlgrey/ip_autogen/pwrmgr:data/pwrmgr.hjson": "pwrmgr",
        "//hw/ip/rom_ctrl/data:rom_ctrl.hjson": "rom_ctrl",
        "//hw/top_earlgrey/ip_autogen/rstmgr:data/rstmgr.hjson": "rstmgr",
        "//hw/ip/rv_core_ibex/data:rv_core_ibex.hjson": "rv_core_ibex",
        "//hw/ip/rv_dm/data:rv_dm.hjson": "rv_dm",
        "//hw/top_earlgrey:ip_autogen/rv_plic/data/rv_plic.hjson": "rv_plic",
        "//hw/ip/rv_timer/data:rv_timer.hjson": "rv_timer",
        "//hw/top_earlgrey/ip/sensor_ctrl/data:sensor_ctrl.hjson": "sensor_ctrl",
        "//hw/ip/spi_device/data:spi_device.hjson": "spi_device",
        "//hw/ip/spi_host/data:spi_host.hjson": "spi_host",
        "//hw/ip/sram_ctrl/data:sram_ctrl.hjson": "sram_ctrl",
        "//hw/ip/sysrst_ctrl/data:sysrst_ctrl.hjson": "sysrst_ctrl",
        "//hw/ip/uart/data:uart.hjson": "uart",
        "//hw/ip/usbdev/data:usbdev.hjson": "usbdev",
    },
    # Toplevel library.
    top_lib = ":top_earlgrey",
    # DT IP headers: we point to a target that has to be manually created at the moment.
    dt_ip_deps = ["//hw/top_earlgrey:dt_headers"],
)

filegroup(
    name = "all_files",
    srcs = glob(["**"]),
)
