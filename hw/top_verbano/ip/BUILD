# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "rtl_files",
    srcs = glob(["**"]) + [
        "//hw/top_verbano/ip/ast:rtl_files",
        "//hw/top_verbano/ip/sensor_ctrl:rtl_files",
        "//hw/top_verbano/ip/xbar:rtl_files",
        "//hw/top_verbano/ip/xbar_main:rtl_files",
        "//hw/top_verbano/ip/xbar_peri:rtl_files",
        "//hw/top_verbano/ip_autogen/alert_handler:rtl_files",
        "//hw/top_verbano/ip_autogen/clkmgr:rtl_files",
        "//hw/top_verbano/ip_autogen/flash_ctrl:rtl_files",
        "//hw/top_verbano/ip_autogen/gpio:rtl_files",
        "//hw/top_verbano/ip_autogen/otp_ctrl:rtl_files",
        "//hw/top_verbano/ip_autogen/pinmux:rtl_files",
        "//hw/top_verbano/ip_autogen/pwm:rtl_files",
        "//hw/top_verbano/ip_autogen/pwrmgr:rtl_files",
        "//hw/top_verbano/ip_autogen/rstmgr:rtl_files",
        "//hw/top_verbano/ip_autogen/rv_core_ibex:rtl_files",
        "//hw/top_verbano/ip_autogen/rv_plic:rtl_files",
    ],
)

filegroup(
    name = "doc_files",
    srcs = [
        "//hw/top_verbano/ip/ast:doc_files",
        "//hw/top_verbano/ip/sensor_ctrl:doc_files",
        "//hw/top_verbano/ip/xbar:doc_files",
    ],
)
