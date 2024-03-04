# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "OPENTITAN_CPU")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "dt_api_ipgen",
    hdrs = [
        "dt_alert_handler.h",
        "dt_clkmgr.h",
        "dt_flash_ctrl.h",
        "dt_pinmux.h",
        "dt_pwrmgr.h",
        "dt_rstmgr.h",
        "dt_rv_plic.h",
    ],
    includes = ["."],
    deps = ["//sw/device/lib/devicetables:dt_api"],
)
