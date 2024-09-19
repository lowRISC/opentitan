# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//hw/top:alias_top.bzl", "alias_top", "alias_ip_sw")

# This directory (hw/top/) exists only to forward various standard top-specific
# items to the right top so they can be refered to in a top-agnostic way.
# At the moment, this is hardcoded for ealrgrey and englishbreakfast.

alias_top(
    name = "top_lib",
    earlgrey = "//hw/top_earlgrey/sw/autogen:top_earlgrey",
)

alias_top(
    name = "dt_api",
    earlgrey = "//hw/top_earlgrey/sw/autogen:dt_api",
)

alias_top(
    name = "devicetables",
    earlgrey = "//hw/top_earlgrey/sw/autogen:devicetables",
)

alias_ip_sw(
    name = "sensor_ctrl",
    earlgrey = "//hw/top_earlgrey/ip/sensor_ctrl/data:sensor_ctrl",
)

alias_ip_sw(
    name = "ast",
    earlgrey = "//hw/top_earlgrey/ip/ast/data:ast",
)

IP_AUTOGEN = [
    "flash_ctrl",
    "clkmgr",
    "rstmgr",
    "pwrmgr",
]

[
    alias_ip_sw(
        name = "{}".format(ipname),
        earlgrey = "//hw/top_earlgrey/ip_autogen/{}:{}".format(ipname, ipname),
    )
    for ipname in IP_AUTOGEN
]

# The following IPs do not follow the regular scheme above for earlgrey and should ideally be made more uniform.
alias_ip_sw(
    name = "rv_plic",
    earlgrey = "//hw/top_earlgrey:rv_plic",
)

alias_ip_sw(
    name = "alert_handler",
    earlgrey = "//hw/top_earlgrey:alert_handler",
)

alias_ip_sw(
    name = "pinmux",
    earlgrey = "//hw/top_earlgrey/ip/pinmux/data/autogen:pinmux",
)
