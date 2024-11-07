# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:autogen.bzl",
    "opentitan_ip_c_header",
    "opentitan_ip_rust_header",
)

package(default_visibility = ["//visibility:public"])

alias(
    name = "top",
    actual = "//hw/top_earlgrey",
)

# List of IPs for which to generate headers.
IPS = [
    "alert_handler",
    "flash_ctrl",
    "clkmgr",
    "rstmgr",
    "rv_plic",
    "pwrmgr",
    "pinmux",
    "adc_ctrl",
    "aes",
    "aon_timer",
    "csrng",
    "edn",
    "entropy_src",
    "gpio",
    "hmac",
    "i2c",
    "keymgr",
    "kmac",
]

[
    opentitan_ip_c_header(
        name = "{}_c_regs".format(ip),
        ip = ip,
        top = ":top",
    )
    for ip in IPS
]

[
    opentitan_ip_rust_header(
        name = "{}_rust_regs".format(ip),
        ip = ip,
        top = ":top",
    )
    for ip in IPS
]
