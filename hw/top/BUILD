# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:autogen.bzl",
    "opentitan_ip_c_header",
    "opentitan_ip_dt_header",
    "opentitan_ip_rust_header",
    "opentitan_top_devicetables",
    "opentitan_top_dt_api",
)

package(default_visibility = ["//visibility:public"])

alias(
    name = "top",
    actual = "//hw/top_earlgrey",
)

alias(
    name = "top_lib",
    actual = "//hw/top_earlgrey/sw/autogen:top_earlgrey",
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
    "lc_ctrl",
    "otbn",
    "otp_ctrl",
    "pattgen",
    "pwm",
    "rom_ctrl",
    "rv_core_ibex",
    "rv_dm",
    "rv_timer",
    "spi_device",
    "spi_host",
    "sram_ctrl",
    "sysrst_ctrl",
    "uart",
    "usbdev",
    "ast",
    "sensor_ctrl",
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

opentitan_top_dt_api(
    name = "dt_api",
    top = ":top",
    deps = [":top_lib"],
)

[
    opentitan_ip_dt_header(
        name = "dt_{}".format(ip),
        ip = ip,
        top = ":top",
        deps = [":dt_api"],
    )
    for ip in IPS
]

cc_library(
    name = "dt_headers",
    srcs = [],
    deps = ["dt_{}".format(ip) for ip in IPS],
)

opentitan_top_devicetables(
    name = "devicetables",
    top = ":top",
    deps = [":dt_headers"],
)
