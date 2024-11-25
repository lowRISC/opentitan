# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# List of IPs for which to generate headers.
OPENTITAN_ALL_IPS = [
    "adc_ctrl",
    "aes",
    "alert_handler",
    "aon_timer",
    "ast",
    "clkmgr",
    "csrng",
    "dma",
    "edn",
    "entropy_src",
    "flash_ctrl",
    "gpio",
    "hmac",
    "i2c",
    "keymgr",
    "keymgr_dpe",
    "kmac",
    "lc_ctrl",
    "mbx",
    "otbn",
    "otp_ctrl",
    "pattgen",
    "pinmux",
    "pwm",
    "pwrmgr",
    "rom_ctrl",
    "rstmgr",
    "rv_core_ibex",
    "rv_dm",
    "rv_plic",
    "rv_timer",
    "sensor_ctrl",
    "spi_device",
    "spi_host",
    "sram_ctrl",
    "sysrst_ctrl",
    "uart",
    "usbdev",
]

def opentitan_require_top(top_name):
    """
    Use this macro in the `target_compatible_with` attribute of
    a rule to express the requirement that this target should only
    be considered for a particular top.

    Example:
    cc_library(
      name = "bla",
      ...
      target_compatible_with = opentitan_require_top("earlgrey"),
    )
    """
    return select({
        "//hw/top:is_{}".format(top_name): [],
        "//conditions:default": ["@platforms//:incompatible"],
    })
