# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:util.bzl", "flatten")
load("//hw/top:defs.bzl", "opentitan_if_ip", "opentitan_require_top")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "base",
    srcs = ["dif_base.c"],
    hdrs = ["dif_base.h"],
    deps = [
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base/internal:status",
    ],
)

cc_library(
    name = "test_base",
    testonly = True,
    hdrs = ["dif_test_base.h"],
    deps = [
        ":base",
        "@googletest//:gtest",
    ],
)

DIFS = {
    "adc_ctrl": {},
    "aes": {},
    "alert_handler": {},
    "aon_timer": {},
    "clkmgr": {},
    "csrng": {
        "deps": [":csrng_shared"],
    },
    "dma": {},
    "edn": {
        "deps": [":csrng_shared"],
    },
    "entropy_src": {},
    "flash_ctrl": {},
    "gpio": {},
    "hmac": {},
    "i2c": {},
    "keymgr": {},
    "keymgr_dpe": {},
    "kmac": {},
    "lc_ctrl": {},
    "mbx": {
        "deps": ["//sw/device/lib/base:abs_mmio"],
    },
    "otbn": {},
    "otp_ctrl": {},
    "pattgen": {},
    "pinmux": {},
    "pwm": {},
    "pwrmgr": {
        "ut_target_compatible_with": opentitan_require_top("earlgrey"),
    },
    "rom_ctrl": {},
    "rstmgr": {},
    "rv_core_ibex": {},
    "rv_dm": {},
    "rv_plic": {},
    "rv_timer": {},
    "soc_proxy": {},
    "spi_device": {},
    "spi_host": {
        "ut_deps": ["//sw/device/lib/base:global_mock"],
    },
    "sram_ctrl": {},
    "sensor_ctrl": {},
    "sysrst_ctrl": {},
    "uart": {},
    "usbdev": {},
}

[
    cc_library(
        name = ip,
        srcs = [
            "dif_{}.c".format(ip),
        ],
        hdrs = [
            "dif_{}.h".format(ip),
        ],
        deps = [
            "//sw/device/lib/dif/autogen:{}".format(ip),
            "//sw/device/lib/base:bitfield",
            "//sw/device/lib/base:macros",
            "//sw/device/lib/base:memory",
            "//sw/device/lib/base:mmio",
            "//sw/device/lib/base:multibits",
            "//sw/device/lib/runtime:hart",
        ] + cfg.get("deps", []),
    )
    for (ip, cfg) in DIFS.items()
]

[
    cc_test(
        name = "{}_unittest".format(ip),
        srcs = [
            "dif_{}_unittest.cc".format(ip),
            "//sw/device/lib/dif/autogen:{}_unittest".format(ip),
        ],
        target_compatible_with = cfg.get("ut_target_compatible_with", []),
        deps = [
            ":{}".format(ip),
            ":test_base",
            "@googletest//:gtest_main",
        ] + cfg.get("ut_deps", []),
    )
    for (ip, cfg) in DIFS.items()
]

cc_library(
    name = "csrng_shared",
    srcs = [
        "dif_csrng_shared.c",
    ],
    hdrs = [
        "dif_csrng.h",
        "dif_csrng_shared.h",
    ],
    deps = [
        ":base",
        "//hw/top:csrng_c_regs",
        "//hw/top:dt_csrng",
        "//hw/top:edn_c_regs",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/dif/autogen:csrng",
    ],
)

cc_library(
    name = "rstmgr_intf",
    srcs = ["//sw/device/lib/dif/autogen:rstmgr_hdr"],
    hdrs = ["dif_rstmgr.h"],
    deps = [
        ":base",
        "//hw/top:dt_rstmgr",
    ],
)

cc_library(
    name = "all_difs",
    deps = flatten([
        # Add all compatible register headers
        opentitan_if_ip(
            ip,
            [":{}".format(ip)],
            [],
        )
        for ip in DIFS.keys()
    ]),
)

alias(
    name = "doxy_target",
    actual = ":all_difs",
)
