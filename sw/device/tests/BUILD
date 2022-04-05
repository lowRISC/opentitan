# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan_test.bzl", "opentitan_functest", "verilator_params")

opentitan_functest(
    name = "aes_smoketest",
    srcs = ["aes_smoketest.c"],
    deps = [
        "//sw/device/lib/dif:aes",
        "//sw/device/lib/testing:aes_testutils",
        "//sw/device/lib/testing:entropy_testutils",
    ],
)

opentitan_functest(
    name = "aon_timer_smoketest",
    srcs = ["aon_timer_smoketest.c"],
    deps = [
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/testing:aon_timer_testutils",
    ],
)

opentitan_functest(
    name = "clkmgr_smoketest",
    srcs = ["clkmgr_smoketest.c"],
    deps = [
        "//sw/device/lib/dif:clkmgr",
    ],
)

opentitan_functest(
    name = "csrng_smoketest",
    srcs = ["csrng_smoketest.c"],
    verilator = verilator_params(
        tags = [
            "cpu:4",
            "failing_verilator",
        ],
    ),
    deps = [
        "//sw/device/lib/dif:csrng",
    ],
)

opentitan_functest(
    name = "entropy_src_smoketest",
    srcs = ["entropy_src_smoketest.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/dif:entropy_src",
    ],
)

opentitan_functest(
    name = "gpio_smoketest",
    srcs = ["gpio_smoketest.c"],
    verilator = verilator_params(
        args = [
            "--verilator-args=--trace",
            "console",
            "--timeout=3600",
            "--exit-failure=FAIL",
            "--exit-success=PASS",
        ],
        tags = [
            "cpu:4",
            "failing_verilator",
        ],
    ),
    deps = [
        "//sw/device/lib/dif:gpio",
    ],
)

opentitan_functest(
    name = "hmac_smoketest",
    srcs = ["hmac_smoketest.c"],
    deps = [
        "//sw/device/lib:flash_ctrl",
        "//sw/device/lib/dif:hmac",
        "//sw/device/lib/testing:hmac_testutils",
    ],
)

opentitan_functest(
    name = "kmac_smoketest",
    srcs = ["kmac_smoketest.c"],
    deps = [
        "//sw/device/lib/dif:kmac",
    ],
)

opentitan_functest(
    name = "otbn_smoketest",
    srcs = ["otbn_smoketest.c"],
    deps = [
        "//sw/device/lib/dif:otbn",
        "//sw/device/lib/runtime:otbn",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/otbn/code-snippets:barrett384",
        "//sw/otbn/code-snippets:err_test",
    ],
)

opentitan_functest(
    name = "otp_ctrl_smoketest",
    srcs = ["otp_ctrl_smoketest.c"],
    deps = [
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/testing:otp_ctrl_testutils",
    ],
)

opentitan_functest(
    name = "pwrmgr_smoketest",
    srcs = ["pwrmgr_smoketest.c"],
    deps = [
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
    ],
)

opentitan_functest(
    name = "rstmgr_smoketest",
    srcs = ["rstmgr_smoketest.c"],
    deps = [
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/testing:rstmgr_testutils",
    ],
)

opentitan_functest(
    name = "rv_plic_smoketest",
    srcs = ["rv_plic_smoketest.c"],
    deps = [
        "//sw/device/lib/dif:rv_plic",
    ],
)

opentitan_functest(
    name = "rv_timer_smoketest",
    srcs = ["rv_timer_smoketest.c"],
)

opentitan_functest(
    name = "uart_smoketest",
    srcs = ["uart_smoketest.c"],
)

opentitan_functest(
    name = "spi_host_smoketest",
    srcs = ["spi_host_smoketest.c"],
    targets = ["cw310"],  # Can only run on CW310 board right now.
    deps = [
        "//sw/device/lib/dif:spi_host",
    ],
)
