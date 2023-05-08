# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "OPENTITAN_CPU")
load(
    "//rules:opentitan_test.bzl",
    "OPENTITANTOOL_OPENOCD_DATA_DEPS",
    "OPENTITANTOOL_OPENOCD_TEST_CMDS",
    "ROM_BOOT_FAILURE_MSG",
    "cw310_params",
    "dv_params",
    "opentitan_functest",
    "verilator_params",
)
load("//rules:splice.bzl", "bitstream_splice")
load("//rules:otp.bzl", "STD_OTP_OVERLAYS", "otp_image", "otp_json", "otp_partition")

package(default_visibility = ["//visibility:public"])

# TODO(lowRISC:opentitan#13180): this is a temporary solution to enable writing
# manufacturer specific tests in the `manufacturer_test_hooks` repository that
# use open source test code. Specifically, this enables defining an
# `opentitan_functest` in the `manufacturer_test_hooks` repository without the
# need to specify the corresponding test hooks that should be used with the test
# on the command line.
exports_files(glob([
    "*.c",
    "*.h",
]))

opentitan_functest(
    name = "aes_masking_off_test",
    srcs = ["aes_masking_off_test.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/ip/aes:model",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aes_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "aes_entropy_test",
    srcs = ["aes_entropy_test.c"],
    deps = [
        "//hw/ip/aes:model",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aes_testutils",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "aes_idle_test",
    srcs = ["aes_idle_test.c"],
    targets = [
        "dv",
        "verilator",
        "cw310_test_rom",
    ],
    deps = [
        "//hw/ip/aes:model",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aes",
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aes_testutils",
        "//sw/device/lib/testing:clkmgr_testutils",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

alias(
    name = "aes_smoketest_entropy_testutils",
    actual = select({
        "//sw/device:is_english_breakfast": "//sw/device:nothing",
        "//conditions:default": "//sw/device/lib/testing:entropy_testutils",
    }),
    visibility = ["//visibility:private"],
)

opentitan_functest(
    name = "aes_smoketest",
    srcs = ["aes_smoketest.c"],
    deps = [
        "//hw/ip/aes:model",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aes_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "alert_handler_ping_timeout_test",
    srcs = ["alert_handler_ping_timeout_test.c"],
    cw310 = cw310_params(
        timeout = "moderate",
    ),
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/top_earlgrey:alert_handler_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:math",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:alert_handler",
        "//sw/device/lib/dif:rv_core_ibex",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:alert_handler_testutils",
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "alert_handler_lpg_clkoff_test",
    srcs = ["alert_handler_lpg_clkoff_test.c"],
    cw310 = cw310_params(timeout = "moderate"),
    targets = [
        # The test requires the Ibex core to wait long enough
        # before checking for the ping_timeout error.
        # The wait-time for the Verilator would be around
        # 32M*8us = 256s (kClockFreqPeripheralHz = 125K).
        # Thus it is not recommended to run this test on
        # Verilator as this wait-time looks impractical. It should still
        # be run as part of the DV nightly regression.
        "cw310_test_rom",
        "dv",
    ],
    deps = [
        "//hw/top_earlgrey:alert_handler_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:math",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aes",
        "//sw/device/lib/dif:alert_handler",
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:hmac",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/dif:otbn",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:spi_host",
        "//sw/device/lib/dif:usbdev",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:alert_handler_testutils",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:rand_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "alert_handler_reverse_ping_in_deep_sleep_test",
    srcs = ["alert_handler_reverse_ping_in_deep_sleep_test.c"],
    targets = [
        "cw310_test_rom",
        "dv",
    ],
    deps = [
        "//hw/top_earlgrey:alert_handler_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:math",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:alert_handler",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:alert_handler_testutils",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "alert_handler_lpg_reset_toggle_test",
    srcs = ["alert_handler_lpg_reset_toggle.c"],
    cw310 = cw310_params(
        timeout = "moderate",
    ),
    targets = [
        # The test requires the Ibex core to wait long enough
        # before checking for the ping_timeout error.
        # The wait-time for the Verilator would be around
        # 32M*8us = 256s (kClockFreqPeripheralHz = 125K).
        # Thus it is not recommended to run this test on
        # Verilator as this wait-time looks impractical. It should still
        # be run as part of the DV nightly regression.
        "cw310_test_rom",
        "dv",
    ],
    deps = [
        "//hw/ip/i2c/data:i2c_regs",
        "//hw/ip/spi_device/data:spi_device_regs",
        "//hw/ip/spi_host/data:spi_host_regs",
        "//hw/ip/usbdev/data:usbdev_regs",
        "//hw/top_earlgrey:alert_handler_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:math",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:alert_handler",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:i2c",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:spi_device",
        "//sw/device/lib/dif:spi_host",
        "//sw/device/lib/dif:usbdev",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:alert_handler_testutils",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "alert_handler_lpg_sleep_mode_pings_test",
    srcs = ["alert_handler_lpg_sleep_mode_pings.c"],
    cw310 = cw310_params(
        timeout = "moderate",
    ),
    targets = [
        # The test requires the Ibex core to wait long enough
        # before checking for the ping_timeout error.
        # The wait-time for the Verilator would be around
        # 4s (kClockFreqPeripheralHz = 125K).
        # Thus it is not recommended to run this test on
        # Verilator as this wait-time looks impractical. It should still
        # be run as part of the DV nightly regression.
        "cw310_test_rom",
        "dv",
    ],
    deps = [
        "//hw/top_earlgrey:alert_handler_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:math",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:alert_handler",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:alert_handler_testutils",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rand_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "alert_handler_lpg_sleep_mode_alerts_test",
    srcs = ["alert_handler_lpg_sleep_mode_alerts.c"],
    targets = [
        # The test requires to drive fatal alerts
        # which is possible only in DV sim.
        "dv",
    ],
    deps = [
        "//hw/top_earlgrey:alert_handler_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:math",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:alert_handler",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:alert_handler_testutils",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rand_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "aon_timer_irq_test",
    srcs = ["aon_timer_irq_test.c"],
    targets = [
        "dv",
        "verilator",
        "cw310_test_rom",
    ],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:math",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:rv_timer",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:rand_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "aon_timer_smoketest",
    srcs = ["aon_timer_smoketest.c"],
    targets = [
        "dv",
        "verilator",
        "cw310_test_rom",
    ],
    deps = [
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "aon_timer_wdog_bite_reset_test",
    srcs = ["aon_timer_wdog_bite_reset_test.c"],
    verilator = verilator_params(
        tags = [
            "broken",
        ],
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:math",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "pwrmgr_wdog_reset_reqs_test",
    srcs = ["pwrmgr_wdog_reset_reqs_test.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:math",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "aon_timer_wdog_lc_escalate_test",
    srcs = ["aon_timer_wdog_lc_escalate_test.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:math",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:alert_handler",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:rv_timer",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:alert_handler_testutils",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "aon_timer_sleep_wdog_sleep_pause_test",
    srcs = ["aon_timer_sleep_wdog_sleep_pause_test.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "chip_power_idle_load",
    srcs = ["chip_power_idle_load.c"],
    verilator = verilator_params(
        tags = ["broken"],  # FIXME #16374 test doesn't make progress after enabling PWM
    ),
    deps = [
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:alert_handler",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:pwm",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:alert_handler_testutils",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "chip_power_sleep_load",
    srcs = ["chip_power_sleep_load.c"],
    verilator = verilator_params(
        tags = ["broken"],  # FIXME #16374 test doesn't make progress after enabling PWM
    ),
    deps = [
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:adc_ctrl",
        "//sw/device/lib/dif:alert_handler",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:pwm",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:alert_handler_testutils",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

cc_library(
    name = "clkmgr_external_clk_src_for_sw_impl",
    srcs = ["clkmgr_external_clk_src_for_sw_impl.c"],
    hdrs = ["clkmgr_external_clk_src_for_sw_impl.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/dif:base",
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:clkmgr_testutils",
        "//sw/device/lib/testing/test_framework:check",
    ],
)

opentitan_functest(
    name = "clkmgr_external_clk_src_for_sw_fast_test",
    srcs = ["clkmgr_external_clk_src_for_sw_fast_test.c"],
    cw310 = cw310_params(
        # FIXME #12486 [bazel] targets in sw/device/tests failing on cw310 and verilator when built by bazel
        tags = ["broken"],
    ),
    verilator = verilator_params(
        tags = [
            "broken",
        ],
    ),
    deps = [
        ":clkmgr_external_clk_src_for_sw_impl",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "clkmgr_external_clk_src_for_sw_slow_test",
    srcs = ["clkmgr_external_clk_src_for_sw_slow_test.c"],
    cw310 = cw310_params(
        # FIXME #12486 [bazel] targets in sw/device/tests failing on cw310 and verilator when built by bazel
        tags = ["broken"],
    ),
    verilator = verilator_params(
        tags = [
            "broken",
        ],
    ),
    deps = [
        ":clkmgr_external_clk_src_for_sw_impl",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "clkmgr_jitter_test",
    srcs = ["clkmgr_jitter_test.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/dif:base",
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "clkmgr_off_peri_test",
    srcs = ["clkmgr_off_peri_test.c"],
    verilator = verilator_params(
        timeout = "eternal",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:base",
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:spi_host",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/dif:usbdev",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

cc_library(
    name = "clkmgr_off_trans_impl",
    srcs = ["clkmgr_off_trans_impl.c"],
    hdrs = ["clkmgr_off_trans_impl.h"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/dif:aes",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:base",
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/dif:hmac",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/dif:otbn",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "clkmgr_off_aes_trans_test",
    srcs = ["clkmgr_off_aes_trans_test.c"],
    deps = ["clkmgr_off_trans_impl"],
)

opentitan_functest(
    name = "clkmgr_off_hmac_trans_test",
    srcs = ["clkmgr_off_hmac_trans_test.c"],
    deps = ["clkmgr_off_trans_impl"],
)

opentitan_functest(
    name = "clkmgr_off_kmac_trans_test",
    srcs = ["clkmgr_off_kmac_trans_test.c"],
    deps = ["clkmgr_off_trans_impl"],
)

opentitan_functest(
    name = "clkmgr_off_otbn_trans_test",
    srcs = ["clkmgr_off_otbn_trans_test.c"],
    deps = ["clkmgr_off_trans_impl"],
)

opentitan_functest(
    name = "clkmgr_reset_frequency_test",
    srcs = ["clkmgr_reset_frequency_test.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:sensor_ctrl",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:clkmgr_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing:sensor_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "clkmgr_sleep_frequency_test",
    srcs = ["clkmgr_sleep_frequency_test.c"],
    verilator = verilator_params(
        # FIXME #13611
        tags = ["broken"],
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:sensor_ctrl",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:clkmgr_testutils",
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing:sensor_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "clkmgr_smoketest",
    srcs = ["clkmgr_smoketest.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/dif:base",
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "coverage_test",
    srcs = ["coverage_test.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "crt_test",
    srcs = ["crt_test.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:stdasm",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_start",
        "//sw/device/lib/testing/test_framework:ottf_test_config",
        "//sw/device/lib/testing/test_framework:status",
    ],
)

opentitan_functest(
    name = "csrng_edn_concurrency_test",
    srcs = ["csrng_edn_concurrency_test.c"],
    verilator = verilator_params(
        timeout = "eternal",
    ),
    deps = [
        ":otbn_randomness_impl",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:base",
        "//sw/device/lib/dif:csrng",
        "//sw/device/lib/dif:csrng_shared",
        "//sw/device/lib/dif:edn",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:csrng_testutils",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:otbn_testutils",
        "//sw/device/lib/testing:rand_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "csrng_kat_test",
    srcs = ["csrng_kat_test.c"],
    deps = [
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:csrng",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:csrng_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "csrng_smoketest",
    srcs = ["csrng_smoketest.c"],
    deps = [
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:csrng",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:csrng_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "entropy_src_fw_ovr_test",
    srcs = ["entropy_src_fw_ovr_test.c"],
    cw310 = cw310_params(
        # FIXME #12486 [bazel] targets in sw/device/tests failing on cw310 and verilator when built by bazel
        tags = ["broken"],
    ),
    verilator = verilator_params(
        tags = [
            "broken",
        ],
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:base",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

cc_library(
    name = "entropy_src_kat_impl",
    srcs = ["entropy_src_kat_impl.c"],
    hdrs = ["entropy_src_kat_impl.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:base",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing/test_framework:check",
    ],
)

opentitan_functest(
    name = "entropy_src_kat_test",
    srcs = ["entropy_src_kat_test.c"],
    deps = [
        ":entropy_src_kat_impl",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "entropy_src_smoketest",
    srcs = ["entropy_src_smoketest.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:base",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "entropy_src_ast_rng_req_test",
    srcs = ["entropy_src_ast_rng_req_test.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "entropy_src_csrng_test",
    srcs = ["entropy_src_csrng_test.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        ":otbn_randomness_impl",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:base",
        "//sw/device/lib/dif:csrng",
        "//sw/device/lib/dif:edn",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/dif:otbn",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:csrng_testutils",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:otbn_testutils",
        "//sw/device/lib/testing:rand_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "entropy_src_edn_reqs_test",
    srcs = ["entropy_src_edn_reqs_test.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        ":otbn_randomness_impl",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aes",
        "//sw/device/lib/dif:alert_handler",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/dif:keymgr",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/dif:otbn",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rv_core_ibex",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aes_testutils",
        "//sw/device/lib/testing:alert_handler_testutils",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "example_concurrency_test",
    srcs = ["example_concurrency_test.c"],
    deps = [
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "example_test_from_flash",
    srcs = ["example_test_from_flash.c"],
    deps = [
        "//sw/device/lib/testing:rand_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "example_test_from_rom",
    srcs = ["example_test_from_rom.c"],
    targets = [
        "dv",
        "verilator",
    ],
    # This test is designed to run and complete entirely in the ROM boot stage.
    # Setting the `test_in_rom` flag makes the `opentitan_functest` rule aware
    # of this, and instructs it to load the test image into ROM (rather than
    # loading the default test ROM, or any other ROM that may be specified via
    # DV or Verilator params).
    test_in_rom = True,
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:status",
        "//sw/device/lib/testing/test_rom:linker_script",
        "//sw/device/lib/testing/test_rom:test_rom_lib",
    ],
)

opentitan_functest(
    name = "flash_ctrl_idle_low_power_test",
    srcs = ["flash_ctrl_idle_low_power_test.c"],
    targets = [
        "dv",
        "verilator",
        "cw310_test_rom",
    ],
    verilator = verilator_params(
        tags = [
            "broken",
        ],
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rand_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "flash_ctrl_ops_test",
    srcs = ["flash_ctrl_ops_test.c"],
    cw310 = cw310_params(
        # FIXME #12486 [bazel] targets in sw/device/tests failing on cw310 and verilator when built by bazel
        tags = ["broken"],
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "flash_ctrl_clock_freqs_test",
    srcs = ["flash_ctrl_clock_freqs_test.c"],
    cw310 = cw310_params(
        # FIXME #12486 [bazel] targets in sw/device/tests failing on cw310 and verilator when built by bazel
        tags = ["broken"],
    ),
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:rand_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "flash_ctrl_test",
    srcs = ["flash_ctrl_test.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "gpio_smoketest",
    srcs = ["gpio_smoketest.c"],
    targets = [
        #not compatible with the verilated top level
        "cw310_test_rom",
        "dv",
    ],
    deps = [
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "gpio_pinmux_test",
    srcs = ["gpio_pinmux_test.c"],
    cw310 = cw310_params(
        interface = "hyper310",
        tags = ["manual"],
        test_cmds = [
            "--rom-kind=testrom",
            "--bitstream=\"$(location {bitstream})\"",
            "--bootstrap=\"$(location {flash})\"",
        ],
    ),
    targets = [
        "verilator",
        "cw310_test_rom",
    ],
    test_harness = "//sw/host/tests/chip/gpio",
    verilator = verilator_params(
        timeout = "eternal",
        test_cmds = [],
    ),
    deps = [
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/testing/json:command",
        "//sw/device/lib/testing/json:gpio",
        "//sw/device/lib/testing/json:pinmux_config",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "hmac_enc_test",
    srcs = ["hmac_enc_test.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:hmac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:hmac_testutils",
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "hmac_enc_idle_test",
    srcs = ["hmac_enc_idle_test.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/dif:hmac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:clkmgr_testutils",
        "//sw/device/lib/testing:hmac_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "hmac_smoketest",
    srcs = ["hmac_smoketest.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:hmac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:hmac_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "keymgr_key_derivation_test",
    srcs = ["keymgr_key_derivation_test.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/ip/keymgr/data:keymgr_regs",
        "//hw/ip/kmac/data:kmac_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/dif:keymgr",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "keymgr_sideload_aes_test",
    srcs = ["keymgr_sideload_aes_test.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/ip/aes/data:aes_regs",
        "//hw/ip/keymgr/data:keymgr_regs",
        "//hw/ip/kmac/data:kmac_regs",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/dif:aes",
        "//sw/device/lib/dif:keymgr",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:aes_testutils",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing:kmac_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "keymgr_sideload_kmac_test",
    srcs = ["keymgr_sideload_kmac_test.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/ip/keymgr/data:keymgr_regs",
        "//hw/ip/kmac/data:kmac_regs",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/dif:keymgr",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing:kmac_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "keymgr_sideload_otbn_test",
    srcs = ["keymgr_sideload_otbn_test.c"],
    verilator = verilator_params(
        timeout = "eternal",
    ),
    deps = [
        "//hw/ip/otbn/data:otbn_regs",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/dif:keymgr",
        "//sw/device/lib/dif:otbn",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing:otbn_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/otbn/crypto:x25519_sideload",
    ],
)

opentitan_functest(
    name = "kmac_app_rom_test",
    srcs = ["kmac_app_rom_test.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:rom_ctrl",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "kmac_entropy_test",
    srcs = ["kmac_entropy_test.c"],
    cw310 = cw310_params(
        # FIXME #15530: EDN doesn't timeout on FPGA
        tags = ["broken"],
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "kmac_idle_test",
    srcs = ["kmac_idle_test.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "kmac_mode_cshake_test",
    srcs = ["kmac_mode_cshake_test.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "kmac_mode_kmac_test",
    srcs = ["kmac_mode_kmac_test.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "kmac_smoketest",
    srcs = ["kmac_smoketest.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "lc_ctrl_otp_hw_cfg_test",
    srcs = ["lc_ctrl_otp_hw_cfg_test.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:lc_ctrl",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "otbn_ecdsa_op_irq_test",
    srcs = ["otbn_ecdsa_op_irq_test.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:otbn",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:otbn_testutils",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/otbn/crypto:p256_ecdsa",
    ],
)

opentitan_functest(
    name = "otbn_irq_test",
    srcs = ["otbn_irq_test.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:otbn",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:otbn_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/otbn/code-snippets:err_test",
    ],
)

opentitan_functest(
    name = "otbn_mem_scramble_test",
    srcs = ["otbn_mem_scramble_test.c"],
    cw310 = cw310_params(
        # FIXME #12486 [bazel] targets in sw/device/tests failing on cw310 and verilator when built by bazel
        tags = ["broken"],
    ),
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:base",
        "//sw/device/lib/dif:otbn",
        "//sw/device/lib/dif:rv_core_ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:otbn_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

cc_library(
    name = "otbn_randomness_impl",
    srcs = ["otbn_randomness_impl.c"],
    hdrs = ["otbn_randomness_impl.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/dif:base",
        "//sw/device/lib/dif:otbn",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:otbn_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/otbn/code-snippets:randomness",
    ],
)

opentitan_functest(
    name = "otbn_randomness_test",
    srcs = ["otbn_randomness_test.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        ":otbn_randomness_impl",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:base",
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/dif:otbn",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:clkmgr_testutils",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:otbn_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "otbn_rsa_test",
    srcs = ["otbn_rsa_test.c"],
    verilator = verilator_params(
        timeout = "eternal",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:otbn",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:otbn_testutils",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/otbn/crypto:rsa",
    ],
)

opentitan_functest(
    name = "otbn_smoketest",
    srcs = ["otbn_smoketest.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:otbn",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:otbn_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/otbn/code-snippets:barrett384",
        "//sw/otbn/code-snippets:err_test",
    ],
)

opentitan_functest(
    name = "otp_ctrl_smoketest",
    srcs = ["otp_ctrl_smoketest.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "plic_sw_irq_test",
    srcs = ["plic_sw_irq_test.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:math",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "pmp_smoketest_napot",
    srcs = ["pmp_smoketest_napot.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:pmp",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "pmp_smoketest_tor",
    srcs = ["pmp_smoketest_tor.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:pmp",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "pwrmgr_smoketest",
    srcs = ["pwrmgr_smoketest.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "pwrmgr_sleep_disabled_test",
    srcs = ["pwrmgr_sleep_disabled_test.c"],
    cw310 = cw310_params(
        # FIXME #12486 [bazel] targets in sw/device/tests failing on cw310 and verilator when built by bazel
        tags = ["broken"],
    ),
    verilator = verilator_params(
        tags = ["broken"],
    ),
    deps = [
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "rstmgr_smoketest",
    srcs = ["rstmgr_smoketest.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "rstmgr_cpu_info_test",
    srcs = ["rstmgr_cpu_info_test.c"],
    targets = [
        "cw310_test_rom",
        "dv",
        "verilator",
    ],
    verilator = verilator_params(
        timeout = "long",
        tags = ["broken"],
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:rv_core_ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "rstmgr_sw_req_test",
    srcs = ["rstmgr_sw_req_test.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "rstmgr_sw_rst_ctrl_test",
    srcs = ["rstmgr_sw_rst_ctrl_test.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/ip/i2c/data:i2c_regs",
        "//hw/ip/spi_device/data:spi_device_regs",
        "//hw/ip/spi_host/data:spi_host_regs",
        "//hw/ip/usbdev/data:usbdev_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:i2c",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:spi_device",
        "//sw/device/lib/dif:spi_host",
        "//sw/device/lib/dif:usbdev",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "rv_plic_smoketest",
    srcs = ["rv_plic_smoketest.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:status",
    ],
)

opentitan_functest(
    name = "rv_timer_smoketest",
    srcs = ["rv_timer_smoketest.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:rv_timer",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "spi_host_smoketest",
    srcs = ["spi_host_smoketest.c"],
    targets = ["cw310_test_rom"],  # Can only run on CW310 board right now.
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:spi_host",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:spi_device_testutils",
        "//sw/device/lib/testing:spi_flash_testutils",
        "//sw/device/lib/testing:spi_host_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "spi_host_irq_test",
    srcs = ["spi_host_irq_test.c"],
    targets = ["cw310_test_rom"],  # Can only run on CW310 board right now.
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:spi_host",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing:spi_device_testutils",
        "//sw/device/lib/testing:spi_flash_testutils",
        "//sw/device/lib/testing:spi_host_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "i2c_host_power_monitor_test",
    srcs = ["i2c_host_power_monitor_test.c"],
    cw310 = cw310_params(
        tags = ["skip_in_ci"],  # Requires the Bob in CI.
    ),
    targets = ["cw310_test_rom"],  # Can only run on CW310 board right now.
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:i2c",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:i2c_testutils",
        "//sw/device/lib/testing:rv_core_ibex_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "sensor_ctrl_alert_test",
    srcs = ["sensor_ctrl_alerts.c"],
    verilator = verilator_params(
        timeout = "eternal",
    ),
    deps = [
        "//hw/top_earlgrey/ip/sensor_ctrl/data:sensor_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:alert_handler",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:sensor_ctrl",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rand_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "sensor_ctrl_wakeup_test",
    srcs = ["sensor_ctrl_wakeup.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/top_earlgrey/ip/sensor_ctrl/data:sensor_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:sensor_ctrl",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "sleep_pwm_pulses_test",
    srcs = ["sleep_pwm_pulses_test.c"],
    verilator = verilator_params(
        timeout = "eternal",
        tags = ["broken"],
    ),
    deps = [
        "//hw/ip/pwm/data:pwm_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:pwm",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "sram_ctrl_execution_test",
    srcs = ["sram_ctrl_execution_test.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/examples/sram_program",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/dif:sram_ctrl",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:epmp_state",
    ],
)

opentitan_functest(
    name = "sram_ctrl_sleep_sram_ret_contents_test",
    srcs = ["sram_ctrl_sleep_sram_ret_contents_test.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing:sram_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
    ],
)

opentitan_functest(
    name = "sram_ctrl_smoketest",
    srcs = ["sram_ctrl_smoketest.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:sram_ctrl",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "uart_smoketest_signed",
    srcs = ["uart_smoketest.c"],
    cw310 = cw310_params(
        exit_failure = ROM_BOOT_FAILURE_MSG,
    ),
    dv = dv_params(
        rom = "//sw/device/silicon_creator/rom:rom_with_fake_keys",
    ),
    manifest = "//sw/device/silicon_creator/rom_ext:manifest_standard",
    signed = True,
    targets = [
        "cw310_rom",
        "verilator",
        "dv",
    ],
    verilator = verilator_params(
        timeout = "eternal",
        exit_failure = ROM_BOOT_FAILURE_MSG,
        rom = "//sw/device/silicon_creator/rom:rom_with_fake_keys",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "uart_smoketest",
    srcs = ["uart_smoketest.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "usbdev_test",
    srcs = ["usbdev_test.c"],
    cw310 = cw310_params(
        tags = ["skip_in_ci"],  # Requires DPI model
    ),
    targets = [
        "verilator",
        "cw310_test_rom",
        "dv",
    ],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:usbdev",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing:usb_testutils",
        "//sw/device/lib/testing:usb_testutils_simpleserial",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "usbdev_stream_test",
    srcs = ["usbdev_stream_test.c"],
    cw310 = cw310_params(
        timeout = "eternal",
    ),
    targets = [
        "verilator",
        "cw310_test_rom",
    ],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing:usb_testutils",
        "//sw/device/lib/testing:usb_testutils_streams",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "rstmgr_alert_info_test",
    srcs = ["rstmgr_alert_info_test.c"],
    targets = [
        "cw310_test_rom",
        "verilator",
        "dv",
    ],
    verilator = verilator_params(
        timeout = "long",
        tags = ["broken"],
    ),
    deps = [
        "//hw/top_earlgrey:alert_handler_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:alert_handler",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:i2c",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:rv_core_ibex",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:rv_timer",
        "//sw/device/lib/dif:spi_host",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:alert_handler_testutils",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "rv_core_ibex_rnd_test",
    srcs = [
        "rv_core_ibex_rnd_test.S",
        "rv_core_ibex_rnd_test.c",
    ],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:edn",
        "//sw/device/lib/dif:rv_core_ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:rv_core_ibex_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "rv_core_ibex_address_translation_test",
    srcs = [
        "rv_core_ibex_address_translation_test.S",
        "rv_core_ibex_address_translation_test.c",
    ],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:rv_core_ibex",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:epmp_state",
    ],
)

opentitan_functest(
    name = "rv_core_ibex_nmi_irq_test",
    srcs = ["rv_core_ibex_nmi_irq_test.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:alert_handler",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:rv_core_ibex",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:alert_handler_testutils",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "rv_core_ibex_icache_invalidate_test",
    srcs = ["rv_core_ibex_icache_invalidate_test.c"],
    deps = [
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "ast_clk_outs_test",
    srcs = ["ast_clk_outs_test.c"],
    cw310 = cw310_params(
        # FIXME #13611
        tags = ["broken"],
    ),
    verilator = verilator_params(
        # FIXME #13611
        timeout = "eternal",
        tags = ["broken"],
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:sensor_ctrl",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:clkmgr_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:sensor_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

otp_json(
    name = "power_virus_systemtest_otp_overlay",
    partitions = [
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {
                # Enable flash scrambling and ECC.
                "CREATOR_SW_CFG_FLASH_DATA_DEFAULT_CFG": "0000090606",
            },
        ),
    ],
)

otp_image(
    name = "power_virus_systemtest_otp_img_rma",
    src = "//hw/ip/otp_ctrl/data:otp_json_rma",
    overlays = STD_OTP_OVERLAYS + [":power_virus_systemtest_otp_overlay"],
    visibility = ["//visibility:private"],
)

bitstream_splice(
    name = "power_virus_systemtest_bitstream",
    src = "//hw/bitstream:test_rom",
    data = ":power_virus_systemtest_otp_img_rma",
    meminfo = "//hw/bitstream:otp_mmi",
    update_usr_access = True,
    visibility = ["//visibility:private"],
)

opentitan_functest(
    name = "power_virus_systemtest",
    srcs = ["power_virus_systemtest.c"],
    cw310 = cw310_params(
        bitstream = ":power_virus_systemtest_bitstream",
        test_cmds = [
            "--rom-kind={rom_kind}",
            "--bitstream=\"$(location {bitstream})\"",
            "--bootstrap=\"$(location {flash})\"",
        ],
    ),
    dv = dv_params(
        otp = ":power_virus_systemtest_otp_img_rma",
    ),
    targets = [
        # TODO(#14814): add more targets
        "cw310_test_rom",
        "dv",
    ],
    test_harness = "//sw/host/tests/chip/power_virus",
    deps = [
        "//hw/ip/adc_ctrl/data:adc_ctrl_regs",
        "//hw/ip/aes:model",
        "//hw/ip/aes/data:aes_regs",
        "//hw/ip/csrng/data:csrng_regs",
        "//hw/ip/entropy_src/data:entropy_src_regs",
        "//hw/ip/gpio/data:gpio_regs",
        "//hw/ip/hmac/data:hmac_regs",
        "//hw/ip/i2c/data:i2c_regs",
        "//hw/ip/kmac/data:kmac_regs",
        "//hw/ip/pattgen/data:pattgen_regs",
        "//hw/ip/pwm/data:pwm_regs",
        "//hw/ip/spi_host/data:spi_host_regs",
        "//hw/ip/uart/data:uart_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:math",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/impl/rsa:rsa_3072_verify",
        "//sw/device/lib/dif:adc_ctrl",
        "//sw/device/lib/dif:aes",
        "//sw/device/lib/dif:csrng",
        "//sw/device/lib/dif:csrng_shared",
        "//sw/device/lib/dif:edn",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:hmac",
        "//sw/device/lib/dif:i2c",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/dif:otbn",
        "//sw/device/lib/dif:pattgen",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:pwm",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:spi_device",
        "//sw/device/lib/dif:spi_host",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aes_testutils",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:hmac_testutils",
        "//sw/device/lib/testing:i2c_testutils",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing:spi_device_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/tests/crypto:rsa_3072_verify_testvectors_hardcoded_header",
    ],
)

opentitan_functest(
    name = "spi_passthru_test",
    srcs = [
        "spi_passthru_test.c",
    ],
    cw310 = cw310_params(
        # This test will need hyperdebug once we start using multi-lane
        # SPI modes.
        #interface = "hyper310",
        #tags = ["manual"],
        test_cmds = [
            "--rom-kind=testrom",
            "--bitstream=\"$(location {bitstream})\"",
            "--bootstrap=\"$(location {flash})\"",
        ],
    ),
    targets = [
        "cw310_test_rom",
    ],
    test_harness = "//sw/host/tests/chip/spi_passthru",
    deps = [
        "//sw/device/lib/arch:device",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:spi_device",
        "//sw/device/lib/testing:spi_device_testutils",
        "//sw/device/lib/testing:spi_flash_testutils",
        "//sw/device/lib/testing/json:command",
        "//sw/device/lib/testing/json:spi_passthru",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
    ],
)

otp_json(
    name = "flash_scrambling_smoketest_otp_overlay",
    partitions = [
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {
                # Enable flash scrambling and ECC.
                "CREATOR_SW_CFG_FLASH_DATA_DEFAULT_CFG": "0000090606",
            },
        ),
    ],
)

otp_image(
    name = "flash_scrambling_smoketest_otp_img_rma",
    src = "//hw/ip/otp_ctrl/data:otp_json_rma",
    overlays = STD_OTP_OVERLAYS + [":flash_scrambling_smoketest_otp_overlay"],
    visibility = ["//visibility:private"],
)

opentitan_functest(
    name = "flash_scrambling_smoketest",
    srcs = ["example_test_from_flash.c"],
    dv = dv_params(
        otp = ":flash_scrambling_smoketest_otp_img_rma",
    ),
    targets = [
        "dv",
    ],
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "openocd_test",
    srcs = ["example_test_from_flash.c"],
    cw310 = cw310_params(
        bitstream = "//hw/bitstream:rom_otp_test_unlocked0",
        tags = ["jtag"],
        test_cmds = [
            "--rom-kind=rom",
            "--bitstream=\"$(rootpath {bitstream})\"",
        ] + OPENTITANTOOL_OPENOCD_TEST_CMDS,
    ),
    data = OPENTITANTOOL_OPENOCD_DATA_DEPS,
    targets = ["cw310_rom"],
    test_harness = "//sw/host/tests/chip/jtag:openocd_test",
    deps = [
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
    logging = "info",
)

opentitan_functest(
    name = "spi_device_ottf_console_test",
    srcs = ["spi_device_ottf_console_test.c"],
    cw310 = cw310_params(
        interface = "hyper310",
        tags = ["manual"],
        test_cmds = [
            "--rom-kind=testrom",
            "--bitstream=\"$(location {bitstream})\"",
            "--bootstrap=\"$(location {flash})\"",
        ],
    ),
    targets = [
        "cw310_test_rom",
    ],
    test_harness = "//sw/host/tests/chip/spi_device_ottf_console",
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:spi_device",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)
