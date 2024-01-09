# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:const-darjeeling.bzl",
    "DARJEELING_OPENTITANTOOL_OPENOCD_DATA_DEPS",
    "DARJEELING_OPENTITANTOOL_OPENOCD_TEST_CMDS",
)
load("//rules:opentitan.bzl", "OPENTITAN_CPU")
load(
    "//rules:opentitan_test.bzl",
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
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:aes",
        "//sw/top_darjeeling/sw/test/utils:aes_testutils",
    ],
)

opentitan_functest(
    name = "aes_entropy_test",
    srcs = ["aes_entropy_test.c"],
    deps = [
        "//hw/ip/aes:model",
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:aes",
        "//sw/top_darjeeling/sw/test/utils:aes_testutils",
        "//sw/top_darjeeling/sw/test/utils:entropy_testutils",
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
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:aes",
        "//sw/top_darjeeling/sw/dif:clkmgr",
        "//sw/top_darjeeling/sw/test/utils:aes_testutils",
        "//sw/top_darjeeling/sw/test/utils:clkmgr_testutils",
        "//sw/top_darjeeling/sw/test/utils:entropy_testutils",
    ],
)

alias(
    name = "aes_smoketest_entropy_testutils",
    actual = select({
        "//sw/device:is_english_breakfast": "//sw/device:nothing",
        "//conditions:default": "//sw/top_darjeeling/sw/test/utils:entropy_testutils",
    }),
    visibility = ["//visibility:private"],
)

opentitan_functest(
    name = "aes_smoketest",
    srcs = ["aes_smoketest.c"],
    deps = [
        "//hw/ip/aes:model",
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:aes",
        "//sw/top_darjeeling/sw/test/utils:aes_testutils",
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
        "//hw/top_darjeeling:alert_handler_regs",
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:math",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/runtime:irq",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:alert_handler",
        "//sw/top_darjeeling/sw/dif:rv_core_ibex",
        "//sw/top_darjeeling/sw/dif:rv_plic",
        "//sw/top_darjeeling/sw/test/utils:alert_handler_testutils",
        "//sw/top_darjeeling/sw/test/utils:isr_testutils",
        "//sw/top_darjeeling/sw/test/utils:rv_plic_testutils",
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
        "//hw/top_darjeeling:alert_handler_regs",
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:math",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/runtime:irq",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:aes",
        "//sw/top_darjeeling/sw/dif:alert_handler",
        "//sw/top_darjeeling/sw/dif:clkmgr",
        "//sw/top_darjeeling/sw/dif:flash_ctrl",
        "//sw/top_darjeeling/sw/dif:hmac",
        "//sw/top_darjeeling/sw/dif:kmac",
        "//sw/top_darjeeling/sw/dif:otbn",
        "//sw/top_darjeeling/sw/dif:rstmgr",
        "//sw/top_darjeeling/sw/dif:rv_plic",
        "//sw/top_darjeeling/sw/dif:spi_host",
        "//sw/top_darjeeling/sw/test/utils:alert_handler_testutils",
        "//sw/top_darjeeling/sw/test/utils:flash_ctrl_testutils",
        "//sw/top_darjeeling/sw/test/utils:isr_testutils",
        "//sw/top_darjeeling/sw/test/utils:nv_counter_testutils",
        "//sw/top_darjeeling/sw/test/utils:rand_testutils",
        "//sw/top_darjeeling/sw/test/utils:rv_plic_testutils",
    ],
)

# opentitan_functest(
#     name = "alert_handler_reverse_ping_in_deep_sleep_test",
#     srcs = ["alert_handler_reverse_ping_in_deep_sleep_test.c"],
#     targets = [
#         "cw310_test_rom",
#         "dv",
#     ],
#     deps = [
#         "//hw/top_darjeeling:alert_handler_regs",
#         "//hw/top_darjeeling/sw/autogen:top_darjeeling",
#         "//sw/device/lib/testing/test_framework:ottf_main",
#         "//sw/lib/sw/device/base:math",
#         "//sw/lib/sw/device/base:mmio",
#         "//sw/lib/sw/device/runtime:ibex",
#         "//sw/lib/sw/device/runtime:irq",
#         "//sw/lib/sw/device/runtime:log",
#         "//sw/top_darjeeling/sw/device/runtime:print",
#         "//sw/top_darjeeling/sw/dif:alert_handler",
#         "//sw/top_darjeeling/sw/dif:aon_timer",
#         "//sw/top_darjeeling/sw/dif:flash_ctrl",
#         "//sw/top_darjeeling/sw/dif:pwrmgr",
#         "//sw/top_darjeeling/sw/dif:rstmgr",
#         "//sw/top_darjeeling/sw/dif:rv_plic",
#         "//sw/top_darjeeling/sw/test/utils:alert_handler_testutils",
#         "//sw/top_darjeeling/sw/test/utils:aon_timer_testutils",
#         "//sw/top_darjeeling/sw/test/utils:isr_testutils",
#         "//sw/top_darjeeling/sw/test/utils:keymgr_testutils",
#         "//sw/top_darjeeling/sw/test/utils:pwrmgr_testutils",
#         "//sw/top_darjeeling/sw/test/utils:rstmgr_testutils",
#         "//sw/top_darjeeling/sw/test/utils:rv_plic_testutils",
#     ],
# )

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
        "//hw/top_darjeeling:alert_handler_regs",
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:math",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/runtime:irq",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:alert_handler",
        "//sw/top_darjeeling/sw/dif:flash_ctrl",
        "//sw/top_darjeeling/sw/dif:i2c",
        "//sw/top_darjeeling/sw/dif:rstmgr",
        "//sw/top_darjeeling/sw/dif:rv_plic",
        "//sw/top_darjeeling/sw/dif:spi_device",
        "//sw/top_darjeeling/sw/dif:spi_host",
        "//sw/top_darjeeling/sw/test/utils:alert_handler_testutils",
        "//sw/top_darjeeling/sw/test/utils:flash_ctrl_testutils",
        "//sw/top_darjeeling/sw/test/utils:isr_testutils",
        "//sw/top_darjeeling/sw/test/utils:nv_counter_testutils",
        "//sw/top_darjeeling/sw/test/utils:rv_plic_testutils",
    ],
)

# opentitan_functest(
#     name = "alert_handler_lpg_sleep_mode_pings_test",
#     srcs = ["alert_handler_lpg_sleep_mode_pings.c"],
#     cw310 = cw310_params(
#         timeout = "moderate",
#     ),
#     targets = [
#         # The test requires the Ibex core to wait long enough
#         # before checking for the ping_timeout error.
#         # The wait-time for the Verilator would be around
#         # 4s (kClockFreqPeripheralHz = 125K).
#         # Thus it is not recommended to run this test on
#         # Verilator as this wait-time looks impractical. It should still
#         # be run as part of the DV nightly regression.
#         "cw310_test_rom",
#         "dv",
#     ],
#     deps = [
#         "//hw/top_darjeeling:alert_handler_regs",
#         "//hw/top_darjeeling/sw/autogen:top_darjeeling",
#         "//sw/device/lib/testing/test_framework:ottf_main",
#         "//sw/lib/sw/device/base:math",
#         "//sw/lib/sw/device/base:mmio",
#         "//sw/lib/sw/device/runtime:ibex",
#         "//sw/lib/sw/device/runtime:irq",
#         "//sw/lib/sw/device/runtime:log",
#         "//sw/top_darjeeling/sw/device/runtime:print",
#         "//sw/top_darjeeling/sw/dif:alert_handler",
#         "//sw/top_darjeeling/sw/dif:flash_ctrl",
#         "//sw/top_darjeeling/sw/dif:rstmgr",
#         "//sw/top_darjeeling/sw/dif:rv_plic",
#         "//sw/top_darjeeling/sw/test/utils:alert_handler_testutils",
#         "//sw/top_darjeeling/sw/test/utils:aon_timer_testutils",
#         "//sw/top_darjeeling/sw/test/utils:flash_ctrl_testutils",
#         "//sw/top_darjeeling/sw/test/utils:isr_testutils",
#         "//sw/top_darjeeling/sw/test/utils:keymgr_testutils",
#         "//sw/top_darjeeling/sw/test/utils:nv_counter_testutils",
#         "//sw/top_darjeeling/sw/test/utils:pwrmgr_testutils",
#         "//sw/top_darjeeling/sw/test/utils:rand_testutils",
#         "//sw/top_darjeeling/sw/test/utils:rstmgr_testutils",
#         "//sw/top_darjeeling/sw/test/utils:rv_plic_testutils",
#     ],
# )

opentitan_functest(
    name = "alert_handler_lpg_sleep_mode_alerts_test",
    srcs = ["alert_handler_lpg_sleep_mode_alerts.c"],
    targets = [
        # The test requires to drive fatal alerts
        # which is possible only in DV sim.
        "dv",
    ],
    deps = [
        "//hw/top_darjeeling:alert_handler_regs",
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:math",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/runtime:irq",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:alert_handler",
        "//sw/top_darjeeling/sw/dif:flash_ctrl",
        "//sw/top_darjeeling/sw/dif:rstmgr",
        "//sw/top_darjeeling/sw/dif:rv_plic",
        "//sw/top_darjeeling/sw/test/utils:alert_handler_testutils",
        "//sw/top_darjeeling/sw/test/utils:aon_timer_testutils",
        "//sw/top_darjeeling/sw/test/utils:flash_ctrl_testutils",
        "//sw/top_darjeeling/sw/test/utils:isr_testutils",
        "//sw/top_darjeeling/sw/test/utils:nv_counter_testutils",
        "//sw/top_darjeeling/sw/test/utils:pwrmgr_testutils",
        "//sw/top_darjeeling/sw/test/utils:rand_testutils",
        "//sw/top_darjeeling/sw/test/utils:rstmgr_testutils",
        "//sw/top_darjeeling/sw/test/utils:rv_plic_testutils",
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
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:math",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:irq",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:aon_timer",
        "//sw/top_darjeeling/sw/dif:rv_plic",
        "//sw/top_darjeeling/sw/dif:rv_timer",
        "//sw/top_darjeeling/sw/test/utils:aon_timer_testutils",
        "//sw/top_darjeeling/sw/test/utils:rand_testutils",
        "//sw/top_darjeeling/sw/test/utils:rv_plic_testutils",
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
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:aon_timer",
        "//sw/top_darjeeling/sw/test/utils:aon_timer_testutils",
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
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:math",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:aon_timer",
        "//sw/top_darjeeling/sw/dif:pwrmgr",
        "//sw/top_darjeeling/sw/dif:rstmgr",
        "//sw/top_darjeeling/sw/test/utils:aon_timer_testutils",
        "//sw/top_darjeeling/sw/test/utils:pwrmgr_testutils",
        "//sw/top_darjeeling/sw/test/utils:rstmgr_testutils",
    ],
)

opentitan_functest(
    name = "pwrmgr_wdog_reset_reqs_test",
    srcs = ["pwrmgr_wdog_reset_reqs_test.c"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:math",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:aon_timer",
        "//sw/top_darjeeling/sw/dif:pwrmgr",
        "//sw/top_darjeeling/sw/dif:rstmgr",
        "//sw/top_darjeeling/sw/test/utils:aon_timer_testutils",
        "//sw/top_darjeeling/sw/test/utils:pwrmgr_testutils",
        "//sw/top_darjeeling/sw/test/utils:rstmgr_testutils",
    ],
)

opentitan_functest(
    name = "aon_timer_wdog_lc_escalate_test",
    srcs = ["aon_timer_wdog_lc_escalate_test.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:math",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:irq",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:alert_handler",
        "//sw/top_darjeeling/sw/dif:aon_timer",
        "//sw/top_darjeeling/sw/dif:pwrmgr",
        "//sw/top_darjeeling/sw/dif:rstmgr",
        "//sw/top_darjeeling/sw/dif:rv_plic",
        "//sw/top_darjeeling/sw/dif:rv_timer",
        "//sw/top_darjeeling/sw/test/utils:alert_handler_testutils",
        "//sw/top_darjeeling/sw/test/utils:aon_timer_testutils",
        "//sw/top_darjeeling/sw/test/utils:rstmgr_testutils",
        "//sw/top_darjeeling/sw/test/utils:rv_plic_testutils",
    ],
)

opentitan_functest(
    name = "aon_timer_sleep_wdog_sleep_pause_test",
    srcs = ["aon_timer_sleep_wdog_sleep_pause_test.c"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:irq",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:aon_timer",
        "//sw/top_darjeeling/sw/dif:pwrmgr",
        "//sw/top_darjeeling/sw/dif:rstmgr",
        "//sw/top_darjeeling/sw/test/utils:aon_timer_testutils",
        "//sw/top_darjeeling/sw/test/utils:pwrmgr_testutils",
        "//sw/top_darjeeling/sw/test/utils:rstmgr_testutils",
    ],
)

cc_library(
    name = "clkmgr_external_clk_src_for_sw_impl",
    srcs = ["clkmgr_external_clk_src_for_sw_impl.c"],
    hdrs = ["clkmgr_external_clk_src_for_sw_impl.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:clkmgr",
        "//sw/top_darjeeling/sw/test/utils:aon_timer_testutils",
        "//sw/top_darjeeling/sw/test/utils:clkmgr_testutils",
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
        "//sw/top_darjeeling/sw/device/runtime:print",
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
        "//sw/top_darjeeling/sw/device/runtime:print",
    ],
)

opentitan_functest(
    name = "clkmgr_jitter_test",
    srcs = ["clkmgr_jitter_test.c"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:memory",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:clkmgr",
    ],
)

opentitan_functest(
    name = "clkmgr_off_peri_test",
    srcs = ["clkmgr_off_peri_test.c"],
    verilator = verilator_params(
        timeout = "eternal",
    ),
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:abs_mmio",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:aon_timer",
        "//sw/top_darjeeling/sw/dif:clkmgr",
        "//sw/top_darjeeling/sw/dif:flash_ctrl",
        "//sw/top_darjeeling/sw/dif:pwrmgr",
        "//sw/top_darjeeling/sw/dif:rstmgr",
        "//sw/top_darjeeling/sw/dif:spi_host",
        "//sw/top_darjeeling/sw/dif:uart",
        "//sw/top_darjeeling/sw/test/utils:aon_timer_testutils",
        "//sw/top_darjeeling/sw/test/utils:flash_ctrl_testutils",
        "//sw/top_darjeeling/sw/test/utils:nv_counter_testutils",
        "//sw/top_darjeeling/sw/test/utils:rstmgr_testutils",
    ],
)

cc_library(
    name = "clkmgr_off_trans_impl",
    srcs = ["clkmgr_off_trans_impl.c"],
    hdrs = ["clkmgr_off_trans_impl.h"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:aes",
        "//sw/top_darjeeling/sw/dif:aon_timer",
        "//sw/top_darjeeling/sw/dif:clkmgr",
        "//sw/top_darjeeling/sw/dif:hmac",
        "//sw/top_darjeeling/sw/dif:kmac",
        "//sw/top_darjeeling/sw/dif:otbn",
        "//sw/top_darjeeling/sw/dif:pwrmgr",
        "//sw/top_darjeeling/sw/dif:rstmgr",
        "//sw/top_darjeeling/sw/test/utils:aon_timer_testutils",
        "//sw/top_darjeeling/sw/test/utils:rstmgr_testutils",
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
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:sensor_ctrl",
        "//sw/top_darjeeling/sw/test/utils:aon_timer_testutils",
        "//sw/top_darjeeling/sw/test/utils:clkmgr_testutils",
        "//sw/top_darjeeling/sw/test/utils:rstmgr_testutils",
        "//sw/top_darjeeling/sw/test/utils:sensor_ctrl_testutils",
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
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:irq",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:rv_plic",
        "//sw/top_darjeeling/sw/dif:sensor_ctrl",
        "//sw/top_darjeeling/sw/test/utils:aon_timer_testutils",
        "//sw/top_darjeeling/sw/test/utils:clkmgr_testutils",
        "//sw/top_darjeeling/sw/test/utils:isr_testutils",
        "//sw/top_darjeeling/sw/test/utils:pwrmgr_testutils",
        "//sw/top_darjeeling/sw/test/utils:rv_plic_testutils",
        "//sw/top_darjeeling/sw/test/utils:sensor_ctrl_testutils",
    ],
)

opentitan_functest(
    name = "clkmgr_smoketest",
    srcs = ["clkmgr_smoketest.c"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:memory",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:clkmgr",
    ],
)

opentitan_functest(
    name = "coverage_test",
    srcs = ["coverage_test.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
    ],
)

opentitan_functest(
    name = "crt_test",
    srcs = ["crt_test.c"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_start",
        "//sw/device/lib/testing/test_framework:ottf_test_config",
        "//sw/device/lib/testing/test_framework:status",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:stdasm",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:uart",
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
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:csrng",
        "//sw/top_darjeeling/sw/dif:csrng_shared",
        "//sw/top_darjeeling/sw/dif:edn",
        "//sw/top_darjeeling/sw/test/utils:csrng_testutils",
        "//sw/top_darjeeling/sw/test/utils:entropy_testutils",
        "//sw/top_darjeeling/sw/test/utils:isr_testutils",
        "//sw/top_darjeeling/sw/test/utils:otbn_testutils",
        "//sw/top_darjeeling/sw/test/utils:rand_testutils",
        "//sw/top_darjeeling/sw/test/utils:rv_plic_testutils",
    ],
)

opentitan_functest(
    name = "csrng_kat_test",
    srcs = ["csrng_kat_test.c"],
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:csrng",
        "//sw/top_darjeeling/sw/test/utils:csrng_testutils",
    ],
)

opentitan_functest(
    name = "csrng_smoketest",
    srcs = ["csrng_smoketest.c"],
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:csrng",
        "//sw/top_darjeeling/sw/test/utils:csrng_testutils",
    ],
)

opentitan_functest(
    name = "dma_inline_hashing",
    srcs = ["dma_inline_hashing.c"],
    targets = [
        "dv",
    ],
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:dma",
        "//sw/top_darjeeling/sw/dif:spi_host",
        "//sw/top_darjeeling/sw/test/utils:dma_testutils",
        "//sw/top_darjeeling/sw/test/utils:isr_testutils",
        "//sw/top_darjeeling/sw/test/utils:pinmux_testutils",
    ],
)

opentitan_functest(
    name = "dma_abort",
    srcs = ["dma_abort.c"],
    targets = [
        "dv",
    ],
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:dma",
        "//sw/top_darjeeling/sw/dif:spi_host",
        "//sw/top_darjeeling/sw/test/utils:dma_testutils",
        "//sw/top_darjeeling/sw/test/utils:pinmux_testutils",
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
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:csrng",
        "//sw/top_darjeeling/sw/dif:edn",
        "//sw/top_darjeeling/sw/dif:otbn",
        "//sw/top_darjeeling/sw/test/utils:csrng_testutils",
        "//sw/top_darjeeling/sw/test/utils:entropy_testutils",
        "//sw/top_darjeeling/sw/test/utils:isr_testutils",
        "//sw/top_darjeeling/sw/test/utils:otbn_testutils",
        "//sw/top_darjeeling/sw/test/utils:rand_testutils",
        "//sw/top_darjeeling/sw/test/utils:rv_plic_testutils",
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
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:aes",
        "//sw/top_darjeeling/sw/dif:alert_handler",
        "//sw/top_darjeeling/sw/dif:entropy_src",
        "//sw/top_darjeeling/sw/dif:keymgr",
        "//sw/top_darjeeling/sw/dif:kmac",
        "//sw/top_darjeeling/sw/dif:otbn",
        "//sw/top_darjeeling/sw/dif:otp_ctrl",
        "//sw/top_darjeeling/sw/dif:pwrmgr",
        "//sw/top_darjeeling/sw/dif:rv_core_ibex",
        "//sw/top_darjeeling/sw/test/utils:aes_testutils",
        "//sw/top_darjeeling/sw/test/utils:alert_handler_testutils",
        "//sw/top_darjeeling/sw/test/utils:entropy_testutils",
        "//sw/top_darjeeling/sw/test/utils:keymgr_testutils",
        "//sw/top_darjeeling/sw/test/utils:otp_ctrl_testutils",
        "//sw/top_darjeeling/sw/test/utils:pwrmgr_testutils",
    ],
)

opentitan_functest(
    name = "example_concurrency_test",
    srcs = ["example_concurrency_test.c"],
    deps = [
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
    ],
)

opentitan_functest(
    name = "example_test_from_flash",
    srcs = ["example_test_from_flash.c"],
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/test/utils:rand_testutils",
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
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:status",
        "//sw/device/lib/testing/test_rom:linker_script",
        "//sw/device/lib/testing/test_rom:test_rom_lib",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:uart",
        "//sw/top_darjeeling/sw/test/utils:pinmux_testutils",
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
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/runtime:irq",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:aon_timer",
        "//sw/top_darjeeling/sw/dif:flash_ctrl",
        "//sw/top_darjeeling/sw/dif:pwrmgr",
        "//sw/top_darjeeling/sw/dif:rstmgr",
        "//sw/top_darjeeling/sw/dif:rv_plic",
        "//sw/top_darjeeling/sw/test/utils:flash_ctrl_testutils",
        "//sw/top_darjeeling/sw/test/utils:isr_testutils",
        "//sw/top_darjeeling/sw/test/utils:pwrmgr_testutils",
        "//sw/top_darjeeling/sw/test/utils:rand_testutils",
        "//sw/top_darjeeling/sw/test/utils:rstmgr_testutils",
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
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:irq",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:flash_ctrl",
        "//sw/top_darjeeling/sw/dif:rv_plic",
        "//sw/top_darjeeling/sw/test/utils:flash_ctrl_testutils",
        "//sw/top_darjeeling/sw/test/utils:isr_testutils",
        "//sw/top_darjeeling/sw/test/utils:rv_plic_testutils",
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
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:clkmgr",
        "//sw/top_darjeeling/sw/dif:flash_ctrl",
        "//sw/top_darjeeling/sw/test/utils:flash_ctrl_testutils",
        "//sw/top_darjeeling/sw/test/utils:rand_testutils",
    ],
)

opentitan_functest(
    name = "flash_ctrl_test",
    srcs = ["flash_ctrl_test.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:flash_ctrl",
        "//sw/top_darjeeling/sw/test/utils:flash_ctrl_testutils",
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
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:gpio",
        "//sw/top_darjeeling/sw/dif:pinmux",
        "//sw/top_darjeeling/sw/test/utils:pinmux_testutils",
    ],
)

# TODO: re-enable this test for verilator and the FPGA
# opentitan_functest(
#     name = "gpio_pinmux_test",
#     srcs = ["gpio_pinmux_test.c"],
#     cw310 = cw310_params(
#         interface = "hyper310",
#         tags = ["manual"],
#         test_cmds = [
#             "--bitstream=\"$(location {bitstream})\"",
#             "--bootstrap=\"$(location {flash})\"",
#         ],
#     ),
#     targets = [
#         "verilator",
#         "cw310_test_rom",
#     ],
#     test_harness = "//sw/host/tests/chip/gpio",
#     verilator = verilator_params(
#         timeout = "eternal",
#         test_cmds = [],
#     ),
#     deps = [
#         "//sw/device/lib/testing/json:command",
#         "//sw/device/lib/testing/json:gpio",
#         "//sw/device/lib/testing/json:pinmux_config",
#         "//sw/device/lib/testing/test_framework:ottf_main",
#         "//sw/top_darjeeling/sw/device/runtime:print",
#         "//sw/top_darjeeling/sw/dif:gpio",
#         "//sw/top_darjeeling/sw/dif:pinmux",
#     ],
# )

opentitan_functest(
    name = "hmac_enc_test",
    srcs = ["hmac_enc_test.c"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:hmac",
        "//sw/top_darjeeling/sw/test/utils:hmac_testutils",
        "//sw/top_darjeeling/sw/test/utils:isr_testutils",
        "//sw/top_darjeeling/sw/test/utils:rv_plic_testutils",
    ],
)

opentitan_functest(
    name = "hmac_enc_idle_test",
    srcs = ["hmac_enc_idle_test.c"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:clkmgr",
        "//sw/top_darjeeling/sw/dif:hmac",
        "//sw/top_darjeeling/sw/test/utils:clkmgr_testutils",
        "//sw/top_darjeeling/sw/test/utils:hmac_testutils",
    ],
)

opentitan_functest(
    name = "hmac_smoketest",
    srcs = ["hmac_smoketest.c"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:hmac",
        "//sw/top_darjeeling/sw/test/utils:hmac_testutils",
    ],
)

opentitan_functest(
    name = "keymgr_dpe_key_derivation_test",
    srcs = ["keymgr_dpe_key_derivation_test.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/ip/keymgr_dpe/data:keymgr_dpe_regs",
        "//hw/ip/kmac/data:kmac_regs",
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:keymgr_dpe",
        "//sw/top_darjeeling/sw/dif:kmac",
        "//sw/top_darjeeling/sw/test/utils:keymgr_dpe_testutils",
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
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:keymgr",
        "//sw/top_darjeeling/sw/dif:kmac",
        "//sw/top_darjeeling/sw/test/utils:keymgr_testutils",
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
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:aes",
        "//sw/top_darjeeling/sw/dif:keymgr",
        "//sw/top_darjeeling/sw/dif:kmac",
        "//sw/top_darjeeling/sw/test/utils:aes_testutils",
        "//sw/top_darjeeling/sw/test/utils:entropy_testutils",
        "//sw/top_darjeeling/sw/test/utils:keymgr_testutils",
        "//sw/top_darjeeling/sw/test/utils:kmac_testutils",
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
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:keymgr",
        "//sw/top_darjeeling/sw/dif:kmac",
        "//sw/top_darjeeling/sw/test/utils:keymgr_testutils",
        "//sw/top_darjeeling/sw/test/utils:kmac_testutils",
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
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/lib/sw/device/runtime:log",
        "//sw/otbn/crypto:x25519_sideload",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:keymgr",
        "//sw/top_darjeeling/sw/dif:otbn",
        "//sw/top_darjeeling/sw/test/utils:keymgr_testutils",
        "//sw/top_darjeeling/sw/test/utils:otbn_testutils",
    ],
)

opentitan_functest(
    name = "kmac_app_rom_test",
    srcs = ["kmac_app_rom_test.c"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:rom_ctrl",
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
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:irq",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:kmac",
    ],
)

opentitan_functest(
    name = "kmac_idle_test",
    srcs = ["kmac_idle_test.c"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:clkmgr",
        "//sw/top_darjeeling/sw/dif:kmac",
    ],
)

opentitan_functest(
    name = "kmac_mode_cshake_test",
    srcs = ["kmac_mode_cshake_test.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:kmac",
    ],
)

opentitan_functest(
    name = "kmac_mode_kmac_test",
    srcs = ["kmac_mode_kmac_test.c"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:kmac",
    ],
)

opentitan_functest(
    name = "kmac_smoketest",
    srcs = ["kmac_smoketest.c"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:kmac",
    ],
)

opentitan_functest(
    name = "lc_ctrl_otp_hw_cfg_test",
    srcs = ["lc_ctrl_otp_hw_cfg_test.c"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:lc_ctrl",
        "//sw/top_darjeeling/sw/dif:otp_ctrl",
        "//sw/top_darjeeling/sw/test/utils:otp_ctrl_testutils",
    ],
)

opentitan_functest(
    name = "mbx_smoketest",
    srcs = ["mbx_smoketest.c"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:mbx",
        "//sw/top_darjeeling/sw/dif:rv_plic",
        "//sw/top_darjeeling/sw/dif:sram_ctrl",
        "//sw/top_darjeeling/sw/test/utils:isr_testutils",
    ],
)

opentitan_functest(
    name = "otp_ctrl_nvm_cnt_test",
    srcs = ["otp_ctrl_nvm_cnt_test.c"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:otp_ctrl",
        "//sw/top_darjeeling/sw/dif:rstmgr",
        "//sw/top_darjeeling/sw/test/utils:otp_ctrl_testutils",
        "//sw/top_darjeeling/sw/test/utils:rstmgr_testutils",
    ],
)

opentitan_functest(
    name = "otp_ctrl_sw_parts_test",
    srcs = ["otp_ctrl_sw_parts_test.c"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:otp_ctrl",
        "//sw/top_darjeeling/sw/dif:rstmgr",
        "//sw/top_darjeeling/sw/test/utils:otp_ctrl_testutils",
        "//sw/top_darjeeling/sw/test/utils:rstmgr_testutils",
    ],
)

opentitan_functest(
    name = "otbn_ecdsa_op_irq_test",
    srcs = ["otbn_ecdsa_op_irq_test.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/ip/base/test/utils:profile",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/runtime:irq",
        "//sw/lib/sw/device/runtime:log",
        "//sw/otbn/crypto:p256_ecdsa",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:otbn",
        "//sw/top_darjeeling/sw/test/utils:entropy_testutils",
        "//sw/top_darjeeling/sw/test/utils:otbn_testutils",
        "//sw/top_darjeeling/sw/test/utils:rv_plic_testutils",
    ],
)

opentitan_functest(
    name = "otbn_irq_test",
    srcs = ["otbn_irq_test.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/runtime:irq",
        "//sw/lib/sw/device/runtime:log",
        "//sw/otbn/code-snippets:err_test",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:otbn",
        "//sw/top_darjeeling/sw/dif:rv_plic",
        "//sw/top_darjeeling/sw/test/utils:entropy_testutils",
        "//sw/top_darjeeling/sw/test/utils:otbn_testutils",
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
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:otbn",
        "//sw/top_darjeeling/sw/dif:rv_core_ibex",
        "//sw/top_darjeeling/sw/test/utils:otbn_testutils",
    ],
)

cc_library(
    name = "otbn_randomness_impl",
    srcs = ["otbn_randomness_impl.c"],
    hdrs = ["otbn_randomness_impl.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/testing/test_framework:check",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/runtime:log",
        "//sw/otbn/code-snippets:randomness",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:otbn",
        "//sw/top_darjeeling/sw/test/utils:otbn_testutils",
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
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/ip/base/dif:base",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/runtime:irq",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:clkmgr",
        "//sw/top_darjeeling/sw/dif:otbn",
        "//sw/top_darjeeling/sw/test/utils:clkmgr_testutils",
        "//sw/top_darjeeling/sw/test/utils:entropy_testutils",
        "//sw/top_darjeeling/sw/test/utils:otbn_testutils",
        "//sw/top_darjeeling/sw/test/utils:rv_plic_testutils",
    ],
)

opentitan_functest(
    name = "otbn_rsa_test",
    srcs = ["otbn_rsa_test.c"],
    verilator = verilator_params(
        timeout = "eternal",
    ),
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/ip/base/test/utils:profile",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/runtime:log",
        "//sw/otbn/crypto:rsa",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:otbn",
        "//sw/top_darjeeling/sw/test/utils:entropy_testutils",
        "//sw/top_darjeeling/sw/test/utils:otbn_testutils",
    ],
)

opentitan_functest(
    name = "otbn_smoketest",
    srcs = ["otbn_smoketest.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/runtime:log",
        "//sw/otbn/code-snippets:barrett384",
        "//sw/otbn/code-snippets:err_test",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:otbn",
        "//sw/top_darjeeling/sw/test/utils:entropy_testutils",
        "//sw/top_darjeeling/sw/test/utils:otbn_testutils",
    ],
)

opentitan_functest(
    name = "otp_ctrl_smoketest",
    srcs = ["otp_ctrl_smoketest.c"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:otp_ctrl",
        "//sw/top_darjeeling/sw/test/utils:otp_ctrl_testutils",
    ],
)

opentitan_functest(
    name = "plic_sw_irq_test",
    srcs = ["plic_sw_irq_test.c"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:abs_mmio",
        "//sw/lib/sw/device/base:math",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:irq",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:rv_plic",
        "//sw/top_darjeeling/sw/test/utils:rv_plic_testutils",
    ],
)

opentitan_functest(
    name = "pmp_smoketest_napot",
    srcs = ["pmp_smoketest_napot.c"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:csr",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/lib/sw/device/runtime:irq",
        "//sw/lib/sw/device/runtime:pmp",
        "//sw/top_darjeeling/sw/device/runtime:print",
    ],
)

opentitan_functest(
    name = "pmp_smoketest_tor",
    srcs = ["pmp_smoketest_tor.c"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:csr",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/lib/sw/device/runtime:irq",
        "//sw/lib/sw/device/runtime:pmp",
        "//sw/top_darjeeling/sw/device/runtime:print",
    ],
)

opentitan_functest(
    name = "pwrmgr_smoketest",
    srcs = ["pwrmgr_smoketest.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:aon_timer",
        "//sw/top_darjeeling/sw/dif:pwrmgr",
        "//sw/top_darjeeling/sw/dif:rstmgr",
        "//sw/top_darjeeling/sw/test/utils:aon_timer_testutils",
        "//sw/top_darjeeling/sw/test/utils:pwrmgr_testutils",
        "//sw/top_darjeeling/sw/test/utils:rstmgr_testutils",
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
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/runtime:irq",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:aon_timer",
        "//sw/top_darjeeling/sw/dif:pwrmgr",
        "//sw/top_darjeeling/sw/dif:rv_plic",
        "//sw/top_darjeeling/sw/test/utils:aon_timer_testutils",
        "//sw/top_darjeeling/sw/test/utils:pwrmgr_testutils",
    ],
)

opentitan_functest(
    name = "rstmgr_smoketest",
    srcs = ["rstmgr_smoketest.c"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:mmio",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:rstmgr",
        "//sw/top_darjeeling/sw/test/utils:rstmgr_testutils",
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
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:abs_mmio",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:pwrmgr",
        "//sw/top_darjeeling/sw/dif:rstmgr",
        "//sw/top_darjeeling/sw/dif:rv_core_ibex",
        "//sw/top_darjeeling/sw/test/utils:aon_timer_testutils",
        "//sw/top_darjeeling/sw/test/utils:rstmgr_testutils",
    ],
)

opentitan_functest(
    name = "rstmgr_sw_req_test",
    srcs = ["rstmgr_sw_req_test.c"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:rstmgr",
        "//sw/top_darjeeling/sw/test/utils:rstmgr_testutils",
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
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:i2c",
        "//sw/top_darjeeling/sw/dif:rstmgr",
        "//sw/top_darjeeling/sw/dif:spi_device",
        "//sw/top_darjeeling/sw/dif:spi_host",
    ],
)

opentitan_functest(
    name = "rv_plic_smoketest",
    srcs = ["rv_plic_smoketest.c"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:status",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/lib/sw/device/runtime:irq",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:rv_plic",
        "//sw/top_darjeeling/sw/dif:uart",
    ],
)

opentitan_functest(
    name = "rv_timer_smoketest",
    srcs = ["rv_timer_smoketest.c"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/runtime:irq",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:rv_timer",
    ],
)

opentitan_functest(
    name = "soc_proxy_smoketest",
    srcs = ["soc_proxy_smoketest.c"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/lib/sw/device/runtime:irq",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:pwrmgr",
        "//sw/top_darjeeling/sw/dif:rstmgr",
        "//sw/top_darjeeling/sw/dif:rv_plic",
        "//sw/top_darjeeling/sw/dif:soc_proxy",
        "//sw/top_darjeeling/sw/test/utils:rstmgr_testutils",
    ],
)

opentitan_functest(
    name = "soc_proxy_external_alerts",
    srcs = ["soc_proxy_external_alerts.c"],
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:alert_handler",
        "//sw/top_darjeeling/sw/dif:rstmgr",
        "//sw/top_darjeeling/sw/dif:soc_proxy",
        "//sw/top_darjeeling/sw/test/utils:alert_handler_testutils",
    ],
)

opentitan_functest(
    name = "soc_proxy_external_wakeup",
    srcs = ["soc_proxy_external_wakeup.c"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:status",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/lib/sw/device/runtime:irq",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:pwrmgr",
        "//sw/top_darjeeling/sw/dif:rv_plic",
        "//sw/top_darjeeling/sw/test/utils:isr_testutils",
        "//sw/top_darjeeling/sw/test/utils:rv_plic_testutils",
    ],
)

opentitan_functest(
    name = "soc_proxy_gpios",
    srcs = ["soc_proxy_gpios.c"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:status",
        "//sw/lib/sw/device/runtime:irq",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:pinmux",
        "//sw/top_darjeeling/sw/dif:rv_plic",
        "//sw/top_darjeeling/sw/dif:soc_proxy",
    ],
)

cc_library(
    name = "spi_host_flash_test_impl",
    srcs = ["spi_host_flash_test_impl.c"],
    hdrs = ["spi_host_flash_test_impl.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:spi_host",
        "//sw/top_darjeeling/sw/test/utils:spi_device_testutils",
        "//sw/top_darjeeling/sw/test/utils:spi_flash_testutils",
        "//sw/top_darjeeling/sw/test/utils:spi_host_testutils",
    ],
)

opentitan_functest(
    name = "spi_host_smoketest",
    srcs = ["spi_host_smoketest.c"],
    cw310 = cw310_params(
        timeout = "moderate",
    ),
    targets = ["cw310_test_rom"],  # Can only run on CW310 board right now.
    deps = [
        ":spi_host_flash_test_impl",
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:spi_host",
        "//sw/top_darjeeling/sw/test/utils:spi_device_testutils",
        "//sw/top_darjeeling/sw/test/utils:spi_flash_testutils",
        "//sw/top_darjeeling/sw/test/utils:spi_host_testutils",
    ],
)

opentitan_functest(
    name = "spi_host_winbond_flash_test",
    srcs = ["spi_host_winbond_flash_test.c"],
    targets = ["cw310_test_rom"],  # Can only run on CW310 board right now.
    deps = [
        ":spi_host_flash_test_impl",
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:spi_host",
        "//sw/top_darjeeling/sw/test/utils:spi_device_testutils",
        "//sw/top_darjeeling/sw/test/utils:spi_flash_testutils",
        "//sw/top_darjeeling/sw/test/utils:spi_host_testutils",
    ],
)

# opentitan_functest(
#     name = "spi_host_irq_test",
#     srcs = ["spi_host_irq_test.c"],
#     targets = ["cw310_test_rom"],  # Can only run on CW310 board right now.
#     deps = [
#         "//hw/top_darjeeling/sw/autogen:top_darjeeling",
#         "//sw/device/lib/testing/test_framework:ottf_main",
#         "//sw/lib/sw/device/arch:device",
#         "//sw/lib/sw/device/base:memory",
#         "//sw/lib/sw/device/base:mmio",
#         "//sw/lib/sw/device/runtime:hart",
#         "//sw/lib/sw/device/runtime:log",
#         "//sw/top_darjeeling/sw/device/runtime:print",
#         "//sw/top_darjeeling/sw/dif:rv_plic",
#         "//sw/top_darjeeling/sw/dif:spi_host",
#         "//sw/top_darjeeling/sw/test/utils:rv_plic_testutils",
#         "//sw/top_darjeeling/sw/test/utils:spi_device_testutils",
#         "//sw/top_darjeeling/sw/test/utils:spi_flash_testutils",
#         "//sw/top_darjeeling/sw/test/utils:spi_host_testutils",
#     ],
# )
#
# # opentitan_functest(
#     name = "i2c_host_accelerometer_test",
#     srcs = ["i2c_host_accelerometer_test.c"],
#     cw310 = cw310_params(
#         tags = [
#             "bob",
#             "manual",
#         ],  # Requires the BoB in CI.
#     ),
#     targets = ["cw310_test_rom"],  # Can only run on CW310 board right now.
#     deps = [
#         "//hw/top_darjeeling/sw/autogen:top_darjeeling",
#         "//sw/device/lib/testing/test_framework:ottf_main",
#         "//sw/lib/sw/device/arch:device",
#         "//sw/lib/sw/device/base:memory",
#         "//sw/lib/sw/device/base:mmio",
#         "//sw/lib/sw/device/runtime:hart",
#         "//sw/lib/sw/device/runtime:log",
#         "//sw/top_darjeeling/sw/device/runtime:print",
#         "//sw/top_darjeeling/sw/dif:i2c",
#         "//sw/top_darjeeling/sw/test/utils:i2c_testutils",
#         "//sw/top_darjeeling/sw/test/utils:rv_core_ibex_testutils",
#     ],
# )

# opentitan_functest(
#     name = "i2c_host_ambient_light_detector_test",
#     srcs = ["i2c_host_ambient_light_detector_test.c"],
#     cw310 = cw310_params(
#         tags = [
#             "bob",
#             "manual",
#         ],  # Requires the BoB in CI.
#     ),
#     targets = ["cw310_test_rom"],  # Can only run on CW310 board right now.
#     deps = [
#         "//hw/top_darjeeling/sw/autogen:top_darjeeling",
#         "//sw/device/lib/testing/test_framework:ottf_main",
#         "//sw/lib/sw/device/arch:device",
#         "//sw/lib/sw/device/base:memory",
#         "//sw/lib/sw/device/base:mmio",
#         "//sw/lib/sw/device/runtime:hart",
#         "//sw/lib/sw/device/runtime:log",
#         "//sw/top_darjeeling/sw/device/runtime:print",
#         "//sw/top_darjeeling/sw/dif:i2c",
#         "//sw/top_darjeeling/sw/test/utils:i2c_testutils",
#         "//sw/top_darjeeling/sw/test/utils:rv_core_ibex_testutils",
#     ],
# )

# opentitan_functest(
#     name = "i2c_host_hdc1080_humidity_temp_test",
#     srcs = ["i2c_host_hdc1080_humidity_temp_test.c"],
#     cw310 = cw310_params(
#         tags = [
#             "bob",
#             "manual",
#         ],  # Requires the BoB in CI.
#     ),
#     targets = ["cw310_test_rom"],  # Can only run on CW310 board right now.
#     deps = [
#         "//hw/top_darjeeling/sw/autogen:top_darjeeling",
#         "//sw/device/lib/testing/test_framework:ottf_main",
#         "//sw/lib/sw/device/arch:device",
#         "//sw/lib/sw/device/base:memory",
#         "//sw/lib/sw/device/base:mmio",
#         "//sw/lib/sw/device/runtime:hart",
#         "//sw/lib/sw/device/runtime:log",
#         "//sw/top_darjeeling/sw/device/runtime:print",
#         "//sw/top_darjeeling/sw/dif:i2c",
#         "//sw/top_darjeeling/sw/test/utils:i2c_testutils",
#         "//sw/top_darjeeling/sw/test/utils:rv_core_ibex_testutils",
#     ],
# )

# opentitan_functest(
#     name = "i2c_host_clock_stretching_test",
#     srcs = ["i2c_host_clock_stretching_test.c"],
#     cw310 = cw310_params(
#         tags = [
#             "bob",
#             "manual",
#         ],  # Requires the BoB in CI.
#     ),
#     targets = ["cw310_test_rom"],  # Can only run on CW310 board right now.
#     deps = [
#         "//hw/top_darjeeling/sw/autogen:top_darjeeling",
#         "//sw/device/lib/testing/test_framework:ottf_main",
#         "//sw/lib/sw/device/arch:device",
#         "//sw/lib/sw/device/base:memory",
#         "//sw/lib/sw/device/base:mmio",
#         "//sw/lib/sw/device/runtime:hart",
#         "//sw/lib/sw/device/runtime:log",
#         "//sw/top_darjeeling/sw/device/runtime:print",
#         "//sw/top_darjeeling/sw/dif:i2c",
#         "//sw/top_darjeeling/sw/dif:rv_plic",
#         "//sw/top_darjeeling/sw/test/utils:i2c_testutils",
#         "//sw/top_darjeeling/sw/test/utils:rv_core_ibex_testutils",
#         "//sw/top_darjeeling/sw/test/utils:rv_plic_testutils",
#     ],
# )

# opentitan_functest(
#     name = "i2c_host_compass_test",
#     srcs = ["i2c_host_compass_test.c"],
#     cw310 = cw310_params(
#         tags = [
#             "bob",
#             "manual",
#         ],  # Requires the BoB in CI.
#     ),
#     targets = ["cw310_test_rom"],  # Can only run on CW310 board right now.
#     deps = [
#         "//hw/top_darjeeling/sw/autogen:top_darjeeling",
#         "//sw/device/lib/testing/test_framework:ottf_main",
#         "//sw/lib/sw/device/arch:device",
#         "//sw/lib/sw/device/base:memory",
#         "//sw/lib/sw/device/base:mmio",
#         "//sw/lib/sw/device/runtime:hart",
#         "//sw/lib/sw/device/runtime:log",
#         "//sw/top_darjeeling/sw/device/runtime:print",
#         "//sw/top_darjeeling/sw/dif:i2c",
#         "//sw/top_darjeeling/sw/dif:rstmgr",
#         "//sw/top_darjeeling/sw/test/utils:i2c_testutils",
#         "//sw/top_darjeeling/sw/test/utils:rv_core_ibex_testutils",
#     ],
# )

# opentitan_functest(
#     name = "i2c_host_eeprom_test",
#     srcs = ["i2c_host_eeprom_test.c"],
#     cw310 = cw310_params(
#         tags = [
#             "bob",
#             "manual",
#         ],  # Requires the BoB in CI.
#     ),
#     targets = ["cw310_test_rom"],  # Can only run on CW310 board right now.
#     deps = [
#         "//hw/top_darjeeling/sw/autogen:top_darjeeling",
#         "//sw/device/lib/testing/test_framework:ottf_main",
#         "//sw/lib/sw/device/arch:device",
#         "//sw/lib/sw/device/base:memory",
#         "//sw/lib/sw/device/base:mmio",
#         "//sw/lib/sw/device/runtime:hart",
#         "//sw/lib/sw/device/runtime:log",
#         "//sw/top_darjeeling/sw/device/runtime:print",
#         "//sw/top_darjeeling/sw/dif:i2c",
#         "//sw/top_darjeeling/sw/test/utils:i2c_testutils",
#         "//sw/top_darjeeling/sw/test/utils:rv_core_ibex_testutils",
#     ],
# )
#
# opentitan_functest(
#     name = "i2c_host_fram_test",
#     srcs = ["i2c_host_fram_test.c"],
#     cw310 = cw310_params(
#         tags = [
#             "bob",
#             "manual",
#         ],  # Requires the BoB in CI.
#     ),
#     targets = ["cw310_test_rom"],  # Can only run on CW310 board right now.
#     deps = [
#         "//hw/top_darjeeling/sw/autogen:top_darjeeling",
#         "//sw/device/lib/testing/test_framework:ottf_main",
#         "//sw/lib/sw/device/arch:device",
#         "//sw/lib/sw/device/base:memory",
#         "//sw/lib/sw/device/base:mmio",
#         "//sw/lib/sw/device/runtime:hart",
#         "//sw/lib/sw/device/runtime:log",
#         "//sw/top_darjeeling/sw/device/runtime:print",
#         "//sw/top_darjeeling/sw/dif:i2c",
#         "//sw/top_darjeeling/sw/test/utils:i2c_testutils",
#         "//sw/top_darjeeling/sw/test/utils:rv_core_ibex_testutils",
#     ],
# )
#
# opentitan_functest(
#     name = "i2c_host_gas_sensor_test",
#     srcs = ["i2c_host_gas_sensor_test.c"],
#     cw310 = cw310_params(
#         tags = [
#             "bob",
#             "manual",
#         ],  # Requires the BoB in CI.
#     ),
#     targets = ["cw310_test_rom"],  # Can only run on CW310 board right now.
#     deps = [
#         "//hw/top_darjeeling/sw/autogen:top_darjeeling",
#         "//sw/device/lib/testing/test_framework:ottf_main",
#         "//sw/lib/sw/device/arch:device",
#         "//sw/lib/sw/device/base:memory",
#         "//sw/lib/sw/device/base:mmio",
#         "//sw/lib/sw/device/runtime:hart",
#         "//sw/lib/sw/device/runtime:log",
#         "//sw/top_darjeeling/sw/device/runtime:print",
#         "//sw/top_darjeeling/sw/dif:i2c",
#         "//sw/top_darjeeling/sw/test/utils:i2c_testutils",
#         "//sw/top_darjeeling/sw/test/utils:rv_core_ibex_testutils",
#     ],
# )

# opentitan_functest(
#     name = "i2c_host_power_monitor_test",
#     srcs = ["i2c_host_power_monitor_test.c"],
#     cw310 = cw310_params(
#         tags = [
#             "bob",
#             "manual",
#         ],  # Requires the BoB in CI.
#     ),
#     targets = ["cw310_test_rom"],  # Can only run on CW310 board right now.
#     deps = [
#         "//hw/top_darjeeling/sw/autogen:top_darjeeling",
#         "//sw/device/lib/testing/test_framework:ottf_main",
#         "//sw/lib/sw/device/arch:device",
#         "//sw/lib/sw/device/base:memory",
#         "//sw/lib/sw/device/base:mmio",
#         "//sw/lib/sw/device/runtime:hart",
#         "//sw/lib/sw/device/runtime:log",
#         "//sw/top_darjeeling/sw/device/runtime:print",
#         "//sw/top_darjeeling/sw/dif:i2c",
#         "//sw/top_darjeeling/sw/test/utils:i2c_testutils",
#         "//sw/top_darjeeling/sw/test/utils:rv_core_ibex_testutils",
#     ],
# )

# opentitan_functest(
#     name = "i2c_host_irq_test",
#     srcs = ["i2c_host_irq_test.c"],
#     cw310 = cw310_params(
#         tags = [
#             "bob",
#             "manual",
#         ],  # Requires the BoB in CI.
#     ),
#     targets = ["cw310_test_rom"],  # Can only run on CW310 board right now.
#     deps = [
#         "//hw/top_darjeeling/sw/autogen:top_darjeeling",
#         "//sw/device/lib/testing/test_framework:ottf_main",
#         "//sw/lib/sw/device/arch:device",
#         "//sw/lib/sw/device/base:memory",
#         "//sw/lib/sw/device/base:mmio",
#         "//sw/lib/sw/device/runtime:hart",
#         "//sw/lib/sw/device/runtime:log",
#         "//sw/top_darjeeling/sw/device/runtime:print",
#         "//sw/top_darjeeling/sw/dif:i2c",
#         "//sw/top_darjeeling/sw/dif:rv_plic",
#         "//sw/top_darjeeling/sw/test/utils:i2c_testutils",
#         "//sw/top_darjeeling/sw/test/utils:rv_core_ibex_testutils",
#         "//sw/top_darjeeling/sw/test/utils:rv_plic_testutils",
#     ],
# )

opentitan_functest(
    name = "sensor_ctrl_alert_test",
    srcs = ["sensor_ctrl_alerts.c"],
    deps = [
        "//hw/top_darjeeling/ip/sensor_ctrl/data:sensor_ctrl_regs",
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:abs_mmio",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/runtime:irq",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:alert_handler",
        "//sw/top_darjeeling/sw/dif:rstmgr",
        "//sw/top_darjeeling/sw/dif:rv_plic",
        "//sw/top_darjeeling/sw/dif:sensor_ctrl",
        "//sw/top_darjeeling/sw/test/utils:flash_ctrl_testutils",
        "//sw/top_darjeeling/sw/test/utils:nv_counter_testutils",
        "//sw/top_darjeeling/sw/test/utils:pwrmgr_testutils",
        "//sw/top_darjeeling/sw/test/utils:rand_testutils",
    ],
)

opentitan_functest(
    name = "sensor_ctrl_wakeup_test",
    srcs = ["sensor_ctrl_wakeup.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/top_darjeeling/ip/sensor_ctrl/data:sensor_ctrl_regs",
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/lib/sw/device/runtime:irq",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:pwrmgr",
        "//sw/top_darjeeling/sw/dif:rv_plic",
        "//sw/top_darjeeling/sw/dif:sensor_ctrl",
        "//sw/top_darjeeling/sw/test/utils:isr_testutils",
        "//sw/top_darjeeling/sw/test/utils:pwrmgr_testutils",
        "//sw/top_darjeeling/sw/test/utils:rv_plic_testutils",
    ],
)

opentitan_functest(
    name = "sram_ctrl_execution_test",
    srcs = ["sram_ctrl_execution_test.c"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/examples/sram_program",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:csr",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/runtime:log",
        "//sw/lib/sw/device/silicon_creator:epmp_state",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:sram_ctrl",
    ],
)

opentitan_functest(
    name = "sram_ctrl_sleep_sram_ret_contents_test",
    srcs = ["sram_ctrl_sleep_sram_ret_contents_test.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/lib/sw/device/base:mmio",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:aon_timer",
        "//sw/top_darjeeling/sw/dif:flash_ctrl",
        "//sw/top_darjeeling/sw/dif:pwrmgr",
        "//sw/top_darjeeling/sw/dif:rstmgr",
        "//sw/top_darjeeling/sw/test/utils:aon_timer_testutils",
        "//sw/top_darjeeling/sw/test/utils:flash_ctrl_testutils",
        "//sw/top_darjeeling/sw/test/utils:isr_testutils",
        "//sw/top_darjeeling/sw/test/utils:pwrmgr_testutils",
        "//sw/top_darjeeling/sw/test/utils:rstmgr_testutils",
        "//sw/top_darjeeling/sw/test/utils:rv_plic_testutils",
        "//sw/top_darjeeling/sw/test/utils:sram_ctrl_testutils",
    ],
)

opentitan_functest(
    name = "sram_ctrl_smoketest",
    srcs = ["sram_ctrl_smoketest.c"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:sram_ctrl",
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
        "cw310_rom_with_fake_keys",
        "verilator",
        "dv",
    ],
    verilator = verilator_params(
        timeout = "eternal",
        exit_failure = ROM_BOOT_FAILURE_MSG,
        rom = "//sw/device/silicon_creator/rom:rom_with_fake_keys",
    ),
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:uart",
    ],
)

opentitan_functest(
    name = "uart_smoketest",
    srcs = ["uart_smoketest.c"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:uart",
    ],
)

# TODO(#500) Enable tests once build system for darjeeling does not attempt to build them
# opentitan_functest(
#     name = "usbdev_test",
#     srcs = ["usbdev_test.c"],
#     cw310 = cw310_params(
#         tags = ["manual"],
#     ),
#     tags = ["earlgrey"],
#     targets = [
#         "verilator",
#         "cw310_test_rom",
#         "dv",
#     ],
#     verilator = verilator_params(
#         timeout = "long",
#     ),
#     deps = [
#         "//hw/top_darjeeling/sw/autogen:top_darjeeling",
#         "//sw/device/lib/testing/test_framework:ottf_main",
#         "//sw/lib/sw/device/runtime:log",
#         "//sw/top_darjeeling/sw/device/runtime:print",
#         "//sw/top_darjeeling/sw/dif:pinmux",
#         "//sw/top_darjeeling/sw/dif:usbdev",
#         "//sw/top_darjeeling/sw/test/utils:pinmux_testutils",
#         "//sw/top_darjeeling/sw/test/utils:usb_testutils",
#         "//sw/top_darjeeling/sw/test/utils:usb_testutils_simpleserial",
#     ],
# )

# opentitan_functest(
#     name = "usbdev_mixed_test",
#     srcs = ["usbdev_mixed_test.c"],
#     tags = ["earlgrey"],
#     targets = [
#         "verilator",
#         "dv",
#     ],
#     verilator = verilator_params(
#         timeout = "long",
#     ),
#     deps = [
#         "//hw/top_darjeeling/sw/autogen:top_darjeeling",
#         "//sw/device/lib/testing/test_framework:ottf_main",
#         "//sw/lib/sw/device/runtime:log",
#         "//sw/top_darjeeling/sw/device/runtime:print",
#         "//sw/top_darjeeling/sw/dif:pinmux",
#         "//sw/top_darjeeling/sw/test/utils:pinmux_testutils",
#         "//sw/top_darjeeling/sw/test/utils:usb_testutils",
#         "//sw/top_darjeeling/sw/test/utils:usb_testutils_streams",
#     ],
# )

# opentitan_functest(
#     name = "usbdev_iso_test",
#     srcs = ["usbdev_iso_test.c"],
#     tags = ["earlgrey"],
#     targets = [
#         "verilator",
#         "dv",
#     ],
#     verilator = verilator_params(
#         timeout = "long",
#     ),
#     deps = [
#         "//hw/top_darjeeling/sw/autogen:top_darjeeling",
#         "//sw/device/lib/testing/test_framework:ottf_main",
#         "//sw/lib/sw/device/runtime:log",
#         "//sw/top_darjeeling/sw/device/runtime:print",
#         "//sw/top_darjeeling/sw/dif:pinmux",
#         "//sw/top_darjeeling/sw/test/utils:pinmux_testutils",
#         "//sw/top_darjeeling/sw/test/utils:usb_testutils",
#         "//sw/top_darjeeling/sw/test/utils:usb_testutils_streams",
#     ],
# )

# opentitan_functest(
#     name = "usbdev_stream_test",
#     srcs = ["usbdev_stream_test.c"],
#     cw310 = cw310_params(
#         timeout = "eternal",
#         tags = ["manual"],
#     ),
#     tags = ["earlgrey"],
#     targets = [
#         "verilator",
#         "cw310_test_rom",
#         "dv",
#     ],
#     verilator = verilator_params(
#         timeout = "long",
#     ),
#     deps = [
#         "//hw/top_darjeeling/sw/autogen:top_darjeeling",
#         "//sw/device/lib/testing/test_framework:ottf_main",
#         "//sw/lib/sw/device/runtime:log",
#         "//sw/top_darjeeling/sw/device/runtime:print",
#         "//sw/top_darjeeling/sw/dif:pinmux",
#         "//sw/top_darjeeling/sw/test/utils:pinmux_testutils",
#         "//sw/top_darjeeling/sw/test/utils:usb_testutils",
#         "//sw/top_darjeeling/sw/test/utils:usb_testutils_streams",
#     ],
# )

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
        "//hw/top_darjeeling:alert_handler_regs",
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:alert_handler",
        "//sw/top_darjeeling/sw/dif:aon_timer",
        "//sw/top_darjeeling/sw/dif:i2c",
        "//sw/top_darjeeling/sw/dif:otp_ctrl",
        "//sw/top_darjeeling/sw/dif:pwrmgr",
        "//sw/top_darjeeling/sw/dif:rstmgr",
        "//sw/top_darjeeling/sw/dif:rv_core_ibex",
        "//sw/top_darjeeling/sw/dif:rv_plic",
        "//sw/top_darjeeling/sw/dif:rv_timer",
        "//sw/top_darjeeling/sw/dif:spi_host",
        "//sw/top_darjeeling/sw/dif:uart",
        "//sw/top_darjeeling/sw/test/utils:alert_handler_testutils",
        "//sw/top_darjeeling/sw/test/utils:aon_timer_testutils",
        "//sw/top_darjeeling/sw/test/utils:keymgr_testutils",
        "//sw/top_darjeeling/sw/test/utils:ret_sram_testutils",
        "//sw/top_darjeeling/sw/test/utils:rstmgr_testutils",
        "//sw/top_darjeeling/sw/test/utils:rv_plic_testutils",
    ],
)

opentitan_functest(
    name = "rv_core_ibex_rnd_test",
    srcs = [
        "rv_core_ibex_rnd_test.S",
        "rv_core_ibex_rnd_test.c",
    ],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:edn",
        "//sw/top_darjeeling/sw/dif:rv_core_ibex",
        "//sw/top_darjeeling/sw/test/utils:entropy_testutils",
        "//sw/top_darjeeling/sw/test/utils:rv_core_ibex_testutils",
    ],
)

opentitan_functest(
    name = "rv_core_ibex_address_translation_test",
    srcs = [
        "rv_core_ibex_address_translation_test.S",
        "rv_core_ibex_address_translation_test.c",
    ],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:csr",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/runtime:log",
        "//sw/lib/sw/device/silicon_creator:epmp_state",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:rv_core_ibex",
    ],
)

opentitan_functest(
    name = "rv_core_ibex_nmi_irq_test",
    srcs = ["rv_core_ibex_nmi_irq_test.c"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/runtime:irq",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:alert_handler",
        "//sw/top_darjeeling/sw/dif:aon_timer",
        "//sw/top_darjeeling/sw/dif:rv_core_ibex",
        "//sw/top_darjeeling/sw/test/utils:alert_handler_testutils",
        "//sw/top_darjeeling/sw/test/utils:aon_timer_testutils",
        "//sw/top_darjeeling/sw/test/utils:isr_testutils",
        "//sw/top_darjeeling/sw/test/utils:pwrmgr_testutils",
    ],
)

opentitan_functest(
    name = "rv_core_ibex_icache_invalidate_test",
    srcs = ["rv_core_ibex_icache_invalidate_test.c"],
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/runtime:hart",
        "//sw/top_darjeeling/sw/device/runtime:print",
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
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:sensor_ctrl",
        "//sw/top_darjeeling/sw/test/utils:aon_timer_testutils",
        "//sw/top_darjeeling/sw/test/utils:clkmgr_testutils",
        "//sw/top_darjeeling/sw/test/utils:pwrmgr_testutils",
        "//sw/top_darjeeling/sw/test/utils:sensor_ctrl_testutils",
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
    src = "//hw/top_darjeeling/bitstream:test_rom",
    data = ":power_virus_systemtest_otp_img_rma",
    meminfo = "//hw/top_darjeeling/bitstream:otp_mmi",
    update_usr_access = True,
    visibility = ["//visibility:private"],
)

opentitan_functest(
    name = "power_virus_systemtest",
    srcs = ["power_virus_systemtest.c"],
    cw310 = cw310_params(
        bitstream = ":power_virus_systemtest_bitstream",
        test_cmds = [
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
        "//hw/ip/aes:model",
        "//hw/ip/aes/data:aes_regs",
        "//hw/ip/csrng/data:csrng_regs",
        "//hw/ip/gpio/data:gpio_regs",
        "//hw/ip/hmac/data:hmac_regs",
        "//hw/ip/i2c/data:i2c_regs",
        "//hw/ip/kmac/data:kmac_regs",
        "//hw/ip/pattgen/data:pattgen_regs",
        "//hw/ip/pwm/data:pwm_regs",
        "//hw/ip/spi_host/data:spi_host_regs",
        "//hw/ip/uart/data:uart_regs",
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/impl/rsa:rsa_3072_verify",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/tests/crypto:rsa_3072_verify_testvectors_hardcoded_header",
        "//sw/lib/sw/device/base:math",
        "//sw/lib/sw/device/base:multibits",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:aes",
        "//sw/top_darjeeling/sw/dif:csrng",
        "//sw/top_darjeeling/sw/dif:csrng_shared",
        "//sw/top_darjeeling/sw/dif:edn",
        "//sw/top_darjeeling/sw/dif:gpio",
        "//sw/top_darjeeling/sw/dif:hmac",
        "//sw/top_darjeeling/sw/dif:i2c",
        "//sw/top_darjeeling/sw/dif:kmac",
        "//sw/top_darjeeling/sw/dif:otbn",
        "//sw/top_darjeeling/sw/dif:pattgen",
        "//sw/top_darjeeling/sw/dif:pinmux",
        "//sw/top_darjeeling/sw/dif:pwm",
        "//sw/top_darjeeling/sw/dif:rv_plic",
        "//sw/top_darjeeling/sw/dif:spi_device",
        "//sw/top_darjeeling/sw/dif:spi_host",
        "//sw/top_darjeeling/sw/dif:uart",
        "//sw/top_darjeeling/sw/test/utils:aes_testutils",
        "//sw/top_darjeeling/sw/test/utils:entropy_testutils",
        "//sw/top_darjeeling/sw/test/utils:hmac_testutils",
        "//sw/top_darjeeling/sw/test/utils:i2c_testutils",
        "//sw/top_darjeeling/sw/test/utils:pinmux_testutils",
        "//sw/top_darjeeling/sw/test/utils:spi_device_testutils",
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
            "--bitstream=\"$(location {bitstream})\"",
            "--bootstrap=\"$(location {flash})\"",
        ],
    ),
    targets = [
        "cw310_test_rom",
    ],
    test_harness = "//sw/host/tests/chip/spi_passthru",
    deps = [
        "//sw/device/lib/testing/json:command",
        "//sw/device/lib/testing/json:spi_passthru",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/lib/sw/device/arch:device",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:gpio",
        "//sw/top_darjeeling/sw/dif:spi_device",
        "//sw/top_darjeeling/sw/test/utils:spi_device_testutils",
        "//sw/top_darjeeling/sw/test/utils:spi_flash_testutils",
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
        "//sw/top_darjeeling/sw/device/runtime:print",
    ],
)

opentitan_functest(
    name = "openocd_test",
    srcs = ["example_test_from_flash.c"],
    cw310 = cw310_params(
        bitstream = "//hw/top_darjeeling/bitstream:" +
                    "rom_with_fake_keys_otp_test_unlocked0",
        test_cmds = [
            "--bitstream=\"$(rootpath {bitstream})\"",
            "--bootstrap=\"$(rootpath {flash})\"",
        ] + DARJEELING_OPENTITANTOOL_OPENOCD_TEST_CMDS,
    ),
    data = DARJEELING_OPENTITANTOOL_OPENOCD_DATA_DEPS,
    targets = [
        #"verilator",
        "cw310_rom_with_fake_keys",
    ],
    test_harness = "//sw/host/tests/chip/jtag:openocd_test",
    verilator = verilator_params(
        timeout = "long",
        test_cmds = [
            "--reset-delay=\"120sec\"",
            "--bootstrap=\"$(rootpath {flash})\"",
        ] + DARJEELING_OPENTITANTOOL_OPENOCD_TEST_CMDS,
    ),
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
    ],
)

opentitan_functest(
    name = "spi_device_ottf_console_test",
    srcs = ["spi_device_ottf_console_test.c"],
    cw310 = cw310_params(
        interface = "hyper310",
        tags = ["manual"],
        test_cmds = [
            "--bitstream=\"$(location {bitstream})\"",
            "--bootstrap=\"$(location {flash})\"",
        ],
    ),
    targets = [
        #"verilator",
        "cw310_test_rom",
    ],
    test_harness = "//sw/host/tests/chip/spi_device_ottf_console",
    verilator = verilator_params(
        timeout = "long",
        tags = ["manual"],
        test_cmds = [
            "--reset-delay=\"120sec\"",
            "--bootstrap=\"$(location {flash})\"",
        ],
    ),
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:spi_device",
    ],
)

opentitan_functest(
    name = "i2c_target_test",
    srcs = [
        "i2c_target_test.c",
    ],
    cw310 = cw310_params(
        # This test needs hyperdebug to serve as I2C host to OpenTitan's
        # I2C target device.
        interface = "hyper310",
        tags = ["manual"],
        test_cmds = [
            "--bitstream=\"$(location {bitstream})\"",
            "--bootstrap=\"$(location {flash})\"",
        ],
    ),
    targets = [
        "cw310_test_rom",
    ],
    test_harness = "//sw/host/tests/chip/i2c_target",
    deps = [
        "//sw/device/lib/testing/json:command",
        "//sw/device/lib/testing/json:i2c_target",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/lib/sw/device/arch:device",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:gpio",
        "//sw/top_darjeeling/sw/dif:i2c",
        "//sw/top_darjeeling/sw/dif:pinmux",
        "//sw/top_darjeeling/sw/dif:pwrmgr",
        "//sw/top_darjeeling/sw/dif:rv_plic",
        "//sw/top_darjeeling/sw/test/utils:i2c_testutils",
        "//sw/top_darjeeling/sw/test/utils:isr_testutils",
        "//sw/top_darjeeling/sw/test/utils:pwrmgr_testutils",
        "//sw/top_darjeeling/sw/test/utils:rv_plic_testutils",
    ],
)

_STATUS_REPORT_TEST_MSG = "\r\n".join([
    ".*ottf_main.c:.* - Ok:654321",
    ".*ottf_main.c:.* - PermissionDenied:\\[\\\"PSY\\\",2.\\]",
    ".*ottf_main.c:.* - Aborted:\\[\\\"UNT\\\",4.\\]",
    ".*ottf_main.c:.* - Aborted:\\[\\\"THK\\\",2.\\]",
    ".*status.c:.* FAIL!",
])

opentitan_functest(
    name = "status_report_test",
    srcs = ["status_report_test.c"],
    cw310 = cw310_params(
        exit_failure = "PASS!",
        exit_success = _STATUS_REPORT_TEST_MSG,
    ),
    targets = [
        "cw310_test_rom",
    ],
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:status_report_unittest_c",
        "//sw/top_darjeeling/sw/device/runtime:print",
    ],
)
