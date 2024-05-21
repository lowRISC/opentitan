# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "@bazel_skylib//lib:dicts.bzl",
    "dicts",
)
load(
    "//rules:const.bzl",
    "CONST",
    "get_lc_items",
)
load(
    "//rules:opentitan.bzl",
    "OPENTITAN_CPU",
    "RSA_ONLY_KEY_STRUCTS",
)
load(
    "//rules:otp.bzl",
    "STD_OTP_OVERLAYS",
    "otp_image",
    "otp_json",
    "otp_partition",
)
load(
    "//rules/opentitan:defs.bzl",
    "EARLGREY_SILICON_OWNER_ROM_EXT_ENVS",
    "EARLGREY_TEST_ENVS",
    "cw310_params",
    "dv_params",
    "opentitan_binary",
    "opentitan_test",
    "rsa_key_for_lc_state",
    "silicon_params",
    "verilator_params",
)

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

opentitan_test(
    name = "aes_masking_off_test",
    srcs = ["aes_masking_off_test.c"],
    exec_env = EARLGREY_TEST_ENVS,
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

opentitan_test(
    name = "aes_entropy_test",
    srcs = ["aes_entropy_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
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

opentitan_test(
    name = "aes_idle_test",
    srcs = ["aes_idle_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
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

opentitan_test(
    name = "aes_smoketest",
    srcs = ["aes_smoketest.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
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

opentitan_test(
    name = "alert_handler_ping_timeout_test",
    srcs = ["alert_handler_ping_timeout_test.c"],
    cw310 = cw310_params(timeout = "moderate"),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    verilator = verilator_params(timeout = "long"),
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

opentitan_test(
    name = "alert_handler_lpg_clkoff_test",
    srcs = ["alert_handler_lpg_clkoff_test.c"],
    cw310 = cw310_params(timeout = "moderate"),
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            # The test requires the Ibex core to wait long enough
            # before checking for the ping_timeout error.
            # The wait-time for the Verilator would be around
            # 32M*8us = 256s (kClockFreqPeripheralHz = 125K).
            # Thus it is not recommended to run this test on
            # Verilator as this wait-time looks impractical. It should still
            # be run as part of the DV nightly regression.
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:fpga_cw310_test_rom": None,
            "//hw/top_earlgrey:silicon_creator": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
    ),
    deps = [
        "//hw/top_earlgrey:alert_handler_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:math",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aes",
        "//sw/device/lib/dif:alert_handler",
        "//sw/device/lib/dif:clkmgr",
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
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:rand_testutils",
        "//sw/device/lib/testing:ret_sram_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "alert_handler_reverse_ping_in_deep_sleep_test",
    srcs = ["alert_handler_reverse_ping_in_deep_sleep_test.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        "//hw/top_earlgrey:sim_dv": None,
    },
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

opentitan_test(
    name = "alert_handler_lpg_reset_toggle_test",
    srcs = ["alert_handler_lpg_reset_toggle.c"],
    cw310 = cw310_params(
        timeout = "moderate",
    ),
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            # The test requires the Ibex core to wait long enough
            # before checking for the ping_timeout error.
            # The wait-time for the Verilator would be around
            # 32M*8us = 256s (kClockFreqPeripheralHz = 125K).
            # Thus it is not recommended to run this test on
            # Verilator as this wait-time looks impractical. It should still
            # be run as part of the DV nightly regression.
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:fpga_cw310_test_rom": None,
            "//hw/top_earlgrey:silicon_creator": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
    ),
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
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:ret_sram_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "alert_handler_lpg_sleep_mode_pings_test",
    srcs = ["alert_handler_lpg_sleep_mode_pings.c"],
    cw310 = cw310_params(
        timeout = "moderate",
    ),
    exec_env = {
        # The test requires the Ibex core to wait long enough
        # before checking for the ping_timeout error.
        # The wait-time for the Verilator would be around
        # 4s (kClockFreqPeripheralHz = 125K).
        # Thus it is not recommended to run this test on
        # Verilator as this wait-time looks impractical. It should still
        # be run as part of the DV nightly regression.
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        "//hw/top_earlgrey:sim_dv": None,
    },
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
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rand_testutils",
        "//sw/device/lib/testing:ret_sram_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "aon_timer_irq_test",
    srcs = ["aon_timer_irq_test.c"],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:fpga_cw310_test_rom": None,
            "//hw/top_earlgrey:silicon_creator": None,
            "//hw/top_earlgrey:sim_dv": None,
            "//hw/top_earlgrey:sim_verilator": None,
        },
    ),
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

opentitan_test(
    name = "aon_timer_smoketest",
    srcs = ["aon_timer_smoketest.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        "//hw/top_earlgrey:silicon_creator": None,
        "//hw/top_earlgrey:silicon_owner_sival_rom_ext": "silicon_owner",
        "//hw/top_earlgrey:silicon_owner_prodc_rom_ext": "silicon_owner",
        "//hw/top_earlgrey:silicon_owner_proda_rom_ext": "silicon_owner",
        "//hw/top_earlgrey:sim_dv": None,
        "//hw/top_earlgrey:sim_verilator": None,
    },
    silicon_owner = silicon_params(
        tags = ["broken"],
    ),
    deps = [
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "aon_timer_wdog_bite_reset_test",
    srcs = ["aon_timer_wdog_bite_reset_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    verilator = verilator_params(tags = ["broken"]),
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

opentitan_test(
    name = "pwrmgr_wdog_reset_reqs_test",
    srcs = ["pwrmgr_wdog_reset_reqs_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
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

opentitan_test(
    name = "aon_timer_wdog_lc_escalate_test",
    srcs = ["aon_timer_wdog_lc_escalate_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    verilator = verilator_params(timeout = "long"),
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

opentitan_test(
    name = "aon_timer_sleep_wdog_sleep_pause_test",
    srcs = ["aon_timer_sleep_wdog_sleep_pause_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
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

opentitan_test(
    name = "chip_power_idle_load_test",
    srcs = ["chip_power_idle_load_test.c"],
    broken = cw310_params(tags = ["broken"]),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
            "//hw/top_earlgrey:silicon_owner_sival_rom_ext": "silicon_owner",
            "//hw/top_earlgrey:silicon_owner_prodc_rom_ext": "silicon_owner",
            "//hw/top_earlgrey:silicon_owner_proda_rom_ext": "silicon_owner",
            # FIXME broken in sival ROM_EXT, remove this line when fixed. See #21706.
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": "broken",
        },
    ),
    silicon_owner = silicon_params(
        tags = ["broken"],
    ),
    # TODO(#16374): test doesn't make progress after enabling PWM
    verilator = verilator_params(tags = ["broken"]),
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

opentitan_test(
    name = "chip_power_sleep_load_test",
    srcs = ["chip_power_sleep_load_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
        },
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

opentitan_test(
    name = "clkmgr_external_clk_src_for_sw_fast_test",
    srcs = ["clkmgr_external_clk_src_for_sw_fast_test.c"],
    cw310 = cw310_params(
        otp = "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/sival_bringup:otp_img_dev_manuf_personalized",
    ),
    exec_env = {
        # Exclude fpga_cw310_rom_with_fake_keys because they are signed with
        # RMA keys, while we need DEV, and the infrastructure doesn't allow
        # changing the key for a single environment.
        "//hw/top_earlgrey:fpga_cw310_sival": None,
        "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        "//hw/top_earlgrey:sim_dv": None,
        "//hw/top_earlgrey:sim_verilator": None,
    },
    verilator = verilator_params(tags = ["broken"]),
    deps = [
        ":clkmgr_external_clk_src_for_sw_impl",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "clkmgr_external_clk_src_for_sw_slow_test",
    srcs = ["clkmgr_external_clk_src_for_sw_slow_test.c"],
    cw310 = cw310_params(
        otp = "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/sival_bringup:otp_img_dev_manuf_personalized",
        # TODO(lowrisc/opentitan#19620): fpga doesn't support lowering main clk frequency
        tags = ["broken"],
    ),
    exec_env = {
        "//hw/top_earlgrey:sim_dv": None,
        "//hw/top_earlgrey:sim_verilator": None,
    },
    verilator = verilator_params(tags = ["broken"]),
    deps = [
        ":clkmgr_external_clk_src_for_sw_impl",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "clkmgr_jitter_frequency_test",
    srcs = ["clkmgr_jitter_frequency_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/dif:base",
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:sensor_ctrl",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:clkmgr_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:sensor_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "clkmgr_jitter_test",
    srcs = ["clkmgr_jitter_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/dif:base",
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "clkmgr_off_peri_test",
    srcs = ["clkmgr_off_peri_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    verilator = verilator_params(timeout = "eternal"),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:base",
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:spi_host",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/dif:usbdev",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:ret_sram_testutils",
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

opentitan_test(
    name = "clkmgr_off_aes_trans_test",
    srcs = ["clkmgr_off_aes_trans_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = ["clkmgr_off_trans_impl"],
)

opentitan_test(
    name = "clkmgr_off_hmac_trans_test",
    srcs = ["clkmgr_off_hmac_trans_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = ["clkmgr_off_trans_impl"],
)

opentitan_test(
    name = "clkmgr_off_kmac_trans_test",
    srcs = ["clkmgr_off_kmac_trans_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = ["clkmgr_off_trans_impl"],
)

opentitan_test(
    name = "clkmgr_off_otbn_trans_test",
    srcs = ["clkmgr_off_otbn_trans_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
        },
    ),
    deps = ["clkmgr_off_trans_impl"],
)

opentitan_test(
    name = "clkmgr_reset_frequency_test",
    srcs = ["clkmgr_reset_frequency_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    verilator = verilator_params(timeout = "long"),
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

opentitan_test(
    name = "clkmgr_sleep_frequency_test",
    srcs = ["clkmgr_sleep_frequency_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    # TODO(#13611): Splice ast_init in FPGA/Verilator.
    verilator = verilator_params(tags = ["broken"]),
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

opentitan_test(
    name = "clkmgr_smoketest",
    srcs = ["clkmgr_smoketest.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/dif:base",
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "coverage_test",
    srcs = ["coverage_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    verilator = verilator_params(timeout = "long"),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "crt_test",
    srcs = ["crt_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
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

opentitan_test(
    name = "csrng_edn_concurrency_test",
    srcs = ["csrng_edn_concurrency_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:silicon_creator": None,
            "//hw/top_earlgrey:silicon_owner_sival_rom_ext": None,
            "//hw/top_earlgrey:silicon_owner_prodc_rom_ext": None,
            "//hw/top_earlgrey:silicon_owner_proda_rom_ext": None,
        },
    ),
    verilator = verilator_params(timeout = "eternal"),
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
        "//sw/device/lib/testing:edn_testutils",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:otbn_testutils",
        "//sw/device/lib/testing:rand_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "csrng_kat_test",
    srcs = ["csrng_kat_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:csrng",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:csrng_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "csrng_smoketest",
    srcs = ["csrng_smoketest.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:csrng",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:csrng_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "edn_auto_mode",
    srcs = ["edn_auto_mode.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    verilator = verilator_params(
        timeout = "eternal",
    ),
    deps = [
        "//hw/ip/aes:model",
        "//hw/ip/edn/data:edn_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/impl/rsa:rsa_3072_verify",
        "//sw/device/lib/dif:aes",
        "//sw/device/lib/dif:csrng",
        "//sw/device/lib/dif:edn",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/dif:otbn",
        "//sw/device/lib/dif:rv_core_ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aes_testutils",
        "//sw/device/lib/testing:edn_testutils",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:otbn_testutils",
        "//sw/device/lib/testing:rand_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/tests:otbn_randomness_impl",
        "//sw/device/tests/crypto:rsa_3072_verify_testvectors_hardcoded_header",
    ],
)

opentitan_test(
    name = "edn_boot_mode",
    srcs = ["edn_boot_mode.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    verilator = verilator_params(
        timeout = "eternal",
    ),
    deps = [
        "//hw/ip/edn/data:edn_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:csrng",
        "//sw/device/lib/dif:edn",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/dif:otbn",
        "//sw/device/lib/dif:rv_core_ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:edn_testutils",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:otbn_testutils",
        "//sw/device/lib/testing:rand_testutils",
        "//sw/device/lib/testing:rv_core_ibex_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/tests:otbn_randomness_impl",
    ],
)

opentitan_test(
    name = "edn_sw_mode",
    srcs = ["edn_sw_mode.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//hw/ip/aes:model",
        "//hw/ip/edn/data:edn_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aes",
        "//sw/device/lib/dif:csrng",
        "//sw/device/lib/dif:edn",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aes_testutils",
        "//sw/device/lib/testing:edn_testutils",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:rand_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "edn_kat",
    srcs = ["edn_kat.c"],
    # Remove this line when fixed.
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//hw/ip/edn/data:edn_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:csrng",
        "//sw/device/lib/dif:csrng_shared",
        "//sw/device/lib/dif:edn",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/dif:rv_core_ibex",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:edn_testutils",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:rv_core_ibex_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "entropy_src_fw_ovr_test",
    srcs = ["entropy_src_fw_ovr_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
            "//hw/top_earlgrey:silicon_owner_sival_rom_ext": "silicon_owner",
            "//hw/top_earlgrey:silicon_owner_prodc_rom_ext": "silicon_owner",
            "//hw/top_earlgrey:silicon_owner_proda_rom_ext": "silicon_owner",
        },
    ),
    silicon_owner = silicon_params(
        tags = ["broken"],
    ),
    verilator = verilator_params(tags = ["broken"]),
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

opentitan_test(
    name = "entropy_src_kat_test",
    srcs = ["entropy_src_kat_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        ":entropy_src_kat_impl",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "entropy_src_smoketest",
    srcs = ["entropy_src_smoketest.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
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

opentitan_test(
    name = "entropy_src_ast_rng_req_test",
    srcs = ["entropy_src_ast_rng_req_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "entropy_src_csrng_test",
    srcs = ["entropy_src_csrng_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:silicon_creator": None,
            "//hw/top_earlgrey:silicon_owner_sival_rom_ext": None,
            "//hw/top_earlgrey:silicon_owner_prodc_rom_ext": None,
            "//hw/top_earlgrey:silicon_owner_proda_rom_ext": None,
        },
    ),
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

opentitan_test(
    name = "entropy_src_fw_observe_many_contiguous_test",
    srcs = ["entropy_src_fw_observe_many_contiguous.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//hw/ip/entropy_src/data:entropy_src_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:base",
        "//sw/device/lib/dif:csrng",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/dif:rv_core_ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:edn_testutils",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:rv_core_ibex_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "entropy_src_edn_reqs_test",
    srcs = ["entropy_src_edn_reqs_test.c"],
    # The SiVal ROM_EXT locks down the OTP and prevents reads by using the ePMP
    # and the key manager state is different, so the test needs to behave differently.
    cw310_sival = cw310_params(defines = ["SIVAL_ROM_EXT"]),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
            "//hw/top_earlgrey:silicon_owner_sival_rom_ext": "silicon_sival",
            "//hw/top_earlgrey:silicon_owner_prodc_rom_ext": None,
            "//hw/top_earlgrey:silicon_owner_proda_rom_ext": None,
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": "cw310_sival",
        },
    ),
    # See cw310_sival.
    silicon_sival = silicon_params(defines = ["SIVAL_ROM_EXT"]),
    verilator = verilator_params(timeout = "long"),
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

opentitan_test(
    name = "example_concurrency_test",
    srcs = ["example_concurrency_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    deps = [
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "example_mem_ujcmd_test",
    srcs = ["example_mem_ujcmd.c"],
    cw310 = cw310_params(
        test_cmd = " ".join([
            "--bootstrap=\"{firmware}\"",
            "\"{firmware:elf}\"",
        ]),
        test_harness = "//sw/host/tests/chip/mem",
    ),
    exec_env = EARLGREY_TEST_ENVS,
    verilator = verilator_params(
        timeout = "eternal",
        tags = ["manual"],
        test_cmd = " ".join([
            "--firmware-elf=\"{firmware:elf}\"",
        ]),
        test_harness = "//sw/host/tests/chip/mem",
    ),
    deps = [
        "//sw/device/lib/testing/json:command",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ujson_ottf_commands",
    ],
)

opentitan_test(
    name = "example_test_from_flash",
    srcs = ["example_test_from_flash.c"],
    exec_env = EARLGREY_TEST_ENVS,
    deps = [
        "//sw/device/lib/testing:rand_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "example_test_from_rom",
    srcs = ["example_test_from_rom.c"],
    exec_env = {
        "//hw/top_earlgrey:sim_dv": None,
        "//hw/top_earlgrey:sim_verilator": None,
    },
    # This test is designed to run and complete entirely in the ROM boot stage.
    # Setting the `test_in_rom` flag makes the `opentitan_functest` rule aware
    # of this, and instructs it to load the test image into ROM (rather than
    # loading the default test ROM, or any other ROM that may be specified via
    # DV or Verilator params).
    kind = "rom",
    linker_script = "//sw/device/lib/testing/test_rom:linker_script",
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
        "//sw/device/lib/testing/test_rom:test_rom_lib",
    ],
)

opentitan_test(
    name = "flash_ctrl_idle_low_power_test",
    srcs = ["flash_ctrl_idle_low_power_test.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        "//hw/top_earlgrey:silicon_owner_sival_rom_ext": None,
        "//hw/top_earlgrey:silicon_owner_prodc_rom_ext": None,
        "//hw/top_earlgrey:silicon_owner_proda_rom_ext": None,
        "//hw/top_earlgrey:sim_dv": None,
        "//hw/top_earlgrey:sim_verilator": None,
    },
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

opentitan_test(
    name = "flash_ctrl_ops_test",
    srcs = ["flash_ctrl_ops_test.c"],
    broken = cw310_params(tags = ["broken"]),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_owner_sival_rom_ext": None,
            # FIXME broken in sival ROM_EXT, remove this line when fixed. See #21706.
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": "broken",
        },
    ),
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
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

# This is sim_dv only target.
# Real sival target is implement after this.
opentitan_test(
    name = "flash_ctrl_info_access_lc",
    srcs = ["flash_ctrl_info_access_lc.c"],
    exec_env = {"//hw/top_earlgrey:sim_dv": None},
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:lc_ctrl",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:lc_ctrl_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

# hash table for lc_state name and value.
_FLASH_CTRL_INFO_ACCESS_LC_STATES = get_lc_items(
    CONST.LCV.TEST_UNLOCKED0,
    CONST.LCV.DEV,
    CONST.LCV.PROD,
    CONST.LCV.PROD_END,
    CONST.LCV.RMA,
)

[
    opentitan_test(
        name = "flash_ctrl_info_access_lc_{}".format(lc_state.lower()),
        srcs = ["flash_ctrl_info_access_lc.c"],
        cw310 = cw310_params(
            otp = "//hw/ip/otp_ctrl/data:img_{}".format(lc_state),
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        },
        rsa_key = rsa_key_for_lc_state(
            RSA_ONLY_KEY_STRUCTS,
            lc_state_val,
        ),
        deps = [
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/base:mmio",
            "//sw/device/lib/dif:flash_ctrl",
            "//sw/device/lib/dif:lc_ctrl",
            "//sw/device/lib/dif:rv_plic",
            "//sw/device/lib/runtime:irq",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing:flash_ctrl_testutils",
            "//sw/device/lib/testing:isr_testutils",
            "//sw/device/lib/testing:lc_ctrl_testutils",
            "//sw/device/lib/testing:rv_plic_testutils",
            "//sw/device/lib/testing/test_framework:ottf_main",
        ],
    )
    for lc_state, lc_state_val in _FLASH_CTRL_INFO_ACCESS_LC_STATES
]

test_suite(
    name = "flash_ctrl_info_access_lc_states",
    tests = ["flash_ctrl_info_access_lc_{}".format(lc_state.lower()) for lc_state, _ in _FLASH_CTRL_INFO_ACCESS_LC_STATES],
)

# These tests cannot run at the owner stage because the ROM_EXT locks the info pages.
[
    opentitan_test(
        name = "flash_ctrl_info_access_lc_{}_personalized".format(lc_state),
        srcs = ["flash_ctrl_info_access_lc.c"],
        cw310 = cw310_params(
            otp = "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/sival_bringup:otp_img_{}_manuf_personalized".format(lc_state),
        ),
        dv = dv_params(
            otp = "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/sival_bringup:otp_img_{}_manuf_personalized".format(lc_state),
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
        },
        deps = [
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/base:mmio",
            "//sw/device/lib/dif:flash_ctrl",
            "//sw/device/lib/dif:lc_ctrl",
            "//sw/device/lib/dif:otp_ctrl",
            "//sw/device/lib/dif:rv_plic",
            "//sw/device/lib/runtime:irq",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing:flash_ctrl_testutils",
            "//sw/device/lib/testing:isr_testutils",
            "//sw/device/lib/testing:lc_ctrl_testutils",
            "//sw/device/lib/testing:rv_plic_testutils",
            "//sw/device/lib/testing/test_framework:ottf_main",
        ],
    )
    for lc_state in [
        "prod",
        "prod_end",
        "dev",
    ]
]

test_suite(
    name = "flash_ctrl_info_access_lc_states_personalized",
    tests = [
        "flash_ctrl_info_access_lc_{}_personalized".format(lc_state)
        for lc_state in [
            "prod",
            "prod_end",
            "dev",
        ]
    ],
)

opentitan_test(
    name = "flash_ctrl_clock_freqs_test",
    srcs = ["flash_ctrl_clock_freqs_test.c"],
    broken = cw310_params(tags = ["broken"]),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_owner_sival_rom_ext": None,
            # FIXME broken in sival ROM_EXT, remove this line when fixed. See #21706.
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": "broken",
        },
    ),
    verilator = verilator_params(timeout = "long"),
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/lib/base:abs_mmio",
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

opentitan_test(
    name = "flash_ctrl_test",
    srcs = ["flash_ctrl_test.c"],
    broken = cw310_params(tags = ["broken"]),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
            # FIXME broken in sival ROM_EXT, remove this line when fixed. See #21706.
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": "broken",
        },
    ),
    silicon = silicon_params(tags = ["broken"]),
    verilator = verilator_params(timeout = "long"),
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

opentitan_test(
    name = "flash_ctrl_write_clear_test",
    srcs = ["flash_ctrl_write_clear_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        {
            "//hw/top_earlgrey:silicon_owner_sival_rom_ext": None,
        },
    ),
    verilator = verilator_params(timeout = "long"),
    deps = [
        "//hw/top_earlgrey/ip/flash_ctrl/data/autogen:flash_ctrl_regs",
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

opentitan_test(
    name = "flash_ctrl_mem_protection_test",
    srcs = ["flash_ctrl_mem_protection_test.c"],
    broken = cw310_params(tags = ["broken"]),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        {
            "//hw/top_earlgrey:silicon_owner_sival_rom_ext": None,
            # FIXME broken in sival ROM_EXT, remove this line when fixed. See #21706.
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": "broken",
        },
    ),
    verilator = verilator_params(timeout = "long"),
    deps = [
        "//hw/top_earlgrey/ip/flash_ctrl/data/autogen:flash_ctrl_regs",
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

opentitan_test(
    name = "flash_ctrl_rma_test",
    srcs = ["flash_ctrl_rma_test.c"],
    cw310 = cw310_params(
        changes_otp = True,
        needs_jtag = True,
        otp = "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/sival_bringup:otp_img_dev_manuf_personalized",
        tags = [
            "broken",
            "lc_dev",
        ],
        test_cmd = " ".join([
            "--elf=\"{firmware}\"",
            " \"{firmware}\"",
        ]),
        test_harness = "//sw/host/tests/chip/flash_ctrl:host_rma_test",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_sival": None,
    },
    kind = "ram",
    linker_script = "//sw/device/silicon_creator/manuf/lib:sram_program_linker_script",
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_test_config",
        "//sw/device/lib/testing/test_framework:ottf_utils",
        "//sw/device/lib/testing/test_framework:status",
        "//sw/device/silicon_creator/manuf/lib:sram_start",
    ],
)

opentitan_test(
    name = "gpio_smoketest",
    srcs = ["gpio_smoketest.c"],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            # Not compatible with the verilated top level.
            "//hw/top_earlgrey:fpga_cw310_test_rom": None,
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:silicon_creator": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
    ),
    silicon = silicon_params(tags = ["broken"]),
    deps = [
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "gpio_pinmux_test",
    srcs = ["gpio_pinmux_test.c"],
    cw310 = cw310_params(
        test_cmd = """
            --bootstrap="{firmware}"
        """,
        test_harness = "//sw/host/tests/chip/gpio",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_sival": None,
        "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
        "//hw/top_earlgrey:silicon_owner_sival_rom_ext": "silicon_owner",
    },
    silicon_owner = silicon_params(
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/chip/gpio",
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

opentitan_test(
    name = "gpio_intr_test",
    srcs = ["gpio_intr_test.c"],
    cw310 = cw310_params(
        test_cmd = """
            --bootstrap="{firmware}"
        """,
        test_harness = "//sw/host/tests/chip/gpio_intr",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_sival": None,
        "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
        "//hw/top_earlgrey:silicon_owner_sival_rom_ext": "silicon_owner",
    },
    silicon_owner = silicon_params(
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/chip/gpio_intr",
    ),
    deps = [
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/json:command",
        "//sw/device/lib/testing/json:gpio",
        "//sw/device/lib/testing/json:pinmux_config",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "hmac_enc_test",
    srcs = ["hmac_enc_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
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

opentitan_test(
    name = "hmac_enc_idle_test",
    srcs = ["hmac_enc_idle_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
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

opentitan_test(
    name = "hmac_secure_wipe_test",
    srcs = ["hmac_secure_wipe_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
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

opentitan_test(
    name = "hmac_smoketest",
    srcs = ["hmac_smoketest.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
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

opentitan_test(
    name = "keymgr_key_derivation_test",
    srcs = ["keymgr_key_derivation_test.c"],
    broken = cw310_params(tags = ["broken"]),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        {
            # This test is not supported by the silicon_owner_sival_rom_ext
            # configuration.
            "//hw/top_earlgrey:silicon_creator": None,
            # FIXME broken in sival ROM_EXT, remove this line when fixed. See #21706.
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": "broken",
        },
    ),
    verilator = verilator_params(timeout = "long"),
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

opentitan_test(
    name = "keymgr_sideload_aes_test",
    srcs = ["keymgr_sideload_aes_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//hw/ip/aes/data:aes_regs",
        "//hw/ip/keymgr/data:keymgr_regs",
        "//hw/ip/kmac/data:kmac_regs",
        "//sw/device/lib/arch:boot_stage",
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

opentitan_test(
    name = "keymgr_sideload_kmac_test",
    srcs = ["keymgr_sideload_kmac_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    verilator = verilator_params(timeout = "long"),
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

opentitan_test(
    name = "keymgr_sideload_otbn_test",
    srcs = ["keymgr_sideload_otbn_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    verilator = verilator_params(timeout = "long"),
    deps = [
        "//hw/ip/otbn/data:otbn_regs",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/dif:keymgr",
        "//sw/device/lib/dif:otbn",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing:otbn_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/otbn/crypto:x25519_sideload",
    ],
)

opentitan_test(
    name = "keymgr_sideload_otbn_simple_test",
    srcs = ["keymgr_sideload_otbn_test.c"],
    copts = ["-DTEST_SIMPLE_CASE_ONLY"],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    silicon = silicon_params(tags = ["broken"]),
    verilator = verilator_params(timeout = "long"),
    deps = [
        "//hw/ip/otbn/data:otbn_regs",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/dif:keymgr",
        "//sw/device/lib/dif:otbn",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing:otbn_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/otbn/crypto:x25519_sideload",
    ],
)

opentitan_test(
    name = "kmac_app_rom_test",
    srcs = ["kmac_app_rom_test.c"],
    exec_env = EARLGREY_TEST_ENVS,
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:rom_ctrl",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "kmac_entropy_test",
    srcs = ["kmac_entropy_test.c"],
    # TODO(#15530): EDN doesn't timeout on FPGA
    cw310 = cw310_params(tags = ["broken"]),
    exec_env = EARLGREY_TEST_ENVS,
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "kmac_idle_test",
    srcs = ["kmac_idle_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "kmac_mode_cshake_test",
    srcs = ["kmac_mode_cshake_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    verilator = verilator_params(timeout = "long"),
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

opentitan_test(
    name = "kmac_mode_kmac_test",
    srcs = ["kmac_mode_kmac_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
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

opentitan_test(
    name = "kmac_smoketest",
    srcs = ["kmac_smoketest.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "lc_ctrl_otp_hw_cfg_test",
    srcs = ["lc_ctrl_otp_hw_cfg_test.c"],
    broken = cw310_params(tags = ["broken"]),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        {
            # FIXME broken in sival ROM_EXT, remove this line when fixed. See #21706.
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": "broken",
        },
    ),
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

opentitan_test(
    name = "otbn_ecdsa_op_irq_test",
    srcs = ["otbn_ecdsa_op_irq_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    verilator = verilator_params(timeout = "long"),
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

opentitan_test(
    name = "otbn_irq_test",
    srcs = ["otbn_irq_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    verilator = verilator_params(timeout = "long"),
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

opentitan_test(
    name = "otbn_mem_scramble_test",
    srcs = ["otbn_mem_scramble_test.c"],
    # TODO(#12486) [bazel] targets in sw/device/tests failing on cw310 and verilator when built by bazel
    cw310 = cw310_params(tags = ["broken"]),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    verilator = verilator_params(timeout = "long"),
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

opentitan_test(
    name = "otbn_randomness_test",
    srcs = ["otbn_randomness_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    verilator = verilator_params(timeout = "long"),
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

opentitan_test(
    name = "otbn_rsa_test",
    srcs = ["otbn_rsa_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    verilator = verilator_params(timeout = "eternal"),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:otbn",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:otbn_testutils_rsa",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "otbn_smoketest",
    srcs = ["otbn_smoketest.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    verilator = verilator_params(timeout = "long"),
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

opentitan_test(
    name = "otbn_isa_test",
    srcs = ["otbn_isa_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//hw/ip/otbn/dv/smoke:smoke_test",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:otbn",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:otbn_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "otp_ctrl_smoketest",
    srcs = ["otp_ctrl_smoketest.c"],
    broken = cw310_params(tags = ["broken"]),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        {
            # FIXME broken in sival ROM_EXT, remove this line when fixed. See #21706.
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": "broken",
        },
    ),
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

opentitan_test(
    name = "plic_sw_irq_test",
    srcs = ["plic_sw_irq_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
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

opentitan_test(
    name = "pmp_smoketest_napot",
    srcs = ["pmp_smoketest_napot.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:pmp",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "pmp_smoketest_tor",
    srcs = ["pmp_smoketest_tor.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:pmp",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

cc_library(
    name = "pwrmgr_sleep_resets_lib",
    srcs = ["pwrmgr_sleep_resets_lib.c"],
    hdrs = ["pwrmgr_sleep_resets_lib.h"],
    target_compatible_with = [OPENTITAN_CPU],
    visibility = ["//sw/device/tests:__pkg__"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:alert_handler",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:rv_timer",
        "//sw/device/lib/dif:sysrst_ctrl",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:alert_handler_testutils",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:check",
    ],
)

opentitan_test(
    name = "pwrmgr_all_reset_reqs_test",
    srcs = ["pwrmgr_all_reset_reqs_test.c"],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": "test_harness",
            "//hw/top_earlgrey:fpga_cw310_sival": "test_harness",
            "//hw/top_earlgrey:fpga_cw310_test_rom": "test_harness",
            "//hw/top_earlgrey:silicon_creator": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_all_resets",
    ),
    test_harness = cw310_params(
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_all_resets",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:ret_sram_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/tests:pwrmgr_sleep_resets_lib",
    ],
)

opentitan_test(
    name = "pwrmgr_random_sleep_all_reset_reqs_test",
    srcs = ["pwrmgr_random_sleep_all_reset_reqs_test.c"],
    cw310 = cw310_params(
        test_cmd = "--bootstrap={firmware}",
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_all_resets",
    ),
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        EARLGREY_TEST_ENVS,
    ),
    silicon = silicon_params(
        test_cmd = "--bootstrap={firmware}",
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_all_resets",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:ret_sram_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/tests:pwrmgr_sleep_resets_lib",
    ],
)

opentitan_test(
    name = "pwrmgr_deep_sleep_all_reset_reqs_test",
    srcs = ["pwrmgr_deep_sleep_all_reset_reqs_test.c"],
    cw310 = cw310_params(
        test_cmd = "--bootstrap={firmware}",
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_all_resets",
    ),
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        EARLGREY_TEST_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
    ),
    silicon = silicon_params(
        test_cmd = "--bootstrap={firmware}",
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_all_resets",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:ret_sram_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/tests:pwrmgr_sleep_resets_lib",
    ],
)

opentitan_test(
    name = "pwrmgr_normal_sleep_all_reset_reqs_test",
    srcs = ["pwrmgr_normal_sleep_all_reset_reqs_test.c"],
    cw310 = cw310_params(
        test_cmd = "--bootstrap={firmware}",
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_all_resets",
    ),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    silicon = silicon_params(
        test_cmd = "--bootstrap={firmware}",
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_all_resets",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:ret_sram_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/tests:pwrmgr_sleep_resets_lib",
    ],
)

opentitan_test(
    name = "pwrmgr_deep_sleep_por_reset_test",
    srcs = ["pwrmgr_deep_sleep_por_reset_test.c"],
    cw310 = cw310_params(
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_por",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_sival": None,
        "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        "//hw/top_earlgrey:silicon_owner_sival_rom_ext": "silicon_owner",
        "//hw/top_earlgrey:silicon_owner_prodc_rom_ext": "silicon_owner",
        "//hw/top_earlgrey:silicon_owner_proda_rom_ext": "silicon_owner",
        "//hw/top_earlgrey:sim_dv": None,
    },
    silicon_owner = silicon_params(
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_por",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:sysrst_ctrl",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "pwrmgr_normal_sleep_por_reset_test",
    srcs = ["pwrmgr_normal_sleep_por_reset_test.c"],
    cw310 = cw310_params(
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_por",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_sival": None,
        "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        "//hw/top_earlgrey:silicon_owner_sival_rom_ext": "silicon_owner",
        "//hw/top_earlgrey:silicon_owner_prodc_rom_ext": "silicon_owner",
        "//hw/top_earlgrey:silicon_owner_proda_rom_ext": "silicon_owner",
        "//hw/top_earlgrey:sim_dv": None,
    },
    silicon_owner = silicon_params(
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_por",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:sysrst_ctrl",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "pwrmgr_normal_sleep_all_wake_ups",
    srcs = ["pwrmgr_normal_sleep_all_wake_ups.c"],
    cw310 = cw310_params(
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_all_wakeups",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_sival": None,
        "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        "//hw/top_earlgrey:silicon_creator": None,
        "//hw/top_earlgrey:silicon_owner_sival_rom_ext": None,
        "//hw/top_earlgrey:silicon_owner_prodc_rom_ext": None,
        "//hw/top_earlgrey:sim_dv": None,
    },
    silicon = silicon_params(
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_all_wakeups",
    ),
    deps = [
        "//hw/top_earlgrey/ip_autogen/pwrmgr/data:pwrmgr_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/tests/sim_dv:pwrmgr_sleep_all_wake_ups_impl",
    ],
)

opentitan_test(
    name = "pwrmgr_deep_sleep_all_wake_ups",
    srcs = ["pwrmgr_deep_sleep_all_wake_ups.c"],
    cw310 = cw310_params(
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_all_wakeups",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_sival": None,
        "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        "//hw/top_earlgrey:silicon_creator": None,
        "//hw/top_earlgrey:silicon_owner_sival_rom_ext": None,
        "//hw/top_earlgrey:silicon_owner_prodc_rom_ext": None,
        "//hw/top_earlgrey:sim_dv": None,
    },
    silicon = silicon_params(
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_all_wakeups",
    ),
    deps = [
        "//hw/top_earlgrey/ip_autogen/pwrmgr/data:pwrmgr_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:ret_sram_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/tests/sim_dv:pwrmgr_sleep_all_wake_ups_impl",
    ],
)

opentitan_test(
    name = "pwrmgr_random_sleep_all_wake_ups",
    srcs = ["pwrmgr_random_sleep_all_wake_ups.c"],
    cw310 = cw310_params(
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_all_wakeups",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_sival": None,
        "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        "//hw/top_earlgrey:silicon_creator": None,
        "//hw/top_earlgrey:silicon_owner_sival_rom_ext": None,
        "//hw/top_earlgrey:silicon_owner_prodc_rom_ext": None,
        "//hw/top_earlgrey:silicon_owner_proda_rom_ext": None,
        "//hw/top_earlgrey:sim_dv": None,
    },
    silicon = silicon_params(
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_all_wakeups",
    ),
    deps = [
        "//hw/top_earlgrey/ip_autogen/pwrmgr/data:pwrmgr_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:ret_sram_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/tests/sim_dv:pwrmgr_sleep_all_wake_ups_impl",
    ],
)

# This test reproduces a silicon failure, but passes in all other environments.
# TODO(lowrisc/opentitan#20798)  Remove this test and extend
# pwrmgr_random_sleep_all_wake_ups to cover all wakeups once this issue is
# fixed.
opentitan_test(
    name = "pwrmgr_sleep_wake_5_bug_test",
    srcs = ["pwrmgr_sleep_wake_5_bug_test.c"],
    cw310 = cw310_params(
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_all_wakeups",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_sival": None,
        "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        "//hw/top_earlgrey:silicon_creator": None,
        "//hw/top_earlgrey:silicon_owner_sival_rom_ext": None,
        "//hw/top_earlgrey:sim_dv": None,
    },
    silicon = silicon_params(
        tags = ["broken"],
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_all_wakeups",
    ),
    deps = [
        "//hw/top_earlgrey/ip_autogen/pwrmgr/data:pwrmgr_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:ret_sram_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/tests/sim_dv:pwrmgr_sleep_all_wake_ups_impl",
    ],
)

opentitan_test(
    name = "pwrmgr_sensor_ctrl_deep_sleep_wake_up",
    srcs = ["pwrmgr_sensor_ctrl_deep_sleep_wake_up.c"],
    exec_env = {"//hw/top_earlgrey:sim_dv": None},
    deps = [
        "//hw/top_earlgrey/ip_autogen/pwrmgr/data:pwrmgr_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/tests/sim_dv:pwrmgr_sleep_all_wake_ups_impl",
    ],
)

opentitan_test(
    name = "pwrmgr_smoketest",
    srcs = ["pwrmgr_smoketest.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:fpga_cw310_test_rom": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    verilator = verilator_params(timeout = "long"),
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

opentitan_test(
    name = "pwrmgr_sleep_disabled_test",
    srcs = ["pwrmgr_sleep_disabled_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
        },
    ),
    verilator = verilator_params(tags = ["broken"]),
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

opentitan_test(
    name = "pwrmgr_usb_clk_disabled_when_active_test",
    srcs = ["pwrmgr_usb_clk_disabled_when_active_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
        },
    ),
    deps = [
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:usbdev",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "rstmgr_smoketest",
    srcs = ["rstmgr_smoketest.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "rstmgr_cpu_info_test",
    srcs = ["rstmgr_cpu_info_test.c"],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_test_rom": None,
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:silicon_creator": None,
            "//hw/top_earlgrey:sim_dv": None,
            "//hw/top_earlgrey:sim_verilator": None,
        },
    ),
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
        "//sw/device/lib/testing:rv_core_ibex_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "rstmgr_sw_req_test",
    srcs = ["rstmgr_sw_req_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "rstmgr_sw_rst_ctrl_test",
    srcs = ["rstmgr_sw_rst_ctrl_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    verilator = verilator_params(timeout = "long"),
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

opentitan_test(
    name = "rv_plic_smoketest",
    srcs = ["rv_plic_smoketest.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
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

opentitan_test(
    name = "rv_timer_smoketest",
    srcs = ["rv_timer_smoketest.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
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

opentitan_test(
    name = "rv_timer_systick_test",
    srcs = ["rv_timer_systick_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
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

opentitan_test(
    name = "spi_device_smoketest",
    srcs = ["spi_device_smoketest.c"],
    cw310 = cw310_params(
        otp = "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/sival:otp_img_prod_manuf_personalized",
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/spi_device_smoketest",
    ),
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:fpga_cw310_test_rom": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap={firmware}
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/spi_device_smoketest",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:base",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:spi_device",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:status",
    ],
)

opentitan_test(
    name = "spi_device_tpm_tx_rx_test",
    srcs = ["spi_device_tpm_tx_rx_test.c"],
    cw310 = cw310_params(
        # This test requires the spi full duplex on the hyperdebug board.
        tags = [
            "broken",
            "manual",
        ],
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/spi_device_tpm_test",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_sival": None,
        "//hw/top_earlgrey:silicon_owner_sival_rom_ext": "silicon_owner",
        "//hw/top_earlgrey:sim_dv": None,
    },
    silicon_owner = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/spi_device_tpm_test",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:spi_device",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:status",
    ],
)

opentitan_test(
    name = "spi_device_flash_smoketest",
    srcs = ["spi_device_flash_smoketest.c"],
    cw310 = cw310_params(
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/spi_device_flash_smoketest",
    ),
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        },
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap={firmware}
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/spi_device_flash_smoketest",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:base",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:spi_device",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:spi_device_testutils",
        "//sw/device/lib/testing:spi_flash_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:status",
    ],
)

cc_library(
    name = "spi_host_flash_test_impl",
    srcs = ["spi_host_flash_test_impl.c"],
    hdrs = ["spi_host_flash_test_impl.h"],
    target_compatible_with = [OPENTITAN_CPU],
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
    ],
)

opentitan_test(
    name = "spi_host_smoketest",
    srcs = ["spi_host_smoketest.c"],
    cw310 = cw310_params(timeout = "moderate"),
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        },
    ),
    deps = [
        ":spi_host_flash_test_impl",
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

opentitan_test(
    name = "spi_host_winbond_flash_test",
    srcs = ["spi_host_winbond_flash_test.c"],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
            "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        },
    ),
    deps = [
        ":spi_host_flash_test_impl",
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

opentitan_test(
    name = "spi_host_irq_test",
    srcs = ["spi_host_irq_test.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        "//hw/top_earlgrey:silicon_owner_sival_rom_ext": None,
    },
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

opentitan_test(
    name = "sensor_ctrl_alert_test",
    srcs = ["sensor_ctrl_alerts_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
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
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rand_testutils",
        "//sw/device/lib/testing:ret_sram_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "sensor_ctrl_wakeup_test",
    srcs = ["sensor_ctrl_wakeup_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    silicon = silicon_params(
        tags = ["broken"],
    ),
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

opentitan_test(
    name = "sleep_pwm_pulses_test",
    srcs = ["sleep_pwm_pulses_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
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

opentitan_test(
    name = "sram_ctrl_execution_test",
    srcs = ["sram_ctrl_execution_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/dif:sram_ctrl",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:epmp_state",
    ],
)

cc_library(
    name = "sram_ctrl_sleep_sram_ret_contents_impl",
    srcs = ["sram_ctrl_sleep_sram_ret_contents_impl.c"],
    hdrs = ["sram_ctrl_sleep_sram_ret_contents_impl.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing:sram_ctrl_testutils",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
    ],
)

opentitan_test(
    name = "sram_ctrl_sleep_sram_ret_contents_no_scramble_test",
    srcs = ["sram_ctrl_sleep_sram_ret_contents_no_scramble_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/tests:sram_ctrl_sleep_sram_ret_contents_impl",
    ],
)

opentitan_test(
    name = "sram_ctrl_sleep_sram_ret_contents_scramble_test",
    srcs = ["sram_ctrl_sleep_sram_ret_contents_scramble_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/tests:sram_ctrl_sleep_sram_ret_contents_impl",
    ],
)

opentitan_test(
    name = "sram_ctrl_smoketest",
    srcs = ["sram_ctrl_smoketest.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:sram_ctrl",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
    ],
)

opentitan_test(
    name = "sram_ctrl_subword_access_test",
    srcs = ["sram_ctrl_subword_access_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:sram_ctrl",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
    ],
)

opentitan_test(
    name = "uart_smoketest",
    srcs = ["uart_smoketest.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
            "//hw/top_earlgrey:fpga_cw340_test_rom": None,
            "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
        },
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

# Work around https://github.com/bazelbuild/bazel/pull/16381
# When adding an executable as a data dependency, it expands
# to multiple locations. This alias forces bazel to only "see"
# the default output and therefore expand to a single file.
alias(
    name = "usbdev_stream_host_harness",
    actual = "//sw/host/tests/usbdev/usbdev_stream:stream_test",
)

opentitan_test(
    name = "usbdev_pincfg_test",
    srcs = ["usbdev_pincfg_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --vbus-sense-en=VBUS_SENSE_EN
            --vbus-sense=VBUS_SENSE
        """,
        test_harness = "//sw/host/tests/chip/usb:usb_harness",
    ),
    verilator = verilator_params(timeout = "long"),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:usbdev",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing:usb_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "usbdev_vbus_test",
    srcs = ["usbdev_vbus_test.c"],
    cw310 = cw310_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --no-wait-for-usb-device
        """,
        test_harness = "//sw/host/tests/chip/usb:usb_harness",
    ),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --vbus-sense-en=VBUS_SENSE_EN
            --vbus-sense=VBUS_SENSE
            --no-wait-for-usb-device
        """,
        test_harness = "//sw/host/tests/chip/usb:usb_harness",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:usbdev",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "usbdev_pullup_test",
    srcs = ["usbdev_pullup_test.c"],
    cw310 = cw310_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --no-wait-for-usb-device
        """,
        test_harness = "//sw/host/tests/chip/usb:usb_harness",
    ),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --vbus-sense-en=VBUS_SENSE_EN
            --vbus-sense=VBUS_SENSE
            --no-wait-for-usb-device
        """,
        test_harness = "//sw/host/tests/chip/usb:usb_harness",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:usbdev",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

# This test requires that the harness has sufficient permissions to
# open the USB parent hub of the device under test so it can issue
# requests directly. For this reason, the test is tagged as manual
# until the CI can provide such an access.
opentitan_test(
    name = "usbdev_aon_wake_reset_test",
    srcs = ["usbdev_aon_wake_reset_test.c"],
    cw310 = cw310_params(
        tags = ["manual"],
        test_cmd = """
            --bootstrap="{firmware}"
            --wake=reset
        """,
        test_harness = "//sw/host/tests/chip/usb:usbdev_aon_wake",
    ),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --vbus-sense-en=VBUS_SENSE_EN
            --vbus-sense=VBUS_SENSE
            --wake=reset
        """,
        test_harness = "//sw/host/tests/chip/usb:usbdev_aon_wake",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:usbdev",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing:usb_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

# Same requirements as usbdev_aon_wake_reset_test
# This test cannot be implemented on the CW310 because
# there is no VBUS control so we cannot disconnect the device.
opentitan_test(
    name = "usbdev_aon_wake_disconnect_test",
    srcs = ["usbdev_aon_wake_disconnect_test.c"],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --vbus-sense-en=VBUS_SENSE_EN
            --vbus-sense=VBUS_SENSE
            --wake=disconnect
        """,
        test_harness = "//sw/host/tests/chip/usb:usbdev_aon_wake",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:usbdev",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing:usb_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "usbdev_aon_pullup_test",
    srcs = ["usbdev_aon_pullup_test.c"],
    cw310 = cw310_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --no-wait-for-usb-device
        """,
        test_harness = "//sw/host/tests/chip/usb:usb_harness",
    ),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --vbus-sense-en=VBUS_SENSE_EN
            --vbus-sense=VBUS_SENSE
            --no-wait-for-usb-device
        """,
        test_harness = "//sw/host/tests/chip/usb:usb_harness",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:usbdev",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "usbdev_setuprx_test",
    srcs = ["usbdev_setuprx_test.c"],
    cw310 = cw310_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --no-wait-for-usb-device
        """,
        test_harness = "//sw/host/tests/chip/usb:usb_harness",
    ),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --vbus-sense-en=VBUS_SENSE_EN
            --vbus-sense=VBUS_SENSE
            --no-wait-for-usb-device
        """,
        test_harness = "//sw/host/tests/chip/usb:usb_harness",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:usbdev",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "usbdev_config_host_test",
    srcs = ["usbdev_config_host_test.c"],
    cw310 = cw310_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --no-wait-for-usb-device
        """,
        test_harness = "//sw/host/tests/chip/usb:usb_harness",
    ),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --vbus-sense-en=VBUS_SENSE_EN
            --vbus-sense=VBUS_SENSE
            --no-wait-for-usb-device
        """,
        test_harness = "//sw/host/tests/chip/usb:usb_harness",
    ),
    verilator = verilator_params(timeout = "long"),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:usbdev",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing:usb_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "usbdev_test",
    srcs = ["usbdev_test.c"],
    cw310 = cw310_params(tags = ["manual"]),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --vbus-sense-en=VBUS_SENSE_EN
            --vbus-sense=VBUS_SENSE
        """,
        test_harness = "//sw/host/tests/chip/usb:usb_harness",
    ),
    verilator = verilator_params(timeout = "long"),
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

opentitan_test(
    name = "usbdev_mixed_test",
    srcs = ["usbdev_mixed_test.c"],
    cw310 = cw310_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --exec=$(rootpath :usbdev_stream_host_harness)
        """,
        test_harness = "//sw/host/tests/chip/usb:usb_harness",
    ),
    data = [
        ":usbdev_stream_host_harness",
    ],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --vbus-sense-en=VBUS_SENSE_EN
            --vbus-sense=VBUS_SENSE
            --exec=$(rootpath :usbdev_stream_host_harness)
        """,
        test_harness = "//sw/host/tests/chip/usb:usb_harness",
    ),
    verilator = verilator_params(timeout = "long"),
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

opentitan_test(
    name = "usbdev_iso_test",
    srcs = ["usbdev_iso_test.c"],
    cw310 = cw310_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --exec=$(rootpath :usbdev_stream_host_harness)
        """,
        test_harness = "//sw/host/tests/chip/usb:usb_harness",
    ),
    data = [
        ":usbdev_stream_host_harness",
    ],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --vbus-sense-en=VBUS_SENSE_EN
            --vbus-sense=VBUS_SENSE
            --exec=$(rootpath :usbdev_stream_host_harness)
        """,
        test_harness = "//sw/host/tests/chip/usb:usb_harness",
    ),
    verilator = verilator_params(timeout = "long"),
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

opentitan_test(
    name = "usbdev_stream_test",
    srcs = ["usbdev_stream_test.c"],
    cw310 = cw310_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --exec=$(rootpath :usbdev_stream_host_harness)
        """,
        test_harness = "//sw/host/tests/chip/usb:usb_harness",
    ),
    data = [
        ":usbdev_stream_host_harness",
    ],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --vbus-sense-en=VBUS_SENSE_EN
            --vbus-sense=VBUS_SENSE
            --exec=$(rootpath :usbdev_stream_host_harness)
        """,
        test_harness = "//sw/host/tests/chip/usb:usb_harness",
    ),
    verilator = verilator_params(timeout = "long"),
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

opentitan_test(
    name = "usbdev_logging_test",
    srcs = ["usbdev_logging_test.c"],
    cw310 = cw310_params(
        timeout = "eternal",
        tags = ["manual"],
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        "//hw/top_earlgrey:sim_dv": None,
        "//hw/top_earlgrey:sim_verilator": None,
    },
    verilator = verilator_params(timeout = "long"),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing:usb_logging",
        "//sw/device/lib/testing:usb_testutils",
        "//sw/device/lib/testing:usb_testutils_streams",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "rstmgr_alert_info_test",
    srcs = ["rstmgr_alert_info_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:sim_dv": None,
            "//hw/top_earlgrey:sim_verilator": None,
        },
    ),
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
        "//sw/device/lib/dif:flash_ctrl",
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
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing:ret_sram_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "rv_core_ibex_rnd_test",
    srcs = [
        "rv_core_ibex_rnd_test.S",
        "rv_core_ibex_rnd_test.c",
    ],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
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

opentitan_test(
    name = "rv_core_ibex_address_translation_test",
    srcs = [
        "rv_core_ibex_address_translation_test.S",
        "rv_core_ibex_address_translation_test.c",
    ],
    exec_env = {
        # This test needs access address translation unit which is blocked by rom_ext.
        "//hw/top_earlgrey:fpga_cw310_sival": None,
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        "//hw/top_earlgrey:sim_dv": None,
        "//hw/top_earlgrey:sim_verilator": None,
    },
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:rv_core_ibex",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "rv_core_ibex_nmi_irq_test",
    srcs = ["rv_core_ibex_nmi_irq_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:silicon_creator": None,
            "//hw/top_earlgrey:silicon_owner_sival_rom_ext": "silicon_owner",
            "//hw/top_earlgrey:silicon_owner_prodc_rom_ext": "silicon_owner",
            "//hw/top_earlgrey:silicon_owner_proda_rom_ext": "silicon_owner",
        },
    ),
    silicon_owner = silicon_params(
        tags = ["broken"],
    ),
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

opentitan_test(
    name = "rv_core_ibex_icache_invalidate_test",
    srcs = ["rv_core_ibex_icache_invalidate_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "ast_clk_outs_test",
    srcs = ["ast_clk_outs_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
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

opentitan_test(
    name = "power_virus_systemtest",
    srcs = ["power_virus_systemtest.c"],
    cw310 = cw310_params(
        otp = "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/sival_bringup:otp_img_prod_manuf_personalized",
        test_cmd = """
            --bootstrap="{firmware}"
        """,
        test_harness = "//sw/host/tests/chip/power_virus",
    ),
    dv = dv_params(
        otp = ":power_virus_systemtest_otp_img_rma",
    ),
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            # This test does not support the fpga_cw310_sival target because the
            # test program doesn't fit inside the ROM_EXT partition size (~64KB).
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:fpga_cw310_test_rom": None,
            "//hw/top_earlgrey:silicon_creator": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
    ),
    silicon = silicon_params(
        timeout = "long",
        tags = ["broken"],
    ),
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
        "//sw/device/lib/testing:otbn_testutils_rsa",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing:spi_device_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "spi_passthru_test",
    srcs = ["spi_passthru_test.c"],
    cw310 = cw310_params(
        # TODO: This test will need hyperdebug once we start using multi-lane
        # SPI modes.
        # interface = "hyper310",
        # tags = ["manual"],
        test_cmd = """
            --bootstrap="{firmware}"
        """,
        test_harness = "//sw/host/tests/chip/spi_passthru",
    ),
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        },
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
        """,
        test_harness = "//sw/host/tests/chip/spi_passthru",
    ),
    deps = [
        "//sw/device/lib/arch:device",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:pinmux",
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

opentitan_test(
    name = "flash_scrambling_smoketest",
    srcs = ["example_test_from_flash.c"],
    dv = dv_params(
        otp = ":flash_scrambling_smoketest_otp_img_rma",
    ),
    exec_env = {
        "//hw/top_earlgrey:sim_dv": None,
    },
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

_SIVAL_OTP_IMAGE = {
    "test_unlocked1": "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/sival:otp_img_test_unlocked1_manuf_individualized",
    "test_locked0": "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/sival:otp_img_test_locked0_manuf_initialized",
    "dev": "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/sival:otp_img_dev_manuf_personalized",
    "prod": "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/sival:otp_img_prod_manuf_personalized",
    "prod_end": "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/sival:otp_img_prod_end_manuf_personalized",
    "rma": "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/sival:otp_img_rma_manuf_personalized",
}

_RV_DM_JTAG_LC_STATES = get_lc_items(
    CONST.LCV.TEST_UNLOCKED1,
    CONST.LCV.DEV,
    CONST.LCV.RMA,
)

[
    opentitan_test(
        name = "rv_dm_csr_rw_{}".format(lc_state),
        srcs = ["example_test_from_flash.c"],
        cw310 = cw310_params(
            needs_jtag = True,
            otp = _SIVAL_OTP_IMAGE[lc_state],
            tags = [
                "lc_{}".format(lc_state),
            ],
            test_harness = "//sw/host/tests/chip/rv_dm:csr_rw",
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
        },
        deps = [
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing/test_framework:ottf_main",
        ],
    )
    for lc_state, _ in _RV_DM_JTAG_LC_STATES
]

test_suite(
    name = "rv_dm_csr_rw",
    tags = ["manual"],
    tests = [
        ":rv_dm_csr_rw_{}".format(lc_state)
        for lc_state, _ in _RV_DM_JTAG_LC_STATES
    ],
)

[
    opentitan_test(
        name = "rv_dm_mem_access_{}".format(lc_state),
        srcs = ["example_test_from_flash.c"],
        cw310 = cw310_params(
            needs_jtag = True,
            otp = _SIVAL_OTP_IMAGE[lc_state],
            tags = [
                "lc_{}".format(lc_state),
            ],
            test_cmd = " --rom={rom:binary}",
            test_harness = "//sw/host/tests/chip/rv_dm:mem_access",
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
        },
        deps = [
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing/test_framework:ottf_main",
        ],
    )
    for lc_state, _ in _RV_DM_JTAG_LC_STATES
]

test_suite(
    name = "rv_dm_mem_access",
    tags = ["manual"],
    tests = [
        ":rv_dm_mem_access_{}".format(lc_state)
        for lc_state, _ in _RV_DM_JTAG_LC_STATES
    ],
)

[
    opentitan_test(
        name = "rv_dm_jtag_{}".format(lc_state),
        srcs = ["example_test_from_flash.c"],
        cw310 = cw310_params(
            needs_jtag = True,
            otp = _SIVAL_OTP_IMAGE[lc_state],
            tags = [
                "lc_{}".format(lc_state),
            ],
            test_harness = "//sw/host/tests/chip/rv_dm:jtag",
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
        },
        deps = [
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing/test_framework:ottf_main",
        ],
    )
    for lc_state, _ in _RV_DM_JTAG_LC_STATES
]

test_suite(
    name = "rv_dm_jtag",
    tags = ["manual"],
    tests = [
        ":rv_dm_jtag_{}".format(lc_state)
        for lc_state, _ in _RV_DM_JTAG_LC_STATES
    ],
)

_RV_DM_TAP_SEL_LC_STATES = get_lc_items(
    CONST.LCV.TEST_UNLOCKED1,
    CONST.LCV.TEST_LOCKED0,
    CONST.LCV.DEV,
    CONST.LCV.PROD,
    CONST.LCV.PROD_END,
    CONST.LCV.RMA,
)

[
    opentitan_test(
        name = "rv_dm_jtag_tap_sel_{}".format(lc_state),
        srcs = ["example_test_from_flash.c"],
        cw310 = cw310_params(
            needs_jtag = True,
            otp = _SIVAL_OTP_IMAGE[lc_state],
            tags = [
                "lc_{}".format(lc_state),
            ],
            test_harness = "//sw/host/tests/chip/rv_dm:jtag_tap_sel",
        ),
        exec_env = dicts.add(
            EARLGREY_SILICON_OWNER_ROM_EXT_ENVS if lc_state == "prod" else {},
            {
                "//hw/top_earlgrey:fpga_cw310_sival": None,
            },
        ),
        silicon = silicon_params(
            needs_jtag = True,
            tags = [
                "lc_{}".format(lc_state),
            ],
            test_harness = "//sw/host/tests/chip/rv_dm:jtag_tap_sel",
        ),
        deps = [
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing/test_framework:ottf_main",
        ],
    )
    for lc_state, _ in _RV_DM_TAP_SEL_LC_STATES
]

test_suite(
    name = "rv_dm_jtag_tap_sel",
    tags = ["manual"],
    tests = [
        ":rv_dm_jtag_tap_sel_{}".format(lc_state)
        for lc_state, _ in _RV_DM_TAP_SEL_LC_STATES
    ],
)

# TL tests are done on Ibex, so requires execution to be enabled.
_RV_DM_LC_DISABLED_TL_LC_STATES = get_lc_items(
    CONST.LCV.TEST_UNLOCKED1,
    CONST.LCV.DEV,
    CONST.LCV.PROD,
    CONST.LCV.PROD_END,
    CONST.LCV.RMA,
)

_RV_DM_LC_DISABLED_JTAG_LC_STATES = get_lc_items(
    CONST.LCV.TEST_UNLOCKED1,
    CONST.LCV.TEST_LOCKED0,
    CONST.LCV.DEV,
    CONST.LCV.PROD,
    CONST.LCV.PROD_END,
    CONST.LCV.RMA,
)

_LC_STATES_DEBUG_DISALLOWED = [
    CONST.LCV.TEST_LOCKED0,
    CONST.LCV.PROD,
    CONST.LCV.PROD_END,
]

[
    opentitan_test(
        name = "rv_dm_lc_disabled_tl_{}".format(lc_state),
        srcs = ["rv_dm_lc_disabled.c"],
        cw310 = cw310_params(
            otp = _SIVAL_OTP_IMAGE[lc_state],
            tags = [
                "lc_{}".format(lc_state),
            ],
        ),
        exec_env = dicts.add(
            EARLGREY_SILICON_OWNER_ROM_EXT_ENVS if lc_state == "prod" else {},
            {
                "//hw/top_earlgrey:fpga_cw310_sival": None,
            },
        ),
        deps = [
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/base:mmio",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing:lc_ctrl_testutils",
            "//sw/device/lib/testing/test_framework:ottf_main",
        ],
    )
    for lc_state, _ in _RV_DM_LC_DISABLED_TL_LC_STATES
]

test_suite(
    name = "rv_dm_lc_disabled_tl",
    tags = ["manual"],
    tests = [
        ":rv_dm_lc_disabled_tl_{}".format(lc_state)
        for lc_state, _ in _RV_DM_LC_DISABLED_TL_LC_STATES
    ],
)

[
    opentitan_test(
        name = "rv_dm_lc_disabled_jtag_{}".format(lc_state),
        srcs = ["example_test_from_flash.c"],
        cw310 = cw310_params(
            needs_jtag = True,
            otp = _SIVAL_OTP_IMAGE[lc_state],
            tags = [
                "lc_{}".format(lc_state),
            ],
            test_cmd = " --expect-fail" if lc_state_val in _LC_STATES_DEBUG_DISALLOWED else "",
            test_harness = "//sw/host/tests/chip/rv_dm:lc_disabled",
        ),
        exec_env = dicts.add(
            EARLGREY_SILICON_OWNER_ROM_EXT_ENVS if lc_state == "prod" else {},
            {
                "//hw/top_earlgrey:fpga_cw310_sival": None,
            },
        ),
        silicon = silicon_params(
            needs_jtag = True,
            test_cmd = " --expect-fail" if lc_state_val in _LC_STATES_DEBUG_DISALLOWED else "",
            test_harness = "//sw/host/tests/chip/rv_dm:lc_disabled",
        ),
        deps = [
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing/test_framework:ottf_main",
        ],
    )
    for lc_state, lc_state_val in _RV_DM_LC_DISABLED_JTAG_LC_STATES
]

test_suite(
    name = "rv_dm_lc_disabled_jtag",
    tags = ["manual"],
    tests = [
        ":rv_dm_lc_disabled_jtag_{}".format(lc_state)
        for lc_state, _ in _RV_DM_LC_DISABLED_JTAG_LC_STATES
    ],
)

[
    opentitan_test(
        name = "rv_dm_ndm_reset_req_{}".format(lc_state),
        srcs = ["rv_dm_ndm_reset_req.c"],
        cw310 = cw310_params(
            needs_jtag = True,
            otp = _SIVAL_OTP_IMAGE[lc_state],
            tags = [
                "lc_{}".format(lc_state),
            ],
            test_cmd = """
                --bootstrap="{firmware}"
            """,
            test_harness = "//sw/host/tests/chip/rv_dm:ndm_reset_req",
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
        deps = [
            "//hw/ip/adc_ctrl/data:adc_ctrl_regs",
            "//hw/ip/keymgr/data:keymgr_regs",
            "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
            "//hw/ip/sysrst_ctrl/data:sysrst_ctrl_regs",
            "//hw/top_earlgrey/ip/flash_ctrl/data/autogen:flash_ctrl_regs",
            "//hw/top_earlgrey/ip/pinmux/data/autogen:pinmux_regs",
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/base:mmio",
            "//sw/device/lib/dif:adc_ctrl",
            "//sw/device/lib/dif:flash_ctrl",
            "//sw/device/lib/dif:keymgr",
            "//sw/device/lib/dif:otp_ctrl",
            "//sw/device/lib/dif:pinmux",
            "//sw/device/lib/dif:rstmgr",
            "//sw/device/lib/dif:sysrst_ctrl",
            "//sw/device/lib/runtime:hart",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing:rstmgr_testutils",
            "//sw/device/lib/testing/test_framework:check",
            "//sw/device/lib/testing/test_framework:ottf_main",
        ],
    )
    for lc_state, lc_state_val in _RV_DM_JTAG_LC_STATES
]

test_suite(
    name = "rv_dm_ndm_reset_req",
    tags = ["manual"],
    tests = [
        ":rv_dm_ndm_reset_req_{}".format(lc_state)
        for lc_state, _ in _RV_DM_JTAG_LC_STATES
    ],
)

[
    opentitan_test(
        name = "rv_dm_ndm_reset_req_when_cpu_halted_{}".format(lc_state),
        srcs = ["rv_dm_ndm_reset_req_when_cpu_halted.c"],
        cw310 = cw310_params(
            needs_jtag = True,
            otp = _SIVAL_OTP_IMAGE[lc_state],
            tags = [
                "lc_{}".format(lc_state),
            ],
            test_cmd = """
                --bootstrap="{firmware}"
            """,
            test_harness = "//sw/host/tests/chip/rv_dm:ndm_reset_req_when_cpu_halted",
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
        deps = [
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/dif:rstmgr",
            "//sw/device/lib/runtime:hart",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing:rstmgr_testutils",
            "//sw/device/lib/testing/test_framework:check",
            "//sw/device/lib/testing/test_framework:ottf_main",
        ],
    )
    for lc_state, lc_state_val in _RV_DM_JTAG_LC_STATES
]

test_suite(
    name = "rv_dm_ndm_reset_req_when_cpu_halted",
    tags = ["manual"],
    tests = [
        ":rv_dm_ndm_reset_req_when_cpu_halted_{}".format(lc_state)
        for lc_state, _ in _RV_DM_JTAG_LC_STATES
    ],
)

[
    opentitan_test(
        name = "rv_dm_dtm_{}".format(lc_state),
        srcs = ["example_test_from_flash.c"],
        cw310 = cw310_params(
            needs_jtag = True,
            otp = _SIVAL_OTP_IMAGE[lc_state],
            tags = [
                "lc_{}".format(lc_state),
            ],
            test_cmd = """
                --bootstrap="{firmware}"
            """,
            test_harness = "//sw/host/tests/chip/rv_dm:dtm",
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
        deps = [
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/dif:rstmgr",
            "//sw/device/lib/runtime:hart",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing:rstmgr_testutils",
            "//sw/device/lib/testing/test_framework:check",
            "//sw/device/lib/testing/test_framework:ottf_main",
        ],
    )
    for lc_state, lc_state_val in _RV_DM_JTAG_LC_STATES
]

test_suite(
    name = "rv_dm_dtm",
    tags = ["manual"],
    tests = [
        ":rv_dm_dtm_{}".format(lc_state)
        for lc_state, _ in _RV_DM_JTAG_LC_STATES
    ],
)

[
    opentitan_test(
        name = "rv_dm_control_status_{}".format(lc_state),
        srcs = ["example_test_from_flash.c"],
        cw310 = cw310_params(
            needs_jtag = True,
            otp = _SIVAL_OTP_IMAGE[lc_state],
            tags = [
                "lc_{}".format(lc_state),
            ],
            test_cmd = """
                --bootstrap="{firmware}"
            """,
            test_harness = "//sw/host/tests/chip/rv_dm:control_status",
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
        deps = [
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/dif:rstmgr",
            "//sw/device/lib/runtime:hart",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing:rstmgr_testutils",
            "//sw/device/lib/testing/test_framework:check",
            "//sw/device/lib/testing/test_framework:ottf_main",
        ],
    )
    for lc_state, lc_state_val in _RV_DM_JTAG_LC_STATES
]

test_suite(
    name = "rv_dm_control_status",
    tags = ["manual"],
    tests = [
        ":rv_dm_control_status_{}".format(lc_state)
        for lc_state, _ in _RV_DM_JTAG_LC_STATES
    ],
)

[
    opentitan_test(
        name = "rv_dm_access_after_wakeup_{}".format(lc_state),
        srcs = ["rv_dm_access_after_wakeup.c"],
        cw310 = cw310_params(
            needs_jtag = True,
            otp = _SIVAL_OTP_IMAGE[lc_state],
            tags = [
                "lc_{}".format(lc_state),
            ],
            test_cmd = """
                --bootstrap="{firmware}"
                --firmware-elf=\"{firmware:elf}\"
            """,
            test_harness = "//sw/host/tests/chip/rv_dm:access_after_wakeup",
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
        deps = [
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/base:abs_mmio",
            "//sw/device/lib/base:mmio",
            "//sw/device/lib/dif:alert_handler",
            "//sw/device/lib/dif:aon_timer",
            "//sw/device/lib/dif:flash_ctrl",
            "//sw/device/lib/dif:pinmux",
            "//sw/device/lib/dif:pwrmgr",
            "//sw/device/lib/dif:rstmgr",
            "//sw/device/lib/dif:rv_plic",
            "//sw/device/lib/dif:rv_timer",
            "//sw/device/lib/dif:sysrst_ctrl",
            "//sw/device/lib/runtime:irq",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing:alert_handler_testutils",
            "//sw/device/lib/testing:aon_timer_testutils",
            "//sw/device/lib/testing:flash_ctrl_testutils",
            "//sw/device/lib/testing:pinmux_testutils",
            "//sw/device/lib/testing:pwrmgr_testutils",
            "//sw/device/lib/testing:rstmgr_testutils",
            "//sw/device/lib/testing:rv_plic_testutils",
            "//sw/device/lib/testing/test_framework:check",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/lib/testing/test_framework:ottf_utils",
        ],
    )
    for lc_state, lc_state_val in _RV_DM_JTAG_LC_STATES
]

test_suite(
    name = "rv_dm_access_after_wakeup",
    tags = ["manual"],
    tests = [
        ":rv_dm_access_after_wakeup_{}".format(lc_state)
        for lc_state, _ in _RV_DM_JTAG_LC_STATES
    ],
)

[
    opentitan_test(
        name = "rv_dm_access_after_hw_reset_{}".format(lc_state),
        srcs = ["rv_dm_access_after_hw_reset.c"],
        cw310 = cw310_params(
            needs_jtag = True,
            otp = _SIVAL_OTP_IMAGE[lc_state],
            tags = [
                "lc_{}".format(lc_state),
            ],
            test_cmd = """
                --bootstrap="{firmware}"
                --firmware-elf=\"{firmware:elf}\"
            """,
            test_harness = "//sw/host/tests/chip/rv_dm:access_after_hw_reset",
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
        },
        deps = [
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/dif:rstmgr",
            "//sw/device/lib/runtime:hart",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing:rstmgr_testutils",
            "//sw/device/lib/testing/test_framework:check",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/lib/testing/test_framework:ottf_utils",
        ],
    )
    for lc_state, lc_state_val in _RV_DM_JTAG_LC_STATES
]

test_suite(
    name = "rv_dm_access_after_hw_reset",
    tags = ["manual"],
    tests = [
        ":rv_dm_access_after_hw_reset_{}".format(lc_state)
        for lc_state, _ in _RV_DM_JTAG_LC_STATES
    ],
)

opentitan_test(
    name = "openocd_test",
    srcs = ["example_test_from_flash.c"],
    cw310 = cw310_params(
        needs_jtag = True,
        otp = "//hw/ip/otp_ctrl/data:img_test_unlocked0",
        test_cmd = """
            --bootstrap="{firmware}"
        """,
        test_harness = "//sw/host/tests/chip/jtag:openocd_test",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_sival": None,
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
    },
    deps = [
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "i2c_host_override_test",
    srcs = [
        "i2c_host_override_test.c",
    ],
    cw310 = cw310_params(
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/i2c_host_override",
    ),
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
        },
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/i2c_host_override",
    ),
    deps = [
        "//sw/device/lib/arch:device",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:i2c",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/testing:i2c_testutils",
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/json:command",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ottf_utils",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
    ],
)

opentitan_test(
    name = "i2c_target_test",
    srcs = [
        "i2c_target_test.c",
    ],
    cw310 = cw310_params(
        test_cmd = """
            --bootstrap="{firmware}"
        """,
        test_harness = "//sw/host/tests/chip/i2c_target",
    ),
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
        },
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
        """,
        test_harness = "//sw/host/tests/chip/i2c_target",
    ),
    deps = [
        "//sw/device/lib/arch:device",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:i2c",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/testing:i2c_testutils",
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/json:command",
        "//sw/device/lib/testing/json:i2c_target",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
    ],
)

_STATUS_REPORT_TEST_MSG = "\r\n".join([
    ".*ottf_main.c:.* Status reported by the test:",
    ".*ottf_main.c:.* - Aborted:\\[\\\"THK\\\",2.\\]",
    ".*ottf_main.c:.* - Aborted:\\[\\\"UNT\\\",4.\\]",
    ".*ottf_main.c:.* - PermissionDenied:\\[\\\"PSY\\\",2.\\]",
    ".*ottf_main.c:.* - Ok:654321",
    ".*status.c:.* FAIL!",
])

opentitan_test(
    name = "status_report_test",
    srcs = ["status_report_test.c"],
    cw310 = cw310_params(
        exit_failure = "PASS!",
        exit_success = _STATUS_REPORT_TEST_MSG,
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
    },
    deps = [
        "//sw/device/lib/base:status_report_unittest_c",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

_STATUS_REPORT_OVERFLOW_TEST_MSG = "\r\n".join([
    ".*ottf_main.c:.* Status reported by the test:",
    ".*ottf_main.c:.* - Aborted.*",
    ".*ottf_main.c:.* - Unavailable.*",
    ".*ottf_main.c:.* - Cancelled.*",
    ".*ottf_main.c:.* Some statuses have been lost.*",
    ".*status.c:.* FAIL!",
])

opentitan_test(
    name = "status_report_overflow_test",
    srcs = ["status_report_overflow_test.c"],
    cw310 = cw310_params(
        exit_failure = "PASS!",
        exit_success = _STATUS_REPORT_OVERFLOW_TEST_MSG,
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
    },
    deps = [
        "//sw/device/lib/base:status_report_unittest_c",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "example_sival",
    srcs = ["example_sival.c"],
    cw310 = cw310_params(
        test_cmd = " ".join([
            "--bootstrap=\"{firmware}\"",
            "\"{firmware:elf}\"",
        ]),
        test_harness = "//sw/host/tests/chip/example_sival",
    ),
    exec_env = EARLGREY_TEST_ENVS,
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ottf_utils",
    ],
)

opentitan_test(
    name = "sysrst_ctrl_inputs_test",
    srcs = ["sysrst_ctrl_inputs_test.c"],
    cw310 = cw310_params(
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/sysrst_ctrl:sysrst_ctrl_inputs",
    ),
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/sysrst_ctrl:sysrst_ctrl_inputs",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:sysrst_ctrl",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:sysrst_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ottf_utils",
    ],
)

opentitan_test(
    name = "sysrst_ctrl_outputs_test",
    srcs = ["sysrst_ctrl_outputs_test.c"],
    cw310 = cw310_params(
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/sysrst_ctrl:sysrst_ctrl_outputs",
    ),
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/sysrst_ctrl:sysrst_ctrl_outputs",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:sysrst_ctrl",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:sysrst_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ottf_utils",
    ],
)

opentitan_test(
    name = "sysrst_ctrl_in_irq_test",
    srcs = ["sysrst_ctrl_in_irq_test.c"],
    cw310 = cw310_params(
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/sysrst_ctrl:sysrst_ctrl_in_irq",
    ),
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/sysrst_ctrl:sysrst_ctrl_in_irq",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:sysrst_ctrl",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing:sysrst_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ottf_utils",
    ],
)

opentitan_test(
    name = "sysrst_ctrl_ec_rst_l_test",
    srcs = ["sysrst_ctrl_ec_rst_l_test.c"],
    cw310 = cw310_params(
        test_cmd = """
            --bootstrap="{firmware}"
        """,
        test_harness = "//sw/host/tests/chip/sysrst_ctrl:sysrst_ctrl_ec_rst_l",
    ),
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
        """,
        test_harness = "//sw/host/tests/chip/sysrst_ctrl:sysrst_ctrl_ec_rst_l",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:sysrst_ctrl",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing:sysrst_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ottf_utils",
    ],
)

opentitan_test(
    name = "sysrst_ctrl_ulp_z3_wakeup_test",
    srcs = ["sysrst_ctrl_ulp_z3_wakeup_test.c"],
    cw310 = cw310_params(
        test_cmd = """
            --bootstrap="{firmware}"
        """,
        test_harness = "//sw/host/tests/chip/sysrst_ctrl:sysrst_ctrl_ulp_z3_wakeup",
    ),
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
        """,
        test_harness = "//sw/host/tests/chip/sysrst_ctrl:sysrst_ctrl_ulp_z3_wakeup",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:sysrst_ctrl",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing:sysrst_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ottf_utils",
    ],
)

opentitan_test(
    name = "sysrst_ctrl_reset_test",
    srcs = ["sysrst_ctrl_reset_test.c"],
    cw310 = cw310_params(
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/sysrst_ctrl:sysrst_ctrl_reset",
    ),
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/sysrst_ctrl:sysrst_ctrl_reset",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:sysrst_ctrl",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing:sysrst_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "sram_ctrl_memset_test",
    srcs = ["sram_ctrl_memset_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:sram_ctrl",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
    ],
)

opentitan_test(
    name = "rv_core_ibex_isa_test_test_unlocked0",
    srcs = ["//sw/device/silicon_creator/manuf/tests:idle_functest.c"],
    cw310 = cw310_params(
        binaries = {
            ":rv_core_ibex_isa_test_sram": "sram_program",
        },
        needs_jtag = True,
        otp = "//sw/device/silicon_creator/manuf/tests:otp_img_rom_exec_disabled_test_unlocked0",
        test_cmd = "--elf={sram_program}",
        test_harness = "//sw/host/tests/chip/rv_core_ibex_isa",
    ),
    exec_env = {
        # This test is not compatible with the test_rom because the test_rom
        # does not respect the exec_disabled OTP config word.
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw310_sival": None,
        "//hw/top_earlgrey:silicon_creator": None,
    },
    silicon = silicon_params(
        needs_jtag = True,
        tags = ["manual"],
        test_cmd = "--elf={firmware}",
        test_harness = "//sw/host/tests/chip/rv_core_ibex_isa",
    ),
    deps = [
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

# This test checks basic Ibex functionality, so we prefer to run as little code as possible before the test.
# In LC states where JTAG is available, we use SRAM execution to run the test before ROM.
opentitan_binary(
    name = "rv_core_ibex_isa_test_sram",
    testonly = True,
    srcs = [
        "rv_core_ibex_isa_test.S",
        "rv_core_ibex_isa_test.c",
    ],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
    },
    kind = "ram",
    linker_script = "//sw/device/silicon_creator/manuf/lib:sram_program_linker_script",
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_test_config",
        "//sw/device/silicon_creator/manuf/lib:sram_start",
    ],
)

# For PROD LC state, we run this test as normal.
opentitan_test(
    name = "rv_core_ibex_isa_test_prod",
    srcs = [
        "rv_core_ibex_isa_test.S",
        "rv_core_ibex_isa_test.c",
    ],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    deps = [
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

test_suite(
    name = "rv_core_ibex_isa_test",
    tags = ["manual"],
    tests = [
        "rv_core_ibex_isa_test_prod",
        "rv_core_ibex_isa_test_test_unlocked0",
    ],
)

opentitan_test(
    name = "rv_core_ibex_epmp_test_functest",
    srcs = ["//sw/device/silicon_creator/manuf/tests:idle_functest.c"],
    cw310 = cw310_params(
        binaries = {
            ":rv_core_ibex_epmp_test": "sram_program",
        },
        needs_jtag = True,
        otp = "//sw/device/silicon_creator/manuf/tests:otp_img_rom_exec_disabled_test_unlocked0",
        tags = ["manual"],
        test_cmd = "--elf={sram_program}",
        test_harness = "//sw/host/tests/chip/rv_core_ibex_epmp",
    ),
    exec_env = {
        # This test is not compatible with the test_rom because the test_rom
        # does not respect the exec_disabled OTP config word.
        "//hw/top_earlgrey:fpga_cw310_sival": None,
        "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
    },
    silicon = silicon_params(
        needs_jtag = True,
        test_cmd = "--elf={firmware}",
        test_harness = "//sw/host/tests/chip/rv_core_ibex_epmp",
    ),
    deps = [
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_binary(
    name = "rv_core_ibex_epmp_test",
    testonly = True,
    srcs = [
        "rv_core_ibex_epmp_test.S",
        "rv_core_ibex_epmp_test.c",
    ],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
    },
    kind = "ram",
    linker_script = "//sw/device/silicon_creator/manuf/lib:sram_program_linker_script",
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:pmp",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_test_config",
        "//sw/device/lib/testing/test_framework:status",
        "//sw/device/silicon_creator/manuf/lib:sram_start",
    ],
)

opentitan_test(
    name = "uart_tx_rx_test",
    srcs = ["uart_tx_rx_test.c"],
    cw310 = cw310_params(
        test_cmd = " ".join([
            "--bootstrap=\"{firmware}\"",
            "--firmware-elf=\"{firmware:elf}\"",
        ]),
        test_harness = "//sw/host/tests/chip/uart:uart_tx_rx",
    ),
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:silicon_creator": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
    ),
    silicon = silicon_params(
        test_cmd = " ".join([
            "--bootstrap=\"{firmware}\"",
            "--firmware-elf=\"{firmware:elf}\"",
        ]),
        test_harness = "//sw/host/tests/chip/uart:uart_tx_rx",
    ),
    deps = [
        "//hw/ip/lc_ctrl/data:lc_ctrl_regs",
        "//hw/top_earlgrey/ip/clkmgr/data/autogen:clkmgr_regs",
        "//hw/top_earlgrey/ip/pinmux/data/autogen:pinmux_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/dif:lc_ctrl",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:clkmgr_testutils",
        "//sw/device/lib/testing:uart_testutils",
        "//sw/device/lib/testing/test_framework:ottf_console",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ottf_utils",
    ],
)

opentitan_test(
    name = "rv_core_ibex_mem_test_test_unlocked0",
    srcs = ["//sw/device/silicon_creator/manuf/tests:idle_functest.c"],
    cw310 = cw310_params(
        binaries = {
            ":rv_core_ibex_mem_test_sram": "sram_program",
        },
        needs_jtag = True,
        otp = "//sw/device/silicon_creator/manuf/tests:otp_img_rom_exec_disabled_test_unlocked0",
        test_cmd = "--elf={sram_program}",
        test_harness = "//sw/host/tests/chip/rv_core_ibex_epmp",
    ),
    exec_env = {
        # This test is not compatible with the test_rom because the test_rom
        # does not respect the exec_disabled OTP config word.
        "//hw/top_earlgrey:silicon_creator": None,
        "//hw/top_earlgrey:fpga_cw310_sival": "hyper310",
        "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": "hyper310",
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
    },
    hyper310 = cw310_params(
        binaries = {
            ":rv_core_ibex_epmp_test": "sram_program",
        },
        needs_jtag = True,
        otp = "//sw/device/silicon_creator/manuf/tests:otp_img_rom_exec_disabled_test_unlocked0",
        tags = ["manual"],
        test_cmd = "--elf={sram_program}",
        test_harness = "//sw/host/tests/chip/rv_core_ibex_epmp",
    ),
    silicon = silicon_params(
        binaries = {
            ":rv_core_ibex_mem_test_sram": "sram_program",
        },
        needs_jtag = True,
        tags = ["manual"],
        test_cmd = "--elf={sram_program}",
        test_harness = "//sw/host/tests/chip/rv_core_ibex_epmp",
    ),
    deps = [
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_binary(
    name = "rv_core_ibex_mem_test_sram",
    testonly = True,
    srcs = ["rv_core_ibex_mem_test.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
    },
    kind = "ram",
    linker_script = "//sw/device/silicon_creator/manuf/lib:sram_program_linker_script",
    deps = [
        "//hw/ip/pwm/data:pwm_regs",
        "//hw/ip/rv_timer/data:rv_timer_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:pmp",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_test_config",
        "//sw/device/lib/testing/test_framework:status",
        "//sw/device/silicon_creator/lib/base:chip",
        "//sw/device/silicon_creator/manuf/lib:sram_start",
    ],
)

opentitan_test(
    name = "rv_core_ibex_mem_test_prod",
    srcs = ["rv_core_ibex_mem_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    deps = [
        "//hw/ip/pwm/data:pwm_regs",
        "//hw/ip/rv_timer/data:rv_timer_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:pmp",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ottf_test_config",
        "//sw/device/lib/testing/test_framework:status",
        "//sw/device/silicon_creator/lib/base:chip",
    ],
)

test_suite(
    name = "rv_core_ibex_mem_test",
    tags = ["manual"],
    tests = [
        "rv_core_ibex_mem_test_prod",
        "rv_core_ibex_mem_test_test_unlocked0",
    ],
)

opentitan_test(
    name = "uart_baud_rate_test",
    srcs = ["uart_baud_rate_test.c"],
    cw310 = cw310_params(
        test_cmd = " ".join([
            "--bootstrap=\"{firmware}\"",
            "--firmware-elf=\"{firmware:elf}\"",
        ]),
        test_harness = "//sw/host/tests/chip/uart:uart_baud_rate",
    ),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    silicon = silicon_params(
        test_cmd = " ".join([
            "--bootstrap=\"{firmware}\"",
            "--firmware-elf=\"{firmware:elf}\"",
        ]),
        test_harness = "//sw/host/tests/chip/uart:uart_baud_rate",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/testing:uart_testutils",
        "//sw/device/lib/testing/test_framework:ottf_console",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ottf_utils",
    ],
)

opentitan_test(
    name = "uart_loopback_test",
    srcs = ["uart_loopback_test.c"],
    cw310 = cw310_params(
        test_cmd = " ".join([
            "--bootstrap=\"{firmware}\"",
            "--firmware-elf=\"{firmware:elf}\"",
        ]),
        test_harness = "//sw/host/tests/chip/uart:uart_loopback",
    ),
    exec_env = dicts.add(
        {"//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None},
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    silicon = silicon_params(
        test_cmd = " ".join([
            "--bootstrap=\"{firmware}\"",
            "--firmware-elf=\"{firmware:elf}\"",
        ]),
        test_harness = "//sw/host/tests/chip/uart:uart_loopback",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/testing:uart_testutils",
        "//sw/device/lib/testing/test_framework:ottf_console",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ottf_utils",
    ],
)

opentitan_test(
    name = "entropy_src_fw_override_test",
    srcs = ["entropy_src_fw_override_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//hw/ip/entropy_src/data:entropy_src_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aes",
        "//sw/device/lib/dif:base",
        "//sw/device/lib/dif:csrng",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/dif:hmac",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/dif:rv_core_ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aes_testutils",
        "//sw/device/lib/testing:edn_testutils",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:hmac_testutils",
        "//sw/device/lib/testing:kmac_testutils",
        "//sw/device/lib/testing:rv_core_ibex_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "uart_parity_break_test",
    srcs = ["uart_parity_break_test.c"],
    cw310 = cw310_params(
        test_cmd = " ".join([
            "--bootstrap=\"{firmware}\"",
            "--firmware-elf=\"{firmware:elf}\"",
        ]),
        test_harness = "//sw/host/tests/chip/uart:uart_parity_break",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_sival": None,
        "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
        "//hw/top_earlgrey:silicon_owner_sival_rom_ext": None,
    },
    silicon = silicon_params(
        test_cmd = " ".join([
            "--bootstrap=\"{firmware}\"",
            "--firmware-elf=\"{firmware:elf}\"",
        ]),
        test_harness = "//sw/host/tests/chip/uart:uart_parity_break",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:uart_testutils",
        "//sw/device/lib/testing/test_framework:ottf_console",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ottf_utils",
    ],
)

opentitan_test(
    name = "sram_ctrl_scrambled_access_test",
    srcs = ["sram_ctrl_scrambled_access_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base:stdasm",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing:sram_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "pwrmgr_usbdev_smoketest",
    srcs = ["pwrmgr_usbdev_smoketest.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    deps = [
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:usbdev",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "sram_ctrl_lc_escalation_test",
    srcs = ["sram_ctrl_lc_escalation_test.c"],
    cw310 = cw310_params(
        timeout = "moderate",
        needs_jtag = True,
        otp = "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/sival_bringup:otp_img_rma_manuf_personalized",
        test_cmd = " ".join([
            "--bootstrap=\"{firmware}\"",
            "--firmware-elf=\"{firmware:elf}\"",
        ]),
        test_harness = "//sw/host/tests/chip/sram_ctrl:sram_ctrl_lc_escalation",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_sival": None,
    },
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:alert_handler",
        "//sw/device/lib/dif:lc_ctrl",
        "//sw/device/lib/dif:sram_ctrl",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ottf_utils",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
    ],
)

opentitan_test(
    name = "sleep_pin_retention_test",
    srcs = ["sleep_pin_retention_test.c"],
    cw310 = cw310_params(
        test_cmd = """
            --bootstrap="{firmware}"
        """,
        test_harness = "//sw/host/tests/chip/gpio:sleep_pin_retention",
    ),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
        """,
        test_harness = "//sw/host/tests/chip/gpio:sleep_pin_retention",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rand_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

# There is an issue with RTL that can cause the data output to glitch.
# The glitch is particularly noticeable on the FPGA so the test is
# marked as broken. The glitch does not seem to occur on silicon.
opentitan_test(
    name = "pattgen_ios_test",
    srcs = ["pattgen_ios_test.c"],
    cw310 = cw310_params(
        tags = ["broken"],
        test_cmd = """
            --bootstrap={firmware}
            --firmware-elf=\"{firmware:elf}\"
        """,
        test_harness = "//sw/host/tests/chip/pattgen:pattgen_ios",
    ),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap={firmware}
            --firmware-elf=\"{firmware:elf}\"
        """,
        test_harness = "//sw/host/tests/chip/pattgen:pattgen_ios",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:pattgen",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ottf_utils",
    ],
)

opentitan_test(
    name = "sleep_pin_mio_dio_val_test",
    srcs = ["sleep_pin_mio_dio_val_test.c"],
    cw310 = cw310_params(
        test_cmd = """
            --bootstrap="{firmware}"
        """,
        test_harness = "//sw/host/tests/chip/gpio:sleep_pin_mio_dio_val",
    ),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
        """,
        test_harness = "//sw/host/tests/chip/gpio:sleep_pin_mio_dio_val",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rand_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)
