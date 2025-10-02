# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//lib:dicts.bzl", "dicts")
load("//hw/top:defs.bzl", "opentitan_select_top")
load(
    "//rules:const.bzl",
    "CONST",
    "get_lc_items",
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
    "DARJEELING_TEST_ENVS",
    "EARLGREY_CW340_TEST_ENVS",
    "EARLGREY_SILICON_OWNER_ROM_EXT_ENVS",
    "EARLGREY_TEST_ENVS",
    "OPENTITAN_CPU",
    "dv_params",
    "ecdsa_key_for_lc_state",
    "fpga_params",
    "opentitan_binary",
    "opentitan_test",
    "qemu_params",
    "silicon_params",
    "verilator_params",
)
load("//rules/opentitan:keyutils.bzl", "ECDSA_ONLY_KEY_STRUCTS")
load("//hw/top:defs.bzl", "opentitan_if_ip", "opentitan_select_top")
load("//rules/opentitan:util.bzl", "flatten")

package(default_visibility = ["//visibility:public"])

# TODO(lowRISC:opentitan#13180): this is a temporary solution to enable writing
# manufacturer specific tests in the `manufacturer_test_hooks` repository that
# use open source test code. Specifically, this enables defining an
# `opentitan_test` in the `manufacturer_test_hooks` repository without the
# need to specify the corresponding test hooks that should be used with the test
# on the command line.
exports_files(glob([
    "*.c",
    "*.h",
]))

filegroup(
    name = "doc_files",
    srcs = glob([
        "**/*.md",
        "**/*.svg",
    ]) + [
        "//sw/device/tests/closed_source:doc_files",
        "//sw/device/tests/crypto/cryptotest:doc_files",
    ],
)

opentitan_test(
    name = "aes_masking_off_test",
    srcs = ["aes_masking_off_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        DARJEELING_TEST_ENVS,
    ),
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/ip/aes:model",
        "//hw/top:dt",
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
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//hw/ip/aes:model",
        "//hw/top:dt",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aes_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "aes_idle_test",
    srcs = ["aes_idle_test.c"],
    exec_env = dicts.add(
        dicts.omit(
            EARLGREY_TEST_ENVS,
            [
                "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys",
                "//hw/top_earlgrey:fpga_cw310_sival_rom_ext",
            ],
        ),
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    qemu = qemu_params(
        globals = {
            "ot-aes.fast-mode": "false",
        },
    ),
    deps = [
        "//hw/ip/aes:model",
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

opentitan_test(
    name = "aes_interrupt_encryption_test",
    srcs = ["aes_interrupt_encryption_test.c"],
    exec_env = dicts.add(
        DARJEELING_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:sim_verilator": None,
            "//hw/top_earlgrey:fpga_cw340_sival": None,
        },
    ),
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/ip/aes:model",
        "//hw/top:dt",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aes",
        "//sw/device/lib/dif:edn",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aes_testutils",
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
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    # Use this test to ensure that all execution environments are tested in CI.
    run_in_ci = EARLGREY_TEST_ENVS.keys() + DARJEELING_TEST_ENVS.keys() + [
        "//hw/top_earlgrey:fpga_cw310_sival",
        "//hw/top_earlgrey:fpga_cw310_sival_rom_ext",
        "//hw/top_earlgrey:fpga_cw310_rom_ext",
    ],
    deps = [
        "//hw/ip/aes:model",
        "//hw/top:dt",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aes_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "aes_force_prng_reseed_test",
    srcs = ["aes_force_prng_reseed_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:sim_verilator": None,
            "//hw/top_earlgrey:fpga_cw340_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/ip/aes:model",
        "//hw/top:dt",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aes",
        "//sw/device/lib/dif:edn",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aes_testutils",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/sca/lib:simple_serial",
    ],
)

opentitan_test(
    name = "aes_prng_reseed_test",
    srcs = ["aes_prng_reseed_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:sim_verilator": None,
            "//hw/top_earlgrey:fpga_cw340_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/ip/aes:model",
        "//hw/top:dt",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aes",
        "//sw/device/lib/dif:edn",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aes_testutils",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ottf_utils",
        "//sw/device/sca/lib:simple_serial",
    ],
)

opentitan_test(
    name = "aes_stall_test",
    srcs = ["aes_stall_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:sim_verilator": None,
            "//hw/top_earlgrey:fpga_cw340_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/ip/aes:model",
        "//hw/top:dt",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aes",
        "//sw/device/lib/dif:edn",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aes_testutils",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ottf_utils",
        "//sw/device/sca/lib:simple_serial",
    ],
)

opentitan_test(
    name = "alert_handler_escalation_test",
    srcs = ["alert_handler_escalation_test.c"],
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
        "//hw/top:alert_handler_c_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:alert_handler",
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/dif:keymgr",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:rv_core_ibex",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:alert_handler_testutils",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "alert_handler_ping_timeout_test",
    srcs = ["alert_handler_ping_timeout_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    fpga = fpga_params(timeout = "moderate"),
    verilator = verilator_params(timeout = "long"),
    deps = [
        "//hw/top:alert_handler_c_regs",
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
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        # The test requires the Ibex core to wait long enough
        # before checking for the ping_timeout error.
        # The wait-time for the Verilator would be around
        # 32M*8us = 256s (kClockFreqPeripheralHz = 125K).
        # Thus it is not recommended to run this test on
        # Verilator as this wait-time looks impractical. It should still
        # be run as part of the DV nightly regression.
        dicts.omit(
            EARLGREY_TEST_ENVS,
            ["//hw/top_earlgrey:sim_verilator"],
        ),
        {
            "//hw/top_earlgrey:silicon_creator": None,
            "//hw/top_earlgrey:fpga_cw310_sival": None,
        },
    ),
    fpga = fpga_params(timeout = "moderate"),
    deps = [
        "//hw/top:alert_handler_c_regs",
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
    broken = fpga_params(tags = ["broken"]),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        {
            # See #23038, this test requires a provisioned flash in sival.
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": "broken",
        },
    ),
    # This test can take > 40 minutes, so mark it manual as it shouldn't run
    # in CI/nightlies.
    verilator = verilator_params(tags = ["manual"]),
    deps = [
        "//hw/top:alert_handler_c_regs",
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
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        # The test requires the Ibex core to wait long enough
        # before checking for the ping_timeout error.
        # The wait-time for the Verilator would be around
        # 32M*8us = 256s (kClockFreqPeripheralHz = 125K).
        # Thus it is not recommended to run this test on
        # Verilator as this wait-time looks impractical. It should still
        # be run as part of the DV nightly regression.
        dicts.omit(
            EARLGREY_TEST_ENVS,
            ["//hw/top_earlgrey:sim_verilator"],
        ),
        {
            "//hw/top_earlgrey:silicon_creator": None,
            "//hw/top_earlgrey:fpga_cw310_sival": None,
        },
    ),
    fpga = fpga_params(
        timeout = "moderate",
    ),
    deps = [
        "//hw/top:alert_handler_c_regs",
        "//hw/top:i2c_c_regs",
        "//hw/top:spi_device_c_regs",
        "//hw/top:spi_host_c_regs",
        "//hw/top:usbdev_c_regs",
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
    broken = fpga_params(tags = ["broken"]),
    exec_env = dicts.add(
        # The test requires the Ibex core to wait long enough
        # before checking for the ping_timeout error.
        # The wait-time for the Verilator would be around
        # 4s (kClockFreqPeripheralHz = 125K).
        # Thus it is not recommended to run this test on
        # Verilator as this wait-time looks impractical. It should still
        # be run as part of the DV nightly regression.
        dicts.omit(
            EARLGREY_TEST_ENVS,
            ["//hw/top_earlgrey:sim_verilator"],
        ),
        {
            # See #23038, this test requires a provisioned flash in sival.
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": "broken",
        },
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    fpga = fpga_params(
        timeout = "moderate",
    ),
    deps = [
        "//hw/top:alert_handler_c_regs",
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
    name = "alert_handler_ping_ok_test",
    srcs = ["alert_handler_ping_ok_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:fpga_cw340_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//sw/device/lib/arch:device",
        "//sw/device/lib/dif:aes",
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
    name = "aon_timer_irq_test",
    srcs = ["aon_timer_irq_test.c"],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        EARLGREY_TEST_ENVS,
        DARJEELING_TEST_ENVS,
        {"//hw/top_earlgrey:silicon_creator": None},
    ),
    deps = [
        "//hw/top:dt",
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
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        DARJEELING_TEST_ENVS,
    ),
    deps = [
        "//hw/top:dt",
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
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    verilator = verilator_params(tags = ["broken"]),
    deps = [
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
        DARJEELING_TEST_ENVS,
    ),
    # This test can take > 40 minutes, so mark it manual as it shouldn't run
    # in CI/nightlies.
    verilator = verilator_params(tags = ["manual"]),
    deps = [
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
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
            "//hw/top_earlgrey:silicon_owner_sival_rom_ext": "silicon_owner",
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
    exec_env = dicts.add(
        # Exclude fpga_*_rom_with_fake_keys because they are signed with
        # RMA keys, while we need DEV, and the infrastructure doesn't allow
        # changing the key for a single environment.
        dicts.omit(
            EARLGREY_TEST_ENVS,
            ["//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys"],
        ),
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:fpga_cw340_sival": None,
        },
    ),
    fpga = fpga_params(
        otp = "//hw/top_earlgrey/data/otp/emulation:otp_img_dev_manuf_personalized",
    ),
    verilator = verilator_params(tags = ["broken"]),
    deps = [
        ":clkmgr_external_clk_src_for_sw_impl",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "clkmgr_external_clk_src_for_sw_slow_test",
    srcs = ["clkmgr_external_clk_src_for_sw_slow_test.c"],
    exec_env = {
        "//hw/top_earlgrey:sim_dv": None,
        "//hw/top_earlgrey:sim_verilator": None,
    },
    fpga = fpga_params(
        otp = "//hw/top_earlgrey/data/otp/emulation:otp_img_dev_manuf_personalized",
        # TODO(lowrisc/opentitan#19620): fpga doesn't support lowering main clk frequency
        tags = ["broken"],
    ),
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
        EARLGREY_CW340_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    # Broken on Verilator. See #24182.
    verilator = verilator_params(tags = ["broken"]),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
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
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
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
        "//sw/device/lib/dif:rv_core_ibex",
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
        "//hw/top:dt",
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
        "//sw/device/lib/dif:rv_core_ibex",
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
        DARJEELING_TEST_ENVS,
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
        DARJEELING_TEST_ENVS,
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
        DARJEELING_TEST_ENVS,
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
        DARJEELING_TEST_ENVS,
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
        EARLGREY_CW340_TEST_ENVS,
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
        EARLGREY_CW340_TEST_ENVS,
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
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//hw/top:dt",
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
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_console",
        "//sw/device/lib/testing/test_framework:ottf_isrs",
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
            "//hw/top_earlgrey:silicon_creator": None,
            "//hw/top_earlgrey:silicon_owner_sival_rom_ext": "silicon_owner",
        },
    ),
    silicon_owner = silicon_params(
        tags = ["broken"],
    ),
    verilator = verilator_params(
        timeout = "eternal",
        # This test can take > 60 minutes, so mark it manual as it shouldn't
        # run in CI/nightlies.
        tags = ["manual"],
    ),
    deps = [
        ":otbn_randomness_impl",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aes",
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
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    silicon = silicon_params(
        tags = ["broken"],
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
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    silicon = silicon_params(tags = ["broken"]),
    deps = [
        "//hw/top:dt",
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
        # This test can take > 60 minutes, so mark it manual as it shouldn't
        # run in CI/nightlies.
        tags = ["manual"],
    ),
    deps = [
        "//hw/ip/aes:model",
        "//hw/top:edn_c_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/crypto/drivers:otbn",
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
        "//hw/top:edn_c_regs",
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
        dicts.omit(
            EARLGREY_TEST_ENVS,
            [
                "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys",
                "//hw/top_earlgrey:fpga_cw310_sival_rom_ext",
            ],
        ),
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/ip/aes:model",
        "//hw/top:edn_c_regs",
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
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/top:edn_c_regs",
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
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    silicon = silicon_params(
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
        "//sw/device/lib/testing:entropy_src_testutils",
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
        "//sw/device/lib/testing:entropy_src_testutils",
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
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        ":entropy_src_kat_impl",
        "//hw/top:dt",
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
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//hw/top:dt",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:base",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:entropy_src_testutils",
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
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//hw/top:dt",
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
    # This test can take > 40 minutes, so mark it manual as it shouldn't run
    # in CI/nightlies.
    verilator = verilator_params(tags = ["manual"]),
    deps = [
        "//hw/top:entropy_src_c_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:base",
        "//sw/device/lib/dif:csrng",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/dif:rv_core_ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:edn_testutils",
        "//sw/device/lib/testing:entropy_src_testutils",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:rv_core_ibex_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "entropy_src_edn_reqs_test",
    srcs = ["entropy_src_edn_reqs_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
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
        "//sw/device/lib/testing:entropy_src_testutils",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "entropy_src_bypass_mode_health_test",
    srcs = ["entropy_src_bypass_mode_health_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:sim_verilator": None,
            "//hw/top_earlgrey:fpga_cw340_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
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
    name = "entropy_src_fips_mode_health_test",
    srcs = ["entropy_src_fips_mode_health_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:sim_verilator": None,
            "//hw/top_earlgrey:fpga_cw340_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    # This test uses carefully tuned health test threshold values to trigger health test alerts
    # inside ENTROPY_SRC. Due to the probabilistic nature of the analog noise source producing the
    # the tested entropy, the test is expected to be "flaky" on silicon targets.
    #
    # In contrast, FPGA platforms use a deterministic model for the analog noise source. The
    # tested entropy bits depend on a netlist constant, the time it takes to reach the test code,
    # and the amount of entropy consumed by endpoints until reaching the test code. Correctly
    # tuning the health test thresholds for FPGA platforms in a robust way is not feasible
    # currently. Instead, the test is marked as "broken" on FPGA.
    fpga = fpga_params(tags = ["broken"]),
    silicon = silicon_params(tags = ["flaky"]),
    verilator = verilator_params(timeout = "long"),
    deps = [
        ":otbn_randomness_impl",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aes",
        "//sw/device/lib/dif:alert_handler",
        "//sw/device/lib/dif:edn",
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
        "//sw/device/lib/testing:edn_testutils",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "example_concurrency_test",
    srcs = ["example_concurrency_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        DARJEELING_TEST_ENVS,
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
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_CW340_TEST_ENVS,
    ),
    fpga = fpga_params(
        test_cmd = " ".join([
            "--bootstrap=\"{firmware}\"",
            "\"{firmware:elf}\"",
        ]),
        test_harness = "//sw/host/tests/chip/mem",
    ),
    verilator = verilator_params(
        timeout = "eternal",
        tags = ["manual"],
        test_cmd = " ".join([
            "\"{firmware:elf}\"",
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
        "//hw/top_darjeeling:sim_dv": None,
    },
    # This test is designed to run and complete entirely in the ROM boot stage.
    # Setting the `test_in_rom` flag makes the `opentitan_test` rule aware
    # of this, and instructs it to load the test image into ROM (rather than
    # loading the default test ROM, or any other ROM that may be specified via
    # DV or Verilator params).
    kind = "rom",
    linker_script = "//sw/device/lib/testing/test_rom:linker_script",
    deps = [
        "//hw/top:dt",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print_uart",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:status",
        "//sw/device/lib/testing/test_rom:test_rom_lib",
    ],
)

opentitan_test(
    name = "flash_ctrl_idle_low_power_test",
    srcs = ["flash_ctrl_idle_low_power_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
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
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rand_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "flash_ctrl_ops_test",
    srcs = ["flash_ctrl_ops_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    # Run also as ROM_EXT stage as test coverage is reduced in silicon owner stage.
    run_in_ci = [
        "//hw/top_earlgrey:fpga_cw310_sival_rom_ext",
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys",
    ],
    deps = [
        "//hw/top:otp_ctrl_c_regs",
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
        ecdsa_key = ecdsa_key_for_lc_state(
            ECDSA_ONLY_KEY_STRUCTS,
            lc_state_val,
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:sim_qemu_rom_with_fake_keys": None,
        },
        fpga = fpga_params(
            otp = "//hw/top_earlgrey/data/otp:img_{}".format(lc_state),
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
        dv = dv_params(
            otp = "//hw/top_earlgrey/data/otp/emulation:otp_img_{}_manuf_personalized".format(lc_state),
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
        },
        fpga = fpga_params(
            otp = "//hw/top_earlgrey/data/otp/emulation:otp_img_{}_manuf_personalized".format(lc_state),
        ),
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
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    # Run also as ROM_EXT stage as test coverage is reduced in silicon owner stage.
    run_in_ci = [
        "//hw/top_earlgrey:fpga_cw310_sival_rom_ext",
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys",
    ],
    verilator = verilator_params(timeout = "long"),
    deps = [
        "//hw/top:otp_ctrl_c_regs",
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
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    # Run also as ROM_EXT stage as test coverage is reduced in silicon owner stage.
    run_in_ci = [
        "//hw/top_earlgrey:fpga_cw310_sival_rom_ext",
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys",
    ],
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
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    verilator = verilator_params(timeout = "long"),
    deps = [
        "//hw/top:flash_ctrl_c_regs",
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
    broken = fpga_params(tags = ["broken"]),
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
        "//hw/top:flash_ctrl_c_regs",
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
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_sival": None,
    },
    fpga = fpga_params(
        changes_otp = True,
        needs_jtag = True,
        otp = "//hw/top_earlgrey/data/otp/emulation:otp_img_dev_manuf_personalized",
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
        DARJEELING_TEST_ENVS,
        # Not compatible with the verilated top level.
        dicts.omit(
            EARLGREY_TEST_ENVS,
            ["//hw/top_earlgrey:sim_verilator"],
        ),
        {
            "//hw/top_earlgrey:silicon_creator": None,
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
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
        },
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
        """,
        test_harness = "//sw/host/tests/chip/gpio:gpio_pinmux",
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/chip/gpio:gpio_pinmux",
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
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
        },
    ),
    fpga = fpga_params(
        timeout = "moderate",
        test_cmd = """
            --bootstrap="{firmware}"
        """,
        test_harness = "//sw/host/tests/chip/gpio:gpio_intr",
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/chip/gpio:gpio_intr",
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
            "//hw/top_darjeeling:sim_dv": None,
        },
    ),
    deps = [
        "//hw/top:dt",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:hmac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:hmac_testutils",
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
        DARJEELING_TEST_ENVS,
    ),
    deps = [
        "//hw/top:dt",
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
    name = "hmac_endianness_test",
    srcs = ["hmac_endianness_test.c"],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:sim_verilator": None,
            "//hw/top_earlgrey:fpga_cw340_sival": None,
        },
        DARJEELING_TEST_ENVS,
    ),
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/top:dt",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:hmac",
        "//sw/device/lib/runtime:log",
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
        },
        DARJEELING_TEST_ENVS,
    ),
    deps = [
        "//hw/top:dt",
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
        DARJEELING_TEST_ENVS,
    ),
    deps = [
        "//hw/top:dt",
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
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        {
            # This test is not supported by the silicon_owner_sival_rom_ext
            # configuration.
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    qemu = qemu_params(
        globals = {
            # Test uses rstmgr, keep running on fatal resets:
            "ot-rstmgr.fatal_reset": 0,
        },
    ),
    verilator = verilator_params(timeout = "long"),
    deps = [
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "keymgr_derive_sealing_test",
    srcs = ["keymgr_derive_cdi_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    qemu = qemu_params(
        globals = {
            # Test uses rstmgr, keep running on fatal resets:
            "ot-rstmgr.fatal_reset": 0,
        },
    ),
    verilator = verilator_params(timeout = "eternal"),
    deps = [
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing:otbn_testutils",
        "//sw/device/lib/testing:ret_sram_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing:sram_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/otbn/crypto:x25519_sideload",
    ],
)

opentitan_test(
    name = "keymgr_derive_attestation_test",
    srcs = ["keymgr_derive_cdi_test.c"],
    copts = ["-DDERIVE_ATTESTATION"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    qemu = qemu_params(
        globals = {
            # Test uses rstmgr, keep running on fatal resets:
            "ot-rstmgr.fatal_reset": 0,
        },
    ),
    verilator = verilator_params(timeout = "eternal"),
    deps = [
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing:otbn_testutils",
        "//sw/device/lib/testing:ret_sram_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing:sram_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/otbn/crypto:x25519_sideload",
    ],
)

otp_json(
    name = "otp_ctrl_descrambling_otp_json",
    partitions = [
        otp_partition(
            name = "SECRET0",
            items = {
                "TEST_UNLOCK_TOKEN": "117dbd7aca3f7de6749f1cb4a7daf4f5",
                "TEST_EXIT_TOKEN": "1dc4b32c25ef2c31d6313735da1740e4",
            },
            lock = False,
        ),
        otp_partition(
            name = "SECRET1",
            items = {
                "FLASH_ADDR_KEY_SEED": "434677540fdc9956038c1b4e7bd7394c8251c8921ed1a7fc8ed040844dde2dca",
                "FLASH_DATA_KEY_SEED": "7cdb1a9d39c20016dcc70e44beeff5f4871b3d2726a673365cc32c34646c9a9f",
                "SRAM_DATA_KEY_SEED": "57f20b5b2e200c010e83fabc03c68203",
            },
            lock = False,
        ),
        otp_partition(
            name = "SECRET2",
            items = {
                "RMA_TOKEN": "6ef5b95acb3ded39bed4fd235f6b24d4",
                "CREATOR_ROOT_KEY_SHARE0": "f915734729d70391ea9f54f370a2fdf8196906bfe0051fa8a9398fab0bba1e23",
                "CREATOR_ROOT_KEY_SHARE1": "e889c1ccf0f57d6ddda3ceb51b6cbc3bbaa7bc074a97c885d3bd2ecfc0fc7581",
            },
            lock = False,
        ),
    ],
)

otp_image(
    name = "otp_ctrl_descrambling_otp_image",
    src = "//hw/top_earlgrey/data/otp:otp_json_rma",
    overlays = STD_OTP_OVERLAYS + [":otp_ctrl_descrambling_otp_json"],
    visibility = ["//visibility:private"],
)

opentitan_test(
    name = "otp_ctrl_descrambling_test",
    srcs = ["otp_ctrl_descrambling_test.c"],
    dv = dv_params(
        otp = ":otp_ctrl_descrambling_otp_image",
    ),
    exec_env = dicts.add(
        {
            "//hw/top_earlgrey:sim_dv": None,
            "//hw/top_earlgrey:sim_verilator": None,
            "//hw/top_earlgrey:fpga_cw310_test_rom": None,
            # This test is not expected to run on silicon, as it would require a very specific OTP configuration that is only useful for this test.
        },
    ),
    fpga = fpga_params(
        otp = ":otp_ctrl_descrambling_otp_image",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_binary(
    name = "otp_ctrl_rot_auth_config_test",
    testonly = True,
    srcs = ["otp_ctrl_rot_auth_config_test.c"],
    exec_env = [
        "//hw/top_earlgrey:sim_dv",
    ],
    kind = "ram",
    linker_script = "//sw/device/examples/sram_program:sram_program_linker_script",
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_test_config",
        "//sw/device/lib/testing/test_framework:status",
        "//sw/device/silicon_creator/manuf/lib:individualize",
        "//sw/device/silicon_creator/manuf/lib:individualize_sw_cfg_sival",
        "//sw/device/silicon_creator/manuf/lib:otp_fields",
        "//sw/device/silicon_creator/manuf/lib:sram_start",
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
    qemu = qemu_params(
        globals = {
            # Test uses rstmgr, keep running on fatal resets:
            "ot-rstmgr.fatal_reset": 0,
        },
    ),
    deps = [
        "//hw/top:aes_c_regs",
        "//hw/top:keymgr_c_regs",
        "//hw/top:kmac_c_regs",
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
    qemu = qemu_params(
        globals = {
            # Test uses rstmgr, keep running on fatal resets:
            "ot-rstmgr.fatal_reset": 0,
        },
    ),
    verilator = verilator_params(timeout = "long"),
    deps = [
        "//hw/top:keymgr_c_regs",
        "//hw/top:kmac_c_regs",
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
    qemu = qemu_params(
        globals = {
            # Test uses rstmgr, keep running on fatal resets:
            "ot-rstmgr.fatal_reset": 0,
        },
    ),
    verilator = verilator_params(timeout = "long"),
    deps = [
        "//hw/top:otbn_c_regs",
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
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    qemu = qemu_params(
        globals = {
            # Test uses rstmgr, keep running on fatal resets:
            "ot-rstmgr.fatal_reset": 0,
        },
    ),
    silicon = silicon_params(tags = ["broken"]),
    verilator = verilator_params(timeout = "long"),
    deps = [
        "//hw/top:otbn_c_regs",
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

# TODO(lowrisc/opentitan#26250): it would be good if execution environments
# could provide a mechanism for obtaining their hashfiles, rather than us
# hardcoding all these hashfile mappings here.
_KMAC_APP_ROM_LIST = [
    (
        "//sw/device/lib/testing/test_rom:test_rom_sim_verilator_hashfile",
        "sim_verilator",
        ["//hw/top_earlgrey"],
    ),
    (
        "//sw/device/lib/testing/test_rom:test_rom_fpga_cw310_hashfile",
        "fpga_cw310_test_rom",
        ["//hw/top_earlgrey"],
    ),
    (
        "//sw/device/silicon_creator/rom:mask_rom_fpga_cw310_hashfile",
        "fpga_cw310_rom_with_fake_keys",
        ["//hw/top_earlgrey"],
    ),
    (
        "//sw/device/silicon_creator/rom:mask_rom_fpga_cw310_hashfile",
        "fpga_cw310_sival",
        ["//hw/top_earlgrey"],
    ),
    (
        "//sw/device/silicon_creator/rom:mask_rom_fpga_cw340_hashfile",
        "fpga_cw340_sival",
        ["//hw/top_earlgrey"],
    ),
    (
        "//sw/device/lib/testing/test_rom:test_rom_sim_dv_hashfile",
        "sim_dv",
        [
            "//hw/top_earlgrey",
            "//hw/top_darjeeling",
        ],
    ),
]

[
    opentitan_test(
        name = "kmac_app_rom_test_{}".format(exec_env),
        srcs = [
            "kmac_app_rom_test.c",
            hashfile,
        ],
        exec_env = {
            "{}:{}".format(top, exec_env): None
            for top in tops
        },
        deps = [
            "//hw/top:dt",
            "//sw/device/lib/base:mmio",
            "//sw/device/lib/dif:rom_ctrl",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing/test_framework:ottf_main",
        ],
    )
    for (hashfile, exec_env, tops) in _KMAC_APP_ROM_LIST
]

test_suite(
    name = "kmac_app_rom_test",
    tests = [
        "kmac_app_rom_test_{}".format(exec_env)
        for (_, exec_env, _) in _KMAC_APP_ROM_LIST
    ],
)

opentitan_test(
    name = "kmac_endianess_test",
    srcs = ["kmac_endianess_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//hw/top:dt",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "kmac_entropy_test",
    srcs = ["kmac_entropy_test.c"],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw340_sival": None,
            "//hw/top_earlgrey:sim_dv": None,
            "//hw/top_earlgrey:sim_verilator": None,
        },
    ),
    verilator = verilator_params(timeout = "long"),
    deps = [
        "//hw/top:dt",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "kmac_error_conditions_test",
    srcs = ["kmac_error_conditions_test.c"],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:fpga_cw340_sival": None,
            "//hw/top_earlgrey:sim_dv": None,
            "//hw/top_earlgrey:sim_verilator": None,
        },
    ),
    verilator = verilator_params(timeout = "long"),
    deps = [
        "//hw/top:dt",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/dif:keymgr",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing:kmac_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "kmac_entropy_stress_test",
    srcs = ["kmac_entropy_stress_test.c"],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:sim_dv": None,
            "//hw/top_earlgrey:sim_verilator": None,
        },
    ),
    verilator = verilator_params(timeout = "eternal"),
    deps = [
        "//hw/top:dt",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:kmac",
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
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//hw/top:dt",
        "//hw/top:top_lib",
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "kmac_kmac_key_sideload_test",
    srcs = ["kmac_kmac_key_sideload_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    qemu = qemu_params(
        globals = {
            # Test uses rstmgr, keep running on fatal resets:
            "ot-rstmgr.fatal_reset": 0,
        },
    ),
    verilator = verilator_params(timeout = "long"),
    deps = [
        "//hw/top:dt",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:keymgr",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing:kmac_testutils",
        "//sw/device/lib/testing:ret_sram_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing:sram_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
    ],
)

opentitan_test(
    name = "kmac_mode_cshake_test",
    srcs = ["kmac_mode_cshake_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    verilator = verilator_params(timeout = "long"),
    deps = [
        "//hw/top:dt",
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
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//hw/top:dt",
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
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//hw/top:dt",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "lc_ctrl_otp_hw_cfg0_test",
    srcs = ["lc_ctrl_otp_hw_cfg0_test.c"],
    exec_env = EARLGREY_TEST_ENVS,
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
        "//sw/otbn/crypto:run_p256",
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
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw340_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
            "//hw/top_earlgrey:sim_dv": None,
            "//hw/top_earlgrey:sim_verilator": None,
        },
    ),
    verilator = verilator_params(timeout = "long"),
    deps = [
        "//hw/top:dt",
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
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    verilator = verilator_params(timeout = "long"),
    deps = [
        ":otbn_randomness_impl",
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
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    verilator = verilator_params(timeout = "long"),
    deps = [
        "//hw/top:dt",
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
    name = "otp_ctrl_mem_access_test",
    srcs = ["otp_ctrl_mem_access_test.c"],
    exec_env = {
        # This test needs to program OTP which is blocked by rom_ext.
        "//hw/top_earlgrey:fpga_cw310_sival": None,
        "//hw/top_earlgrey:sim_dv": None,
        "//hw/top_earlgrey:sim_verilator": None,
    },
    fpga = fpga_params(
        changes_otp = True,
    ),
    # This test can take > 40 minutes, so mark it manual as it shouldn't run
    # in CI/nightlies.
    verilator = verilator_params(tags = ["manual"]),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "otp_ctrl_smoketest",
    srcs = ["otp_ctrl_smoketest.c"],
    exec_env = {
        # This test needs to program OTP which is blocked by rom_ext.
        "//hw/top_earlgrey:fpga_cw310_sival": None,
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        "//hw/top_earlgrey:sim_dv": None,
        "//hw/top_earlgrey:sim_verilator": None,
        "//hw/top_darjeeling:sim_dv": None,
    },
    fpga = fpga_params(
        changes_otp = True,
    ),
    deps = [
        "//hw/top:dt",
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
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//hw/top:dt",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:math",
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

opentitan_test(
    name = "pwm_smoketest",
    srcs = ["pwm_smoketest.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_owner_sival_rom_ext": None,
            "//hw/top_earlgrey:fpga_cw310_sival": None,
        },
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/pwm_smoketest",
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/pwm_smoketest",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:pwm",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ottf_utils",
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
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_all_resets",
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_all_resets",
    ),
    # FIXME this test is also broken in Verilator for the same reason as in
    # sival ROM_EXT above. Remove this line when fixed. See #21706.
    verilator = verilator_params(tags = ["broken"]),
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
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        EARLGREY_TEST_ENVS,
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_all_resets",
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_all_resets",
    ),
    # This test can take > 40 minutes, so mark it manual as it shouldn't run
    # in CI/nightlies.
    verilator = verilator_params(tags = ["manual"]),
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
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        EARLGREY_TEST_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    fpga = fpga_params(
        test_cmd = "--bootstrap={firmware}",
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_all_resets",
    ),
    silicon = silicon_params(
        test_cmd = "--bootstrap={firmware}",
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_all_resets",
    ),
    # This test can take > 40 minutes, so mark it manual as it shouldn't run
    # in CI/nightlies.
    verilator = verilator_params(tags = ["manual"]),
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
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    fpga = fpga_params(
        test_cmd = "--bootstrap={firmware}",
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_all_resets",
    ),
    silicon = silicon_params(
        test_cmd = "--bootstrap={firmware}",
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_all_resets",
    ),
    # This test can take > 40 minutes, so mark it manual as it shouldn't run
    # in CI/nightlies.
    verilator = verilator_params(tags = ["manual"]),
    deps = [
        "//sw/device/lib/arch:device",
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
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
        },
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_por",
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_por",
    ),
    # This test can take > 40 minutes, so mark it manual as it shouldn't run
    # in CI/nightlies.
    verilator = verilator_params(tags = ["manual"]),
    deps = [
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
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
        },
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_por",
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_por",
    ),
    # This test can take > 40 minutes, so mark it manual as it shouldn't run
    # in CI/nightlies.
    verilator = verilator_params(tags = ["manual"]),
    deps = [
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

# List of IPs supported by the pwrmgr_sleep_all_wake_ups_impl
# library. Some of these can be top-specific.
PWRMGR_SUPPORTED_IPS = [
    "aon_timer",
    "adc_ctrl",
    "pinmux",
    "sensor_ctrl",
    "sysrst_ctrl",
    "usbdev",
]

cc_library(
    name = "pwrmgr_sleep_all_wake_ups_impl",
    srcs = ["pwrmgr_sleep_all_wake_ups_impl.c"],
    hdrs = ["pwrmgr_sleep_all_wake_ups_impl.h"],
    defines = flatten(
        [
            opentitan_if_ip(
                ip,
                ["HAS_" + ip.upper()],
                [],
            )
            for ip in PWRMGR_SUPPORTED_IPS
        ],
    ),
    target_compatible_with = [OPENTITAN_CPU],
    visibility = ["//sw/device/tests:__pkg__"],
    deps = [
        "//hw/top:dt",
        "//hw/top:pwrmgr_c_regs",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ] + flatten(
        [
            opentitan_if_ip(
                ip,
                ["//sw/device/lib/dif:" + ip],
                [],
            )
            for ip in PWRMGR_SUPPORTED_IPS
        ],
    ),
)

opentitan_test(
    name = "pwrmgr_normal_sleep_all_wake_ups",
    srcs = ["pwrmgr_normal_sleep_all_wake_ups.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_all_wakeups",
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_all_wakeups",
    ),
    # This test can take > 40 minutes, so mark it manual as it shouldn't run
    # in CI/nightlies.
    verilator = verilator_params(tags = ["manual"]),
    deps = [
        ":pwrmgr_sleep_all_wake_ups_impl",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "pwrmgr_deep_sleep_all_wake_ups",
    srcs = ["pwrmgr_deep_sleep_all_wake_ups.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_all_wakeups",
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_all_wakeups",
    ),
    # This test can take > 40 minutes, so mark it manual as it shouldn't run
    # in CI/nightlies.
    verilator = verilator_params(tags = ["manual"]),
    deps = [
        ":pwrmgr_sleep_all_wake_ups_impl",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:ret_sram_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "pwrmgr_random_sleep_all_wake_ups",
    srcs = ["pwrmgr_random_sleep_all_wake_ups.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_all_wakeups",
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/chip/pwrmgr:sleep_all_wakeups",
    ),
    # This test can take > 40 minutes, so mark it manual as it shouldn't run
    # in CI/nightlies.
    verilator = verilator_params(tags = ["manual"]),
    deps = [
        ":pwrmgr_sleep_all_wake_ups_impl",
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
    ],
)

opentitan_test(
    name = "sleep_pin_wake_test",
    srcs = ["sleep_pin_wake_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/gpio:sleep_pin_wake",
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/gpio:sleep_pin_wake",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rand_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ottf_utils",
    ],
)

opentitan_test(
    name = "pwrmgr_sensor_ctrl_deep_sleep_wake_up",
    srcs = ["pwrmgr_sensor_ctrl_deep_sleep_wake_up.c"],
    exec_env = {"//hw/top_earlgrey:sim_dv": None},
    deps = [
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:sensor_ctrl",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
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
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    verilator = verilator_params(
        timeout = "long",
        # This test can take > 60 minutes, so mark it manual as it shouldn't
        # run in CI/nightlies.
        tags = ["manual"],
    ),
    deps = [
        "//hw/top:dt",
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
    # Broken on Verilator. See #24182.
    verilator = verilator_params(tags = ["broken"]),
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
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    qemu = qemu_params(
        globals = {
            # Test uses rstmgr, keep running on fatal resets:
            "ot-rstmgr.fatal_reset": 0,
        },
    ),
    deps = [
        "//hw/top:dt",
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
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    verilator = verilator_params(
        timeout = "long",
        tags = ["broken"],
    ),
    deps = [
        "//hw/top:dt",
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
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    qemu = qemu_params(
        globals = {
            # Test uses rstmgr, keep running on fatal resets:
            "ot-rstmgr.fatal_reset": 0,
        },
    ),
    deps = [
        "//hw/top:dt",
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
            "//hw/top_darjeeling:sim_dv": None,
        },
    ),
    local_defines = opentitan_if_ip(
        "usbdev",
        ["OT_HAS_USBDEV"],
        [],
    ),
    verilator = verilator_params(timeout = "long"),
    deps = [
        "//hw/top:dt",
        "//hw/top:i2c_c_regs",
        "//hw/top:spi_device_c_regs",
        "//hw/top:spi_host_c_regs",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:i2c",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:spi_device",
        "//sw/device/lib/dif:spi_host",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ] + opentitan_select_top(
        {
            "earlgrey": [
                "//hw/top:usbdev_c_regs",
                "//sw/device/lib/dif:usbdev",
            ],
            # Darjeeling doesn't have a USB Device to test
            "darjeeling": [],
        },
        ["@platforms//:incompatible"],
    ),
)

opentitan_test(
    name = "rv_plic_smoketest",
    srcs = ["rv_plic_smoketest.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//hw/top:dt",
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
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//hw/top:dt",
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
    name = "spi_device_tpm_tx_rx_test",
    srcs = ["spi_device_tpm_tx_rx_test.c"],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:sim_dv": None,
            "//hw/top_earlgrey:sim_verilator": None,
            "//hw/top_earlgrey:fpga_cw340_sival": None,
            "//hw/top_earlgrey:fpga_cw340_sival_rom_ext": None,
        },
    ),
    fpga = fpga_params(
        # This test requires the spi full duplex on the hyperdebug board.
        tags = ["manual"],
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/spi_device:spi_device_tpm_test",
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/spi_device:spi_device_tpm_test",
    ),
    # This test can take > 40 minutes, so mark it manual as it shouldn't run
    # in CI/nightlies.
    verilator = verilator_params(tags = ["manual"]),
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
        "//sw/device/lib/testing:spi_device_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:status",
    ],
)

opentitan_test(
    name = "spi_device_flash_smoketest",
    srcs = ["spi_device_flash_smoketest.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/spi_device:spi_device_flash_smoketest",
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap={firmware}
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/spi_device:spi_device_flash_smoketest",
    ),
    # This test can take > 40 minutes, so mark it manual as it shouldn't run
    # in CI/nightlies.
    verilator = verilator_params(tags = ["manual"]),
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

opentitan_test(
    name = "spi_device_ujson_console_test",
    srcs = ["spi_device_ujson_console_test.c"],
    exec_env = dicts.add(
        EARLGREY_CW340_TEST_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        },
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/spi_device_ujson_console_test",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:spi_device",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:spi_flash_testutils",
        "//sw/device/lib/testing/json:command",
        "//sw/device/lib/testing/json:provisioning_data",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ujson_ottf_commands",
    ],
)

opentitan_test(
    name = "spi_device_sleep_test",
    srcs = ["spi_device_sleep_test.c"],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        EARLGREY_CW340_TEST_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
        """,
        test_harness = "//sw/host/tests/chip/spi_device:spi_device_sleep_test",
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/chip/spi_device:spi_device_sleep_test",
    ),
    deps = [
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:base",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:spi_device",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
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
    exec_env = dicts.add(
        # This test requires a flash connected to the SPI bus,
        # which is not available in Verilator.
        dicts.omit(
            EARLGREY_TEST_ENVS,
            ["//hw/top_earlgrey:sim_verilator"],
        ),
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    fpga = fpga_params(timeout = "moderate"),
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
        dicts.omit(
            EARLGREY_TEST_ENVS,
            # This test requires an SPI flash on the bus, and therefore
            # cannot be tested in Verilator where this is not available.
            ["//hw/top_earlgrey:sim_verilator"],
        ),
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
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
    name = "spi_host_config_test",
    srcs = ["spi_host_config_test.c"],
    exec_env = dicts.add(
        EARLGREY_CW340_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
        },
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/spi_device:spi_host_config_test",
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/spi_device:spi_host_config_test",
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
        "//sw/device/lib/testing/test_framework:ottf_utils",
    ],
)

opentitan_test(
    name = "spi_host_irq_test",
    srcs = ["spi_host_irq_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
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
        "//hw/top:sensor_ctrl_c_regs",
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
        # This test can take > 60 minutes, so mark it manual as it shouldn't
        # run in CI/nightlies.
        tags = ["manual"],
    ),
    deps = [
        "//hw/top:sensor_ctrl_c_regs",
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
        "//hw/top:pwm_c_regs",
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
    exec_env = dicts.omit(
        dicts.add(
            EARLGREY_TEST_ENVS,
            EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        ),
        # TODO (#26100): QEMU's `flashgen.py` script does not like this test.
        ["//hw/top_earlgrey:sim_qemu_rom_with_fake_keys"],
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
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing:sram_ctrl_testutils",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
    ],
)

opentitan_test(
    name = "ottf_console_with_gpio_tx_indicator_test",
    srcs = ["ottf_console_with_gpio_tx_indicator_test.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
    },
    fpga = fpga_params(
        # We run this as part of the manuf test suite as we want to run it in
        # the hyper310 exec_env as this is most realistic of a provisioning
        # scenario where this feature will be used. Without this tag, the test
        # is not run in CI which causes a CI error ("Verify FPGA Jobs" check
        # will fail).
        tags = ["manuf"],
        test_cmd = """
            --clear-bitstream
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/ottf_console_with_gpio_tx_indicator",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing/json:provisioning_data",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
    ],
)

opentitan_test(
    name = "spi_device_ottf_console_test",
    srcs = ["spi_device_ottf_console_test.c"],
    exec_env = dicts.add(
        {
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        },
        EARLGREY_CW340_TEST_ENVS,
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/spi_device_ottf_console",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:spi_device",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:spi_flash_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
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
        # This test can take > 60 minutes, so mark it manual as it shouldn't
        # run in CI/nightlies.
        tags = ["manual"],
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
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    verilator = verilator_params(
        timeout = "long",
        # This test can take > 60 minutes, so mark it manual as it shouldn't
        # run in CI/nightlies.
        tags = ["manual"],
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
        DARJEELING_TEST_ENVS,
    ),
    deps = [
        "//hw/top:dt",
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
        EARLGREY_CW340_TEST_ENVS,
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//hw/top:dt",
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
            --no-wait-for-usb-device
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
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --no-wait-for-usb-device
        """,
        test_harness = "//sw/host/tests/chip/usb:usb_harness",
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --timeout=30s
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
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --no-wait-for-usb-device
        """,
        test_harness = "//sw/host/tests/chip/usb:usb_harness",
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
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --no-wait-for-usb-device
        """,
        test_harness = "//sw/host/tests/chip/usb:usb_harness",
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
    exec_env = dicts.add(
        dicts.omit(
            EARLGREY_TEST_ENVS,
            [
                "//hw/top_earlgrey:sim_dv",
                "//hw/top_earlgrey:sim_verilator",
            ],
        ),
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    fpga = fpga_params(
        tags = ["manual"],
        test_cmd = """
            --bootstrap="{firmware}"
            --wake=reset
        """,
        test_harness = "//sw/host/tests/chip/usb:usbdev_aon_wake",
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

opentitan_test(
    name = "usbdev_setuprx_test",
    srcs = ["usbdev_setuprx_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --no-wait-for-usb-device
        """,
        test_harness = "//sw/host/tests/chip/usb:usb_harness",
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
    # Broken on Verilator. See #24182.
    verilator = verilator_params(tags = ["broken"]),
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
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --no-wait-for-usb-device
        """,
        test_harness = "//sw/host/tests/chip/usb:usb_harness",
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
    verilator = verilator_params(
        timeout = "long",
        # Broken on Verilator. See #24182.
        tags = ["broken"],
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
    name = "usbdev_test",
    srcs = ["usbdev_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    fpga = fpga_params(
        tags = ["manual"],
        test_cmd = """
            --bootstrap="{firmware}"
        """,
        test_harness = "//sw/host/tests/chip/usb:usbdev_smoketest",
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --vbus-sense-en=VBUS_SENSE_EN
            --vbus-sense=VBUS_SENSE
        """,
        test_harness = "//sw/host/tests/chip/usb:usbdev_smoketest",
    ),
    verilator = verilator_params(timeout = "long"),
    deps = [
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
    name = "usbdev_mem_test",
    srcs = ["usbdev_mem_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
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
    name = "usbdev_mixed_test",
    srcs = ["usbdev_mixed_test.c"],
    data = [
        ":usbdev_stream_host_harness",
    ],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --exec=$(rootpath :usbdev_stream_host_harness)
        """,
        test_harness = "//sw/host/tests/chip/usb:usb_harness",
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
    data = [
        ":usbdev_stream_host_harness",
    ],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --exec=$(rootpath :usbdev_stream_host_harness)
        """,
        test_harness = "//sw/host/tests/chip/usb:usb_harness",
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
    data = [
        ":usbdev_stream_host_harness",
    ],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --exec=$(rootpath :usbdev_stream_host_harness)
        """,
        test_harness = "//sw/host/tests/chip/usb:usb_harness",
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
    name = "usbdev_toggle_restore_test",
    srcs = ["usbdev_toggle_restore_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --no-wait-for-usb-device
        """,
        test_harness = "//sw/host/tests/chip/usb:usb_harness",
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
        "//sw/device/lib/dif:usbdev",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "usbdev_tx_pkt_test",
    srcs = ["usbdev_tx_pkt_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    fpga = fpga_params(
        timeout = "eternal",
        tags = ["manual"],
        test_cmd = """
            --bootstrap="{firmware}"
            --no-wait-for-usb-device
        """,
        test_harness = "//sw/host/tests/chip/usb:usb_harness",
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --timeout=30s
            --vbus-sense-en=VBUS_SENSE_EN
            --vbus-sense=VBUS_SENSE
            --no-wait-for-usb-device
        """,
        test_harness = "//sw/host/tests/chip/usb:usb_harness",
    ),
    verilator = verilator_params(
        timeout = "eternal",
        tags = ["manual"],
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
    name = "usbdev_logging_test",
    srcs = ["usbdev_logging_test.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        "//hw/top_earlgrey:sim_dv": None,
        "//hw/top_earlgrey:sim_verilator": None,
    },
    fpga = fpga_params(
        timeout = "eternal",
        tags = [
            "manual",
            "slow_test",
        ],
    ),
    verilator = verilator_params(
        timeout = "long",
        # Broken on Verilator. See #24182.
        tags = ["broken"],
    ),
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

cc_library(
    name = "usbdev_suspend",
    srcs = ["usbdev_suspend.c"],
    hdrs = ["usbdev_suspend.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:usbdev",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing:sram_ctrl_testutils",
        "//sw/device/lib/testing:usb_testutils",
        "//sw/device/lib/testing:usb_testutils_streams",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
    ],
)

opentitan_test(
    name = "usbdev_suspend_resume_test",
    srcs = [
        "usbdev_suspend_resume_test.c",
    ],
    cw310 = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --fin-phase=suspend
            --init-phase=suspend
        """,
        test_harness = "//sw/host/tests/chip/usb:usbdev_suspend",
    ),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:fpga_cw310_test_rom": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --fin-phase=suspend
            --init-phase=suspend
            --vbus-sense-en=VBUS_SENSE_EN
            --vbus-sense=VBUS_SENSE
        """,
        test_harness = "//sw/host/tests/chip/usb:usbdev_suspend",
    ),
    verilator = verilator_params(timeout = "long"),
    deps = [
        "//sw/device/tests:usbdev_suspend",
    ],
)

opentitan_test(
    name = "usbdev_sleep_resume_test",
    srcs = [
        "usbdev_sleep_resume_test.c",
    ],
    cw310 = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --fin-phase=sleep-resume
            --init-phase=sleep-resume
        """,
        test_harness = "//sw/host/tests/chip/usb:usbdev_suspend",
    ),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:fpga_cw310_test_rom": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --fin-phase=sleep-resume
            --init-phase=sleep-resume
            --vbus-sense-en=VBUS_SENSE_EN
            --vbus-sense=VBUS_SENSE
        """,
        test_harness = "//sw/host/tests/chip/usb:usbdev_suspend",
    ),
    verilator = verilator_params(timeout = "long"),
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/tests:usbdev_suspend",
    ],
)

opentitan_test(
    name = "usbdev_sleep_reset_test",
    srcs = [
        "usbdev_sleep_reset_test.c",
    ],
    cw310 = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --fin-phase=sleep-reset
            --init-phase=sleep-resume
        """,
        test_harness = "//sw/host/tests/chip/usb:usbdev_suspend",
    ),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:fpga_cw310_test_rom": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --fin-phase=sleep-reset
            --init-phase=sleep-resume
            --vbus-sense-en=VBUS_SENSE_EN
            --vbus-sense=VBUS_SENSE
        """,
        test_harness = "//sw/host/tests/chip/usb:usbdev_suspend",
    ),
    verilator = verilator_params(timeout = "long"),
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/tests:usbdev_suspend",
    ],
)

opentitan_test(
    name = "usbdev_sleep_disconnect_test",
    srcs = [
        "usbdev_sleep_disconnect_test.c",
    ],
    cw310 = fpga_params(
        timeout = "eternal",
        tags = [
            "manual",
            "slow_test",
        ],
        test_cmd = """
            --bootstrap="{firmware}"
            --fin-phase=deep-resume
            --init-phase=sleep-disconnect
        """,
        test_harness = "//sw/host/tests/chip/usb:usbdev_suspend",
    ),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:fpga_cw310_test_rom": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --fin-phase=deep-resume
            --init-phase=sleep-disconnect
            --vbus-sense-en=VBUS_SENSE_EN
            --vbus-sense=VBUS_SENSE
        """,
        test_harness = "//sw/host/tests/chip/usb:usbdev_suspend",
    ),
    verilator = verilator_params(timeout = "long"),
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/tests:usbdev_suspend",
    ],
)

opentitan_test(
    name = "usbdev_deep_resume_test",
    srcs = [
        "usbdev_deep_resume_test.c",
    ],
    cw310 = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --fin-phase=deep-resume
            --init-phase=deep-resume
        """,
        test_harness = "//sw/host/tests/chip/usb:usbdev_suspend",
    ),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:fpga_cw310_test_rom": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --fin-phase=deep-resume
            --init-phase=deep-resume
            --vbus-sense-en=VBUS_SENSE_EN
            --vbus-sense=VBUS_SENSE
        """,
        test_harness = "//sw/host/tests/chip/usb:usbdev_suspend",
    ),
    verilator = verilator_params(timeout = "long"),
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/tests:usbdev_suspend",
    ],
)

opentitan_test(
    name = "usbdev_deep_reset_test",
    srcs = [
        "usbdev_deep_reset_test.c",
    ],
    cw310 = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --fin-phase=deep-reset
            --init-phase=deep-resume
        """,
        test_harness = "//sw/host/tests/chip/usb:usbdev_suspend",
    ),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:fpga_cw310_test_rom": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --fin-phase=deep-reset
            --init-phase=deep-resume
            --vbus-sense-en=VBUS_SENSE_EN
            --vbus-sense=VBUS_SENSE
        """,
        test_harness = "//sw/host/tests/chip/usb:usbdev_suspend",
    ),
    verilator = verilator_params(timeout = "long"),
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/tests:usbdev_suspend",
    ],
)

opentitan_test(
    name = "usbdev_deep_disconnect_test",
    srcs = [
        "usbdev_deep_disconnect_test.c",
    ],
    cw310 = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --fin-phase=shutdown
            --init-phase=deep-disconnect
        """,
        test_harness = "//sw/host/tests/chip/usb:usbdev_suspend",
    ),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:fpga_cw310_test_rom": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --fin-phase=shutdown
            --init-phase=deep-disconnect
            --vbus-sense-en=VBUS_SENSE_EN
            --vbus-sense=VBUS_SENSE
        """,
        test_harness = "//sw/host/tests/chip/usb:usbdev_suspend",
    ),
    verilator = verilator_params(timeout = "long"),
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/tests:usbdev_suspend",
    ],
)

opentitan_test(
    name = "usbdev_suspend_full_test",
    srcs = [
        "usbdev_suspend_full_test.c",
    ],
    # This test cannot be implemented on the CW310/CW340 because
    # there is no VBUS control so we cannot disconnect the device.
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:sim_dv": None,
        },
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            --fin-phase=shutdown
            --init-phase=suspend
            --vbus-sense-en=VBUS_SENSE_EN
            --vbus-sense=VBUS_SENSE
        """,
        test_harness = "//sw/host/tests/chip/usb:usbdev_suspend",
    ),
    verilator = verilator_params(timeout = "long"),
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/tests:usbdev_suspend",
    ],
)

opentitan_test(
    name = "rstmgr_alert_info_test",
    srcs = ["rstmgr_alert_info_test.c"],
    broken = fpga_params(tags = ["broken"]),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
            # TODO(lowrisc/opentitan#20589): Enable _sival* tests when bug is fixed
            "//hw/top_earlgrey:fpga_cw310_sival": "broken",
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": "broken",
            "//hw/top_darjeeling:sim_dv": None,
        },
    ),
    fpga = fpga_params(
        timeout = "moderate",
    ),
    qemu = qemu_params(
        globals = {
            # Test uses rstmgr, keep running on fatal resets:
            "ot-rstmgr.fatal_reset": 0,
        },
    ),
    silicon = silicon_params(
        tags = ["broken"],
    ),
    verilator = verilator_params(
        timeout = "long",
        tags = ["broken"],
    ),
    deps = [
        "//hw/top:alert_handler_c_regs",
        "//hw/top:dt",
        "//sw/device/lib/arch:boot_stage",
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
        "//sw/device/lib/testing:ret_sram_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ] + opentitan_select_top(
        {
            "earlgrey": [
                "//sw/device/lib/dif:flash_ctrl",
                "//sw/device/lib/testing:flash_ctrl_testutils",
                "//sw/device/lib/testing:keymgr_testutils",
            ],
        },
        [],
    ),
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
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//sw/device/lib/base:memory",
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
        "//hw/top_darjeeling:sim_dv": None,
    },
    deps = [
        "//hw/top:dt",
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
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        DARJEELING_TEST_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    silicon = silicon_params(
        tags = ["broken"],
    ),
    deps = [
        "//hw/top:dt",
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
        DARJEELING_TEST_ENVS,
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
    src = "//hw/top_earlgrey/data/otp:otp_json_rma",
    overlays = STD_OTP_OVERLAYS + [":power_virus_systemtest_otp_overlay"],
    visibility = ["//visibility:private"],
)

opentitan_test(
    name = "power_virus_systemtest",
    srcs = ["power_virus_systemtest.c"],
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
    fpga = fpga_params(
        otp = "//hw/top_earlgrey/data/otp/emulation:otp_img_prod_manuf_personalized",
        test_cmd = """
            --bootstrap="{firmware}"
        """,
        test_harness = "//sw/host/tests/chip/power_virus",
    ),
    silicon = silicon_params(
        timeout = "long",
        tags = ["broken"],
    ),
    deps = [
        "//hw/ip/aes:model",
        "//hw/top:adc_ctrl_c_regs",
        "//hw/top:aes_c_regs",
        "//hw/top:csrng_c_regs",
        "//hw/top:dt",
        "//hw/top:entropy_src_c_regs",
        "//hw/top:gpio_c_regs",
        "//hw/top:hmac_c_regs",
        "//hw/top:i2c_c_regs",
        "//hw/top:kmac_c_regs",
        "//hw/top:pattgen_c_regs",
        "//hw/top:pwm_c_regs",
        "//hw/top:spi_host_c_regs",
        "//hw/top:uart_c_regs",
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
        "//sw/device/lib/testing:alert_handler_testutils",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:hmac_testutils",
        "//sw/device/lib/testing:i2c_testutils",
        "//sw/device/lib/testing:otbn_testutils_rsa",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing:spi_device_testutils",
        "//sw/device/lib/testing:spi_host_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "spi_passthru_test",
    srcs = ["spi_passthru_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    fpga = fpga_params(
        timeout = "long",
        tags = ["slow_test"],
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/spi_device:spi_passthru",
    ),
    silicon = silicon_params(
        timeout = "long",
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/spi_device:spi_passthru",
    ),
    # This test can take > 40 minutes, so mark it manual as it shouldn't run
    # in CI/nightlies.
    verilator = verilator_params(tags = ["manual"]),
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
        "//sw/device/lib/testing/test_framework:ujson_ottf_commands",
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
    src = "//hw/top_earlgrey/data/otp:otp_json_rma",
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
    "test_unlocked1": "//hw/top_earlgrey/data/otp/emulation:otp_img_test_unlocked1_manuf_individualized",
    "test_locked0": "//hw/top_earlgrey/data/otp/emulation:otp_img_test_locked0_manuf_initialized",
    "dev": "//hw/top_earlgrey/data/otp/emulation:otp_img_dev_manuf_personalized",
    "prod": "//hw/top_earlgrey/data/otp/emulation:otp_img_prod_manuf_personalized",
    "prod_end": "//hw/top_earlgrey/data/otp/emulation:otp_img_prod_end_manuf_personalized",
    "rma": "//hw/top_earlgrey/data/otp/emulation:otp_img_rma_manuf_personalized",
}

_RV_DM_JTAG_LC_STATES = get_lc_items(
    CONST.LCV.TEST_UNLOCKED1,
    CONST.LCV.DEV,
    CONST.LCV.RMA,
)

_RV_DM_TEST_CONFIGURATIONS = [
    {
        "name": "test_unlocked1",
        "lc_state": "test_unlocked1",
        "rv_dm_delayed_en": "",
        "otp": _SIVAL_OTP_IMAGE["test_unlocked1"],
    },
    {
        "name": "dev_rv_dm_default_enabled",
        "lc_state": "dev",
        "rv_dm_delayed_en": "",
        "otp": _SIVAL_OTP_IMAGE["dev"],
    },
    {
        "name": "dev_rv_dm_delayed_enabled",
        "lc_state": "dev",
        "rv_dm_delayed_en": "--rv-dm-delayed-enable",
        "otp": "//hw/top_earlgrey/data/otp/emulation:otp_img_dev_manuf_personalized_enable_rv_dm_late_debug_enable",
    },
    {
        "name": "rma",
        "lc_state": "rma",
        "rv_dm_delayed_en": "",
        "otp": _SIVAL_OTP_IMAGE["rma"],
    },
]

[
    opentitan_test(
        name = "rv_dm_csr_rw_{}".format(test_cfg["name"]),
        srcs = ["rv_dm_delayed_enable.c"],
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:fpga_cw340_sival": None,
        },
        fpga = fpga_params(
            needs_jtag = True,
            otp = test_cfg["otp"],
            rv_dm_delayed_en = test_cfg["rv_dm_delayed_en"],
            tags = [
                "lc_{}".format(test_cfg["lc_state"]),
            ],
            test_cmd = """
                --bootstrap="{firmware}"
                {rv_dm_delayed_en}
            """,
            test_harness = "//sw/host/tests/chip/rv_dm:csr_rw",
        ),
        deps = [
            "//sw/device/lib/base:multibits",
            "//sw/device/lib/dif:lc_ctrl",
            "//sw/device/lib/dif:rv_dm",
            "//sw/device/lib/runtime:hart",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing:lc_ctrl_testutils",
            "//sw/device/lib/testing/test_framework:ottf_main",
        ],
    )
    for test_cfg in _RV_DM_TEST_CONFIGURATIONS
]

test_suite(
    name = "rv_dm_csr_rw",
    tags = ["manual"],
    tests = [
        ":rv_dm_csr_rw_{}".format(test_cfg["name"])
        for test_cfg in _RV_DM_TEST_CONFIGURATIONS
    ],
)

[
    opentitan_test(
        name = "rv_dm_mem_access_{}".format(test_cfg["name"]),
        srcs = ["rv_dm_delayed_enable.c"],
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:fpga_cw340_sival": None,
        },
        fpga = fpga_params(
            timeout = "moderate",
            needs_jtag = True,
            otp = test_cfg["otp"],
            rv_dm_delayed_en = test_cfg["rv_dm_delayed_en"],
            tags = [
                "lc_{}".format(test_cfg["lc_state"]),
            ],
            test_cmd = """
                --rom={rom:binary}
                --bootstrap="{firmware}"
                {rv_dm_delayed_en}
            """,
            test_harness = "//sw/host/tests/chip/rv_dm:mem_access",
        ),
        deps = [
            "//sw/device/lib/base:multibits",
            "//sw/device/lib/dif:lc_ctrl",
            "//sw/device/lib/dif:rv_dm",
            "//sw/device/lib/runtime:hart",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing:lc_ctrl_testutils",
            "//sw/device/lib/testing/test_framework:ottf_main",
        ],
    )
    for test_cfg in _RV_DM_TEST_CONFIGURATIONS
]

test_suite(
    name = "rv_dm_mem_access",
    tags = ["manual"],
    tests = [
        ":rv_dm_mem_access_{}".format(test_cfg["name"])
        for test_cfg in _RV_DM_TEST_CONFIGURATIONS
    ],
)

[
    opentitan_test(
        name = "rv_dm_jtag_{}".format(lc_state),
        srcs = ["example_test_from_flash.c"],
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:fpga_cw340_sival": None,
        },
        fpga = fpga_params(
            needs_jtag = True,
            otp = _SIVAL_OTP_IMAGE[lc_state],
            tags = [
                "lc_{}".format(lc_state),
            ],
            test_harness = "//sw/host/tests/chip/rv_dm:jtag",
        ),
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
    CONST.LCV.DEV,
    CONST.LCV.PROD,
    CONST.LCV.RMA,
)

[
    opentitan_test(
        name = "rv_dm_jtag_tap_sel_{}".format(lc_state),
        srcs = ["example_test_from_flash.c"],
        exec_env = dicts.add(
            EARLGREY_SILICON_OWNER_ROM_EXT_ENVS if lc_state == "prod" else {},
            {
                "//hw/top_earlgrey:fpga_cw310_sival": None,
                "//hw/top_earlgrey:fpga_cw340_sival": None,
            },
        ),
        fpga = fpga_params(
            needs_jtag = True,
            otp = _SIVAL_OTP_IMAGE[lc_state],
            tags = [
                "lc_{}".format(lc_state),
            ],
            test_harness = "//sw/host/tests/chip/rv_dm:jtag_tap_sel",
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
        exec_env = dicts.add(
            EARLGREY_SILICON_OWNER_ROM_EXT_ENVS if lc_state == "prod" else {},
            {
                "//hw/top_earlgrey:fpga_cw310_sival": None,
                "//hw/top_earlgrey:fpga_cw340_sival": None,
            },
        ),
        fpga = fpga_params(
            otp = _SIVAL_OTP_IMAGE[lc_state],
            tags = [
                "lc_{}".format(lc_state),
            ],
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
        exec_env = dicts.add(
            EARLGREY_SILICON_OWNER_ROM_EXT_ENVS if lc_state == "prod" else {},
            {
                "//hw/top_earlgrey:fpga_cw310_sival": None,
                "//hw/top_earlgrey:fpga_cw340_sival": None,
            },
        ),
        fpga = fpga_params(
            needs_jtag = True,
            otp = _SIVAL_OTP_IMAGE[lc_state],
            tags = [
                "lc_{}".format(lc_state),
            ],
            test_cmd = " --expect-fail" if lc_state_val in _LC_STATES_DEBUG_DISALLOWED else "",
            test_harness = "//sw/host/tests/chip/rv_dm:lc_disabled",
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
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:sim_dv": None,
            "//hw/top_darjeeling:sim_dv": None,
        },
        fpga = fpga_params(
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
        deps = [
            "//hw/top:dt",
            "//hw/top:otp_ctrl_c_regs",
            "//hw/top:pinmux_c_regs",
            "//sw/device/lib/base:mmio",
            "//sw/device/lib/dif:rstmgr",
            "//sw/device/lib/runtime:hart",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing:rstmgr_testutils",
            "//sw/device/lib/testing/test_framework:check",
            "//sw/device/lib/testing/test_framework:ottf_main",
        ] + opentitan_select_top(
            {
                "darjeeling": [
                    "//hw/top:keymgr_dpe_c_regs",
                ],
            },
            [
                "//hw/top:adc_ctrl_c_regs",
                "//hw/top:flash_ctrl_c_regs",
                "//hw/top:keymgr_c_regs",
                "//hw/top:sysrst_ctrl_c_regs",
            ],
        ),
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
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
        fpga = fpga_params(
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
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
        fpga = fpga_params(
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
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
        fpga = fpga_params(
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
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
        fpga = fpga_params(
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
        deps = [
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
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
        },
        fpga = fpga_params(
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
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_sival": None,
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
    },
    fpga = fpga_params(
        needs_jtag = True,
        otp = "//hw/top_earlgrey/data/otp:img_test_unlocked0",
        # TODO(#22823): Remove "broken" tag once the test is fixed.
        tags = ["broken"],
        test_cmd = """
            --bootstrap="{firmware}"
        """,
        test_harness = "//sw/host/tests/chip/jtag:openocd_test",
    ),
    deps = [
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "i2c_target_smbus_arp_test",
    srcs = [
        "i2c_target_smbus_arp_test.c",
    ],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_sival": None,
    },
    fpga = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/i2c_target:i2c_target_smbus_arp",
    ),
    deps = [
        "//sw/device/lib/arch:device",
        "//sw/device/lib/dif:i2c",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/testing:i2c_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/json:command",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/testing/test_framework:ujson_ottf_commands",
    ],
)

opentitan_test(
    name = "i2c_host_override_test",
    srcs = [
        "i2c_host_override_test.c",
    ],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
        },
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/i2c_host_override",
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
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
        },
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
        """,
        test_harness = "//sw/host/tests/chip/i2c_target",
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
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
    },
    fpga = fpga_params(
        exit_failure = "PASS!",
        exit_success = _STATUS_REPORT_TEST_MSG,
    ),
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
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
    },
    fpga = fpga_params(
        exit_failure = "PASS!",
        exit_success = _STATUS_REPORT_OVERFLOW_TEST_MSG,
    ),
    deps = [
        "//sw/device/lib/base:status_report_unittest_c",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "example_sival",
    srcs = ["example_sival.c"],
    # We only run this test on the Hyper310 FPGA (the `fpga_cw310_sival_rom_ext`
    # platform (as well as the RTL sim platforms) as these are the only
    # compatible with both pre- and post-silicon test environments.
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
        "//hw/top_earlgrey:sim_dv": None,
        "//hw/top_earlgrey:sim_verilator": None,
    },
    fpga = fpga_params(
        test_cmd = " ".join([
            "--bootstrap=\"{firmware}\"",
            "\"{firmware:elf}\"",
        ]),
        test_harness = "//sw/host/tests/chip/example_sival",
    ),
    # This test can take > 40 minutes, so mark it manual as it shouldn't run
    # in CI/nightlies.
    verilator = verilator_params(tags = ["manual"]),
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ottf_utils",
    ],
)

opentitan_test(
    name = "sysrst_ctrl_inputs_test",
    srcs = ["sysrst_ctrl_inputs_test.c"],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/sysrst_ctrl:sysrst_ctrl_inputs",
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
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/sysrst_ctrl:sysrst_ctrl_outputs",
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/sysrst_ctrl:sysrst_ctrl_outputs",
    ),
    deps = [
        "//hw/top:dt",
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
    name = "sysrst_ctrl_in_irq_test",
    srcs = ["sysrst_ctrl_in_irq_test.c"],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/sysrst_ctrl:sysrst_ctrl_in_irq",
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
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
        """,
        test_harness = "//sw/host/tests/chip/sysrst_ctrl:sysrst_ctrl_ec_rst_l",
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
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
        """,
        test_harness = "//sw/host/tests/chip/sysrst_ctrl:sysrst_ctrl_ulp_z3_wakeup",
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
        """,
        test_harness = "//sw/host/tests/chip/sysrst_ctrl:sysrst_ctrl_ulp_z3_wakeup",
    ),
    deps = [
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:sysrst_ctrl",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
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
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/sysrst_ctrl:sysrst_ctrl_reset",
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
            "{firmware:elf}"
        """,
        test_harness = "//sw/host/tests/chip/sysrst_ctrl:sysrst_ctrl_reset",
    ),
    deps = [
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
    name = "sram_ctrl_readback_test",
    srcs = ["sram_ctrl_readback_test.c"],
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
    exec_env = dicts.add(
        # This test is not compatible with the test_rom because the test_rom
        # does not respect the exec_disabled OTP config word.
        dicts.omit(
            EARLGREY_TEST_ENVS,
            ["//hw/top_earlgrey:fpga_cw310_test_rom"],
        ),
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    fpga = fpga_params(
        binaries = {
            ":rv_core_ibex_isa_test_sram": "sram_program",
        },
        needs_jtag = True,
        otp = "//sw/device/silicon_creator/manuf/tests:otp_img_rom_exec_disabled_test_unlocked0",
        test_cmd = "--elf={sram_program}",
        test_harness = "//sw/host/tests/chip/rv_core_ibex_isa",
    ),
    silicon = silicon_params(
        needs_jtag = True,
        tags = ["manual"],
        test_cmd = "--elf={firmware}",
        test_harness = "//sw/host/tests/chip/rv_core_ibex_isa",
    ),
    # This test can take > 40 minutes, so mark it manual as it shouldn't run
    # in CI/nightlies.
    verilator = verilator_params(tags = ["manual"]),
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
    exec_env = dicts.add(
        # This test is not compatible with the test_rom because the test_rom
        # does not respect the exec_disabled OTP config word.
        dicts.omit(
            EARLGREY_TEST_ENVS,
            ["//hw/top_earlgrey:fpga_cw310_test_rom"],
        ),
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:fpga_cw340_sival": None,
        },
    ),
    fpga = fpga_params(
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
        needs_jtag = True,
        test_cmd = "--elf={firmware}",
        test_harness = "//sw/host/tests/chip/rv_core_ibex_epmp",
    ),
    # This test can take > 40 minutes, so mark it manual as it shouldn't run
    # in CI/nightlies.
    verilator = verilator_params(tags = ["manual"]),
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
        "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
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
        "//sw/device/lib/testing/test_framework:ottf_console",
        "//sw/device/lib/testing/test_framework:ottf_test_config",
        "//sw/device/lib/testing/test_framework:status",
        "//sw/device/silicon_creator/lib:dbg_print",
        "//sw/device/silicon_creator/manuf/lib:sram_start",
    ],
)

opentitan_test(
    name = "uart_tx_rx_test",
    srcs = ["uart_tx_rx_test.c"],
    broken = fpga_params(tags = ["broken"]),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_CW340_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
            # See #23468, currently broken on SAM3X execution environments.
            "//hw/top_earlgrey:fpga_cw310_test_rom": "broken",
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": "broken",
        },
    ),
    fpga = fpga_params(
        test_cmd = " ".join([
            "--bootstrap=\"{firmware}\"",
            "--firmware-elf=\"{firmware:elf}\"",
        ]),
        test_harness = "//sw/host/tests/chip/uart:uart_tx_rx",
    ),
    silicon = silicon_params(
        test_cmd = " ".join([
            "--bootstrap=\"{firmware}\"",
            "--firmware-elf=\"{firmware:elf}\"",
        ]),
        test_harness = "//sw/host/tests/chip/uart:uart_tx_rx",
    ),
    # This test can take > 40 minutes, so mark it manual as it shouldn't run
    # in CI/nightlies.
    verilator = verilator_params(tags = ["manual"]),
    deps = [
        "//hw/top:clkmgr_c_regs",
        "//hw/top:lc_ctrl_c_regs",
        "//hw/top:pinmux_c_regs",
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
    exec_env = dicts.add(
        # This test is not compatible with the test_rom because the test_rom
        # does not respect the exec_disabled OTP config word.
        dicts.omit(
            EARLGREY_TEST_ENVS,
            ["//hw/top_earlgrey:fpga_cw310_test_rom"],
        ),
        {
            "//hw/top_earlgrey:silicon_creator": None,
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:fpga_cw340_sival": None,
        },
    ),
    fpga = fpga_params(
        binaries = {
            ":rv_core_ibex_mem_test_sram": "sram_program",
        },
        needs_jtag = True,
        otp = "//sw/device/silicon_creator/manuf/tests:otp_img_rom_exec_disabled_test_unlocked0",
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
    # This test can take > 40 minutes, so mark it manual as it shouldn't run
    # in CI/nightlies.
    verilator = verilator_params(tags = ["manual"]),
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
        "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
        "//hw/top_earlgrey:silicon_creator": None,
    },
    kind = "ram",
    linker_script = "//sw/device/silicon_creator/manuf/lib:sram_program_linker_script",
    deps = [
        "//hw/top:pwm_c_regs",
        "//hw/top:rv_timer_c_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:pmp",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_console",
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
        dicts.omit(
            EARLGREY_TEST_ENVS,
            ["//hw/top_earlgrey:sim_verilator"],
        ),
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    deps = [
        "//hw/top:pwm_c_regs",
        "//hw/top:rv_timer_c_regs",
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
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    fpga = fpga_params(
        test_cmd = " ".join([
            "--bootstrap=\"{firmware}\"",
            "--firmware-elf=\"{firmware:elf}\"",
        ]),
        test_harness = "//sw/host/tests/chip/uart:uart_baud_rate",
    ),
    silicon = silicon_params(
        test_cmd = " ".join([
            "--bootstrap=\"{firmware}\"",
            "--firmware-elf=\"{firmware:elf}\"",
        ]),
        test_harness = "//sw/host/tests/chip/uart:uart_baud_rate",
    ),
    # This test can take > 40 minutes, so mark it manual as it shouldn't run
    # in CI/nightlies.
    verilator = verilator_params(tags = ["manual"]),
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
    broken = fpga_params(tags = ["broken"]),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            # See #23468: currently broken over the SAM3X interface.
            "//hw/top_earlgrey:fpga_cw310_test_rom": "broken",
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": "broken",
        },
    ),
    fpga = fpga_params(
        test_cmd = " ".join([
            "--bootstrap=\"{firmware}\"",
            "--firmware-elf=\"{firmware:elf}\"",
        ]),
        test_harness = "//sw/host/tests/chip/uart:uart_loopback",
    ),
    silicon = silicon_params(
        test_cmd = " ".join([
            "--bootstrap=\"{firmware}\"",
            "--firmware-elf=\"{firmware:elf}\"",
        ]),
        test_harness = "//sw/host/tests/chip/uart:uart_loopback",
    ),
    # This test can take > 40 minutes, so mark it manual as it shouldn't run
    # in CI/nightlies.
    verilator = verilator_params(tags = ["manual"]),
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
    # This takes around 2 hours to run on Verilator, and so should only be
    # run manually for debugging purposes.
    verilator = verilator_params(tags = ["manual"]),
    deps = [
        ":otbn_randomness_impl",
        "//hw/top:entropy_src_c_regs",
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
        "//sw/device/lib/testing:entropy_src_testutils",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:hmac_testutils",
        "//sw/device/lib/testing:kmac_testutils",
        "//sw/device/lib/testing:rand_testutils",
        "//sw/device/lib/testing:rv_core_ibex_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "uart_parity_break_test",
    srcs = ["uart_parity_break_test.c"],
    broken = fpga_params(tags = ["broken"]),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            # See #23468: currently broken over the SAM3X interface.
            "//hw/top_earlgrey:fpga_cw310_test_rom": "broken",
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": "broken",
        },
    ),
    fpga = fpga_params(
        test_cmd = " ".join([
            "--bootstrap=\"{firmware}\"",
            "--firmware-elf=\"{firmware:elf}\"",
        ]),
        test_harness = "//sw/host/tests/chip/uart:uart_parity_break",
    ),
    silicon = silicon_params(
        test_cmd = " ".join([
            "--bootstrap=\"{firmware}\"",
            "--firmware-elf=\"{firmware:elf}\"",
        ]),
        test_harness = "//sw/host/tests/chip/uart:uart_parity_break",
    ),
    # This test can take > 40 minutes, so mark it manual as it shouldn't run
    # in CI/nightlies.
    verilator = verilator_params(tags = ["manual"]),
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
        EARLGREY_CW340_TEST_ENVS,
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_darjeeling:sim_dv": None,
        },
    ),
    deps = [
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base:stdasm",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing:sram_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ottf_utils",
    ],
)

opentitan_test(
    name = "pwrmgr_usbdev_smoketest",
    srcs = ["pwrmgr_usbdev_smoketest.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    # Broken on Verilator. See #24182.
    verilator = verilator_params(tags = ["broken"]),
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
    name = "pwrmgr_lowpower_cancel_test",
    srcs = ["pwrmgr_lowpower_cancel_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    deps = [
        "//hw/top:pwrmgr_c_regs",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "sram_ctrl_lc_escalation_test",
    srcs = ["sram_ctrl_lc_escalation_test.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_sival": None,
    },
    fpga = fpga_params(
        timeout = "moderate",
        needs_jtag = True,
        otp = "//hw/top_earlgrey/data/otp/emulation:otp_img_rma_manuf_personalized",
        test_cmd = " ".join([
            "--bootstrap=\"{firmware}\"",
            "--firmware-elf=\"{firmware:elf}\"",
        ]),
        test_harness = "//sw/host/tests/chip/sram_ctrl:sram_ctrl_lc_escalation",
    ),
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
    name = "sleep_pin_mio_dio_val_test",
    srcs = ["sleep_pin_mio_dio_val_test.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw340_sival": None,
            "//hw/top_earlgrey:fpga_cw340_sival_rom_ext": None,
            "//hw/top_darjeeling:sim_dv": None,
        },
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
        """,
        test_harness = "//sw/host/tests/chip/gpio:sleep_pin_mio_dio_val",
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
        """,
        test_harness = "//sw/host/tests/chip/gpio:sleep_pin_mio_dio_val",
    ),
    # This test can take > 40 minutes, so mark it manual as it shouldn't run
    # in CI/nightlies.
    verilator = verilator_params(tags = ["manual"]),
    deps = [
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rand_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "sleep_pin_retention_test",
    srcs = ["sleep_pin_retention_test.c"],
    broken = fpga_params(tags = ["broken"]),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            # See #23468, currently broken in SAM3X execution environments.
            "//hw/top_earlgrey:fpga_cw310_test_rom": "broken",
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": "broken",
        },
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap="{firmware}"
        """,
        test_harness = "//sw/host/tests/chip/gpio:sleep_pin_retention",
    ),
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
        """,
        test_harness = "//sw/host/tests/chip/gpio:sleep_pin_retention",
    ),
    # This test can take > 40 minutes, so mark it manual as it shouldn't run
    # in CI/nightlies.
    verilator = verilator_params(tags = ["manual"]),
    deps = [
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rand_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "pattgen_ios_test",
    srcs = ["pattgen_ios_test.c"],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
    ),
    fpga = fpga_params(
        test_cmd = """
            --bootstrap={firmware}
            --firmware-elf=\"{firmware:elf}\"
        """,
        test_harness = "//sw/host/tests/chip/pattgen:pattgen_ios",
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
    name = "hmac_error_conditions_test",
    srcs = ["hmac_error_conditions_test.c"],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:sim_verilator": None,
            "//hw/top_earlgrey:fpga_cw340_sival": None,
        },
        DARJEELING_TEST_ENVS,
    ),
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/top:dt",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:hmac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:hmac_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

cc_library(
    name = "rom_exit_immediately_lib",
    srcs = ["rom_exit_immediately.S"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:rv_core_ibex",
        "//sw/device/silicon_creator/lib/base:static_critical",
    ],
)

opentitan_test(
    name = "rom_exit_immediately",
    exec_env = {
        "//hw/top_earlgrey:sim_qemu_base": None,
    },
    kind = "rom",
    linker_script = "//sw/device/lib/testing/test_rom:linker_script",
    qemu = qemu_params(
        # This test doesn't print `PASS!`, just check the exit code.
        test_harness = "//third_party/qemu:qemu-system-riscv32",
    ),
    deps = [":rom_exit_immediately_lib"],
)

opentitan_test(
    name = "dma_inline_hashing",
    srcs = ["dma_inline_hashing.c"],
    exec_env = DARJEELING_TEST_ENVS,
    deps = [
        "//hw/top:dt",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:dma",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:spi_host",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:dma_testutils",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "dma_abort",
    srcs = ["dma_abort.c"],
    exec_env = DARJEELING_TEST_ENVS,
    deps = [
        "//hw/top:dt",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:dma",
        "//sw/device/lib/dif:spi_host",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:dma_testutils",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "keymgr_dpe_key_derivation_test",
    srcs = ["keymgr_dpe_key_derivation_test.c"],
    exec_env = DARJEELING_TEST_ENVS,
    deps = [
        "//hw/top:dt",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/dif:keymgr_dpe",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:keymgr_dpe_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "mbx_smoketest",
    srcs = ["mbx_smoketest.c"],
    exec_env = DARJEELING_TEST_ENVS,
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/dif:mbx",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:sram_ctrl",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "soc_proxy_smoketest",
    srcs = ["soc_proxy_smoketest.c"],
    exec_env = DARJEELING_TEST_ENVS,
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:soc_proxy",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "soc_proxy_external_alerts",
    srcs = ["soc_proxy_external_alerts.c"],
    exec_env = DARJEELING_TEST_ENVS,
    deps = [
        "//sw/device/lib/dif:alert_handler",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:soc_proxy",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:alert_handler_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "soc_proxy_external_wakeup",
    srcs = ["soc_proxy_external_wakeup.c"],
    exec_env = DARJEELING_TEST_ENVS,
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:status",
    ],
)

opentitan_test(
    name = "soc_proxy_gpios",
    srcs = ["soc_proxy_gpios.c"],
    exec_env = DARJEELING_TEST_ENVS,
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:soc_proxy",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:status",
    ],
)
