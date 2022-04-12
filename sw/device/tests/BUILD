# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan_test.bzl", "opentitan_functest", "verilator_params")

opentitan_functest(
    name = "aes_idle_test",
    srcs = ["aes_idle_test.c"],
    verilator = verilator_params(
        tags = [
            "cpu:4",
            "failing_verilator",
        ],
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aes",
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aes_testutils",
        "//sw/device/lib/testing:clkmgr_testutils",
        "//sw/device/lib/testing:entropy_testutils",
    ],
)

# FIXME(lowRISC/opentitan#12065) This is a hack to work around currently
# only supporting one top.
#
# See //hw/top_englishbreakfast/util/prepare_sw.py for where this is set.
config_setting(
    name = "is_english_breakfast",
    values = {"copt": "-DOT_IS_ENGLISH_BREAKFAST_REDUCED_SUPPORT_FOR_INTERNAL_USE_ONLY_"},
    visibility = ["//visibility:private"],
)

cc_library(
    name = "nothing",
    visibility = ["//visibility:private"],
)

alias(
    name = "aes_smoketest_entropy_testutils",
    actual = select({
        ":is_english_breakfast": ":nothing",
        "//conditions:default": "//sw/device/lib/testing:entropy_testutils",
    }),
    visibility = ["//visibility:private"],
)

opentitan_functest(
    name = "aes_smoketest",
    srcs = ["aes_smoketest.c"],
    deps = [
        ":aes_smoketest_entropy_testutils",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aes_testutils",
    ],
)

opentitan_functest(
    name = "aon_timer_irq_test",
    srcs = ["aon_timer_irq_test.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib:irq",
        "//sw/device/lib/base:math",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:rv_timer",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:rand_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
    ],
)

opentitan_functest(
    name = "aon_timer_smoketest",
    srcs = ["aon_timer_smoketest.c"],
    deps = [
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aon_timer_testutils",
    ],
)

opentitan_functest(
    name = "aon_timer_wdog_bite_reset_test",
    srcs = ["aon_timer_wdog_bite_reset_test.c"],
    verilator = verilator_params(
        tags = [
            "cpu:4",
            "failing_verilator",
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
    ],
)

opentitan_functest(
    name = "aon_timer_wdog_lc_escalate_test",
    srcs = ["aon_timer_wdog_lc_escalate_test.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib:irq",
        "//sw/device/lib/base:math",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:alert_handler",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:rv_timer",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:alert_handler_testutils",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
    ],
)

opentitan_functest(
    name = "clkmgr_external_clk_src_for_sw_test",
    srcs = ["clkmgr_external_clk_src_for_sw_test.c"],
    verilator = verilator_params(
        tags = [
            "cpu:4",
            "failing_verilator",
        ],
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/dif:base",
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:clkmgr_testutils",
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
    ],
)

opentitan_functest(
    name = "clkmgr_off_peri_test",
    srcs = ["clkmgr_off_peri_test.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:base",
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aon_timer_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
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
    ],
)

opentitan_functest(
    name = "coverage_test",
    srcs = ["coverage_test.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
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
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:csrng",
        "//sw/device/lib/runtime:log",
    ],
)

opentitan_functest(
    name = "entropy_src_fw_ovr_test",
    srcs = ["entropy_src_fw_ovr_test.c"],
    verilator = verilator_params(
        tags = [
            "cpu:4",
            "failing_verilator",
        ],
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/runtime:log",
    ],
)

opentitan_functest(
    name = "entropy_src_smoketest",
    srcs = ["entropy_src_smoketest.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/runtime:log",
    ],
)

opentitan_functest(
    name = "example_test_from_flash",
    srcs = ["example_test_from_flash.c"],
)

opentitan_functest(
    name = "example_test_from_rom",
    srcs = ["example_test_from_rom.c"],
    # This test doesn't use the OTTF.
    ottf = [],
    targets = ["verilator"],  # Can only run in verilator right now.
    # This test is designed to run and complete entirely in the ROM boot stage.
    # Setting the `test_in_rom` flag makes the `opentitan_functest` rule aware
    # of this, and instructs it to load the test image into ROM (rather than
    # loading the default test ROM, or any other ROM that may be specified via
    # Verilator or CW310 params).
    test_in_rom = True,
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib:pinmux",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing/test_framework",
        "//sw/device/lib/testing/test_rom:linker_script",
        "//sw/device/lib/testing/test_rom:test_rom_lib",
    ],
)

opentitan_functest(
    name = "flash_ctrl_idle_low_power_test",
    srcs = ["flash_ctrl_idle_low_power_test.c"],
    verilator = verilator_params(
        tags = [
            "cpu:4",
            "failing_verilator",
        ],
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib:irq",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing:rand_testutils",
    ],
)

opentitan_functest(
    name = "flash_ctrl_ops_test",
    srcs = ["flash_ctrl_ops_test.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib:irq",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
    ],
)

opentitan_functest(
    name = "flash_ctrl_test",
    srcs = ["flash_ctrl_test.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib:flash_ctrl",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/runtime:log",
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
    name = "hmac_enc_irq_test",
    srcs = ["hmac_enc_irq_test.c"],
    verilator = verilator_params(
        tags = [
            "cpu:4",
            "failing_verilator",
        ],
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib:irq",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:hmac",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:hmac_testutils",
        "//sw/device/lib/testing:isr_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
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
    ],
)

opentitan_functest(
    name = "hmac_smoketest",
    srcs = ["hmac_smoketest.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib:flash_ctrl",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:hmac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:hmac_testutils",
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
    ],
)

opentitan_functest(
    name = "kmac_mode_cshake_test",
    srcs = ["kmac_mode_cshake_test.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib:flash_ctrl",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/runtime:log",
    ],
)

opentitan_functest(
    name = "kmac_mode_kmac_test",
    srcs = ["kmac_mode_kmac_test.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib:flash_ctrl",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/runtime:log",
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
        "//sw/device/lib:irq",
        "//sw/device/lib/dif:otbn",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:otbn",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/otbn/crypto:p256_ecdsa",
    ],
)

opentitan_functest(
    name = "otbn_irq_test",
    srcs = ["otbn_irq_test.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib:irq",
        "//sw/device/lib/dif:otbn",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:otbn",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/otbn/code-snippets:err_test",
    ],
)

opentitan_functest(
    name = "otbn_mem_scramble_test",
    srcs = ["otbn_mem_scramble_test.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:base",
        "//sw/device/lib/dif:otbn",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:otbn",
        "//sw/otbn/code-snippets:randomness",
    ],
)

opentitan_functest(
    name = "otbn_rsa_test",
    srcs = ["otbn_rsa_test.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:otbn",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:otbn",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/otbn/crypto:rsa",
    ],
)

opentitan_functest(
    name = "otbn_smoketest",
    srcs = ["otbn_smoketest.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:otbn",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
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
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:otp_ctrl_testutils",
    ],
)

opentitan_functest(
    name = "plic_all_irqs_test",
    srcs = ["autogen/plic_all_irqs_test.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib:irq",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:adc_ctrl",
        "//sw/device/lib/dif:alert_handler",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:csrng",
        "//sw/device/lib/dif:edn",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:hmac",
        "//sw/device/lib/dif:i2c",
        "//sw/device/lib/dif:keymgr",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/dif:otbn",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/dif:pattgen",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:rv_timer",
        "//sw/device/lib/dif:spi_device",
        "//sw/device/lib/dif:spi_host",
        "//sw/device/lib/dif:sysrst_ctrl",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/dif:usbdev",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:rv_plic_testutils",
    ],
)

opentitan_functest(
    name = "pmp_smoketest_napot",
    srcs = ["pmp_smoketest_napot.c"],
    verilator = verilator_params(
        tags = [
            "cpu:4",
            "failing_verilator",
        ],
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib:irq",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:pmp",
    ],
)

opentitan_functest(
    name = "pmp_smoketest_tor",
    srcs = ["pmp_smoketest_tor.c"],
    verilator = verilator_params(
        tags = [
            "cpu:4",
            "failing_verilator",
        ],
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib:irq",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:pmp",
    ],
)

opentitan_functest(
    name = "pwrmgr_smoketest",
    srcs = ["pwrmgr_smoketest.c"],
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
    ],
)

opentitan_functest(
    name = "rstmgr_sw_rst_ctrl_test",
    srcs = ["rstmgr_sw_rst_ctrl_test.c"],
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
    ],
)

opentitan_functest(
    name = "rv_plic_smoketest",
    srcs = ["rv_plic_smoketest.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib:irq",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
    ],
)

opentitan_functest(
    name = "rv_timer_smoketest",
    srcs = ["rv_timer_smoketest.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib:irq",
        "//sw/device/lib/dif:rv_timer",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
    ],
)

opentitan_functest(
    name = "spi_host_smoketest",
    srcs = ["spi_host_smoketest.c"],
    targets = ["cw310"],  # Can only run on CW310 board right now.
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:spi_host",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
    ],
)

opentitan_functest(
    name = "sleep_pwm_pulses_test",
    srcs = ["sleep_pwm_pulses_test.c"],
    verilator = verilator_params(
        timeout = "long",
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
    ],
)

opentitan_functest(
    name = "sram_ctrl_execution_test_ret",
    srcs = ["sram_ctrl_execution_test_ret.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/dif:sram_ctrl",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:sram_ctrl_testutils",
    ],
)

opentitan_functest(
    name = "sram_ctrl_sleep_sram_ret_contents_test",
    srcs = ["sram_ctrl_sleep_sram_ret_contents_test.c"],
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
    ],
)

opentitan_functest(
    name = "usbdev_test",
    srcs = ["usbdev_test.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib:pinmux",
        "//sw/device/lib:usb",
        "//sw/device/lib:usb_simpleserial",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
    ],
)
