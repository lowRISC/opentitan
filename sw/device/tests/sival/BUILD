# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# See sw/device/tests/doc/sival/README.md#running-test-suites for details on
# how to run SV test suites across execution environments.

test_suite(
    name = "sv1_tests",
    tests = [
        "//sw/device/tests:rstmgr_cpu_info_test",
        "//sw/device/tests:rv_core_ibex_rnd_test",
    ],
)

test_suite(
    name = "sv2_tests",
    tests = [
        "//sw/device/tests:aes_new_smoketest",
        "//sw/device/tests:alert_handler_lpg_clkoff_test",
        "//sw/device/tests:alert_handler_lpg_reset_toggle_test",
        "//sw/device/tests:aon_timer_irq_test",
        "//sw/device/tests:aon_timer_wdog_bite_reset_test",
        "//sw/device/tests:ast_clk_outs_test",
        "//sw/device/tests:csrng_edn_concurrency_test",
        "//sw/device/tests:entropy_src_csrng_test",
        "//sw/device/tests:hmac_smoketest",
        "//sw/device/tests:keymgr_key_derivation_test",
        "//sw/device/tests:kmac_smoketest",
        "//sw/device/tests:otbn_smoketest",
        "//sw/device/tests:pwrmgr_random_sleep_all_reset_reqs_test",
        "//sw/device/tests:pwrmgr_random_sleep_all_wake_ups",
        "//sw/device/tests:pwrmgr_smoketest",
        "//sw/device/tests:rstmgr_alert_info_test",
        "//sw/device/tests:rv_core_ibex_nmi_irq_test",
        "//sw/device/tests:spi_device_smoketest",
        "//sw/device/tests:sram_ctrl_sleep_sram_ret_contents_no_scramble_test",
        "//sw/device/tests:sram_ctrl_sleep_sram_ret_contents_scramble_test",
        "//sw/device/tests:uart0_tx_rx_test",
        "//sw/device/tests:uart1_tx_rx_test",
        "//sw/device/tests:uart2_tx_rx_test",
    ],
)

test_suite(
    name = "sv3_tests",
    tests = [
        "//sw/device/tests:keymgr_sideload_aes_test",
        "//sw/device/tests:keymgr_sideload_kmac_test",
        "//sw/device/tests:keymgr_sideload_otbn_simple_test",
        "//sw/device/tests:keymgr_sideload_otbn_test",
    ],
)
