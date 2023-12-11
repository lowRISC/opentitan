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
        "//sw/device/tests:aon_timer_irq_test",
        "//sw/device/tests:csrng_edn_concurrency_test",
        "//sw/device/tests:entropy_src_csrng_test",
        "//sw/device/tests:hmac_smoketest",
        "//sw/device/tests:kmac_smoketest",
        "//sw/device/tests:power_virus_systemtest",
        "//sw/device/tests:pwrmgr_smoketest",
    ],
)
