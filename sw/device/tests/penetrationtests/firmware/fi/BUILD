# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "crypto_fi",
    srcs = ["crypto_fi.c"],
    hdrs = ["crypto_fi.h"],
    deps = [
        "//hw/ip/aes/data:aes_c_regs",
        "//hw/ip/kmac/data:kmac_c_regs",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:aes",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/dif:rv_core_ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aes_testutils",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/sca/lib:sca",
        "//sw/device/tests/penetrationtests/firmware/lib:sca_lib",
        "//sw/device/tests/penetrationtests/json:crypto_fi_commands",
    ],
)

cc_library(
    name = "ibex_fi",
    srcs = [
        "ibex_fi.S",
        "ibex_fi.c",
    ],
    hdrs = ["ibex_fi.h"],
    deps = [
        "//sw/device/lib/base:csr",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:rv_core_ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/sca/lib:sca",
        "//sw/device/tests/penetrationtests/firmware/lib:sca_lib",
        "//sw/device/tests/penetrationtests/json:ibex_fi_commands",
    ],
)

cc_library(
    name = "otbn_fi",
    srcs = ["otbn_fi.c"],
    hdrs = ["otbn_fi.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/dif:otbn",
        "//sw/device/lib/dif:rv_core_ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/sca/lib:sca",
        "//sw/device/tests/penetrationtests/firmware/fi/otbn:otbn_char_hardware_dmem_op_loop",
        "//sw/device/tests/penetrationtests/firmware/fi/otbn:otbn_char_hardware_reg_op_loop",
        "//sw/device/tests/penetrationtests/firmware/fi/otbn:otbn_char_unrolled_dmem_op_loop",
        "//sw/device/tests/penetrationtests/firmware/fi/otbn:otbn_char_unrolled_reg_op_loop",
        "//sw/device/tests/penetrationtests/firmware/lib:sca_lib",
        "//sw/device/tests/penetrationtests/json:otbn_fi_commands",
    ],
)

cc_library(
    name = "rng_fi",
    srcs = ["rng_fi.c"],
    hdrs = ["rng_fi.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:csrng",
        "//sw/device/lib/dif:csrng_shared",
        "//sw/device/lib/dif:edn",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/dif:rv_core_ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:csrng_testutils",
        "//sw/device/lib/testing:edn_testutils",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:rv_core_ibex_testutils",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/sca/lib:sca",
        "//sw/device/tests/penetrationtests/firmware/lib:sca_lib",
        "//sw/device/tests/penetrationtests/json:rng_fi_commands",
    ],
)
