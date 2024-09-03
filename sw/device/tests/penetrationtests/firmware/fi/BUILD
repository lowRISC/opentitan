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
        "//sw/device/tests/penetrationtests/firmware/lib:pentest_lib",
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
        "//hw/ip/otp_ctrl/data:otp_ctrl_c_regs",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/dif:rv_core_ibex",
        "//sw/device/lib/dif:sram_ctrl",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing:sram_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/sca/lib:sca",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/manuf/lib:otp_fields",
        "//sw/device/tests/penetrationtests/firmware/lib:pentest_lib",
        "//sw/device/tests/penetrationtests/json:ibex_fi_commands",
    ],
)

cc_library(
    name = "lc_ctrl_fi",
    srcs = ["lc_ctrl_fi.c"],
    hdrs = ["lc_ctrl_fi.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:lc_ctrl",
        "//sw/device/lib/dif:rv_core_ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:rv_core_ibex_testutils",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/sca/lib:sca",
        "//sw/device/tests/penetrationtests/firmware/lib:pentest_lib",
        "//sw/device/tests/penetrationtests/json:lc_ctrl_fi_commands",
    ],
)

cc_library(
    name = "otbn_fi",
    srcs = ["otbn_fi.c"],
    hdrs = ["otbn_fi.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/drivers:keymgr",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/dif:otbn",
        "//sw/device/lib/dif:rv_core_ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/sca/lib:sca",
        "//sw/device/tests/penetrationtests/firmware/fi/otbn:otbn_char_hardware_dmem_op_loop",
        "//sw/device/tests/penetrationtests/firmware/fi/otbn:otbn_char_hardware_reg_op_loop",
        "//sw/device/tests/penetrationtests/firmware/fi/otbn:otbn_char_unrolled_dmem_op_loop",
        "//sw/device/tests/penetrationtests/firmware/fi/otbn:otbn_char_unrolled_reg_op_loop",
        "//sw/device/tests/penetrationtests/firmware/fi/otbn:otbn_key_sideload",
        "//sw/device/tests/penetrationtests/firmware/fi/otbn:otbn_load_integrity",
        "//sw/device/tests/penetrationtests/firmware/lib:pentest_lib",
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
        "//sw/device/tests/penetrationtests/firmware/lib:pentest_lib",
        "//sw/device/tests/penetrationtests/json:rng_fi_commands",
    ],
)

cc_library(
    name = "otp_fi",
    srcs = ["otp_fi.c"],
    hdrs = ["otp_fi.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/sca/lib:sca",
        "//sw/device/tests/penetrationtests/firmware/lib:pentest_lib",
        "//sw/device/tests/penetrationtests/json:otp_fi_commands",
    ],
)

cc_library(
    name = "rom_fi",
    srcs = ["rom_fi.c"],
    hdrs = ["rom_fi.h"],
    deps = [
        "//hw/ip/rom_ctrl/data:rom_ctrl_c_regs",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:rom_ctrl",
        "//sw/device/lib/dif:rv_core_ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/sca/lib:sca",
        "//sw/device/tests/penetrationtests/firmware/lib:pentest_lib",
        "//sw/device/tests/penetrationtests/json:rom_fi_commands",
    ],
)
