# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load(
    "//rules/opentitan:defs.bzl",
    "opentitan_binary",
    "opentitan_test",
    "silicon_params",
)

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "aes",
    srcs = ["aes.c"],
    hdrs = ["aes.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/impl:aes",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/tests/crypto/cryptotest/json:aes_commands",
    ],
)

cc_library(
    name = "ecdsa",
    srcs = ["ecdsa.c"],
    hdrs = ["ecdsa.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/impl:ecc",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/impl/ecc:ecdsa_p256",
        "//sw/device/lib/crypto/impl/ecc:p256_common",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/tests/crypto/cryptotest/json:ecdsa_commands",
    ],
)

cc_library(
    name = "ecdh",
    srcs = ["ecdh.c"],
    hdrs = ["ecdh.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/impl:ecc",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/tests/crypto/cryptotest/json:ecdh_commands",
    ],
)

cc_library(
    name = "drbg",
    srcs = ["drbg.c"],
    hdrs = ["drbg.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/crypto/impl:drbg",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/tests/crypto/cryptotest/json:drbg_commands",
    ],
)

cc_library(
    name = "hash",
    srcs = ["hash.c"],
    hdrs = ["hash.h"],
    deps = [
        "//sw/device/lib/base:math",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/drivers:kmac",
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/tests/crypto/cryptotest/json:hash_commands",
    ],
)

cc_library(
    name = "hmac",
    srcs = ["hmac.c"],
    hdrs = ["hmac.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/impl:mac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/tests/crypto/cryptotest/json:hmac_commands",
    ],
)

cc_library(
    name = "sphincsplus",
    srcs = ["sphincsplus.c"],
    hdrs = ["sphincsplus.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:verify",
        "//sw/device/tests/crypto/cryptotest/json:sphincsplus_commands",
    ],
)

cc_library(
    name = "kmac",
    srcs = ["kmac.c"],
    hdrs = ["kmac.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/impl:mac",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/tests/crypto/cryptotest/json:kmac_commands",
    ],
)

cc_library(
    name = "aes_sca",
    srcs = ["aes_sca.c"],
    hdrs = [
        "aes_sca.h",
        "status.h",
    ],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:aes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:aes_testutils",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/sca/lib:aes",
        "//sw/device/sca/lib:prng",
        "//sw/device/sca/lib:sca",
        "//sw/device/tests/crypto/cryptotest/firmware:sca_lib",
        "//sw/device/tests/crypto/cryptotest/json:aes_sca_commands",
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
        "//sw/device/tests/crypto/cryptotest/firmware:sca_lib",
        "//sw/device/tests/crypto/cryptotest/json:ibex_fi_commands",
    ],
)

cc_library(
    name = "ibex_sca",
    srcs = ["ibex_sca.c"],
    hdrs = ["ibex_sca.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:keymgr",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/sca/lib:sca",
        "//sw/device/tests/crypto/cryptotest/firmware:sca_lib",
        "//sw/device/tests/crypto/cryptotest/json:ibex_sca_commands",
    ],
)

cc_library(
    name = "extclk_sca_fi",
    srcs = ["extclk_sca_fi.c"],
    hdrs = ["extclk_sca_fi.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/tests/crypto/cryptotest/json:extclk_sca_fi_commands",
    ],
)

cc_library(
    name = "kmac_sca",
    srcs = ["kmac_sca.c"],
    hdrs = [
        "kmac_sca.h",
        "status.h",
    ],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/sca/lib:prng",
        "//sw/device/sca/lib:sca",
        "//sw/device/tests/crypto/cryptotest/firmware:sca_lib",
        "//sw/device/tests/crypto/cryptotest/json:kmac_sca_commands",
    ],
)

cc_library(
    name = "otbn_fi",
    srcs = ["otbn_fi.c"],
    hdrs = [
        "otbn_fi.h",
        "status.h",
    ],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/dif:otbn",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/sca/lib:sca",
        "//sw/device/tests/crypto/cryptotest/firmware/otbn:otbn_char_hardware_dmem_op_loop",
        "//sw/device/tests/crypto/cryptotest/firmware/otbn:otbn_char_hardware_reg_op_loop",
        "//sw/device/tests/crypto/cryptotest/firmware/otbn:otbn_char_unrolled_dmem_op_loop",
        "//sw/device/tests/crypto/cryptotest/firmware/otbn:otbn_char_unrolled_reg_op_loop",
        "//sw/device/tests/crypto/cryptotest/json:otbn_fi_commands",
    ],
)

cc_library(
    name = "prng_sca",
    srcs = ["prng_sca.c"],
    hdrs = ["prng_sca.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/sca/lib:prng",
        "//sw/device/tests/crypto/cryptotest/json:prng_sca_commands",
    ],
)

cc_library(
    name = "sca_lib",
    srcs = ["sca_lib.c"],
    hdrs = ["sca_lib.h"],
    deps = [
        "//sw/device/lib/base:csr",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

cc_library(
    name = "sha3_sca",
    srcs = ["sha3_sca.c"],
    hdrs = [
        "sha3_sca.h",
        "status.h",
    ],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/sca/lib:prng",
        "//sw/device/sca/lib:sca",
        "//sw/device/tests/crypto/cryptotest/firmware:sca_lib",
        "//sw/device/tests/crypto/cryptotest/json:sha3_sca_commands",
    ],
)

cc_library(
    name = "trigger_sca",
    srcs = ["trigger_sca.c"],
    hdrs = ["trigger_sca.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/sca/lib:sca",
        "//sw/device/tests/crypto/cryptotest/json:trigger_sca_commands",
    ],
)

FIRMWARE_DEPS = [
    ":aes_sca",
    ":aes",
    ":drbg",
    ":ecdh",
    ":ecdsa",
    ":extclk_sca_fi",
    ":hash",
    ":hmac",
    ":ibex_fi",
    ":ibex_sca",
    ":kmac_sca",
    ":kmac",
    ":otbn_fi",
    ":prng_sca",
    ":sha3_sca",
    ":sphincsplus",
    ":trigger_sca",
    "//sw/device/lib/base:csr",
    "//sw/device/lib/base:status",
    "//sw/device/lib/crypto/drivers:entropy",
    "//sw/device/lib/testing/test_framework:check",
    "//sw/device/lib/testing/test_framework:ottf_main",
    "//sw/device/lib/testing/test_framework:ujson_ottf",
    "//sw/device/lib/ujson",

    # Include all JSON commands.
    "//sw/device/tests/crypto/cryptotest/json:commands",
]

[
    opentitan_binary(
        name = "firmware_{}".format(exec_env),
        testonly = True,
        srcs = [":firmware.c"],
        exec_env = [
            "//hw/top_earlgrey:{}".format(exec_env),
        ],
        deps = FIRMWARE_DEPS,
    )
    for exec_env in [
        "fpga_cw310_test_rom",
        "silicon_owner_sival_rom_ext",
        "silicon_owner_prodc_rom_ext",
    ]
]

opentitan_test(
    name = "chip_pen_test",
    srcs = [":firmware.c"],
    exec_env = {
        "//hw/top_earlgrey:silicon_owner_sival_rom_ext": "silicon_owner",
        "//hw/top_earlgrey:silicon_owner_prodc_rom_ext": "silicon_owner",
    },
    silicon_owner = silicon_params(
        tags = ["broken"],
    ),
    deps = FIRMWARE_DEPS,
)
