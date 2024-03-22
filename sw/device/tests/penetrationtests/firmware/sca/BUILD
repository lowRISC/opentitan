# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "aes_sca",
    srcs = ["aes_sca.c"],
    hdrs = ["aes_sca.h"],
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
        "//sw/device/tests/penetrationtests/firmware/lib:sca_lib",
        "//sw/device/tests/penetrationtests/json:aes_sca_commands",
    ],
)

cc_library(
    name = "ecc256_keygen_sca",
    srcs = ["ecc256_keygen_sca.c"],
    hdrs = ["ecc256_keygen_sca.h"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/sca/lib:prng",
        "//sw/device/sca/lib:sca",
        "//sw/device/tests/penetrationtests/json:otbn_sca_commands",
        "//sw/otbn/crypto:p256_key_from_seed_sca",
    ],
)

cc_library(
    name = "otbn_sca",
    srcs = ["otbn_sca.c"],
    hdrs = ["otbn_sca.h"],
    deps = [
        ":ecc256_keygen_sca",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/impl:status",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/sca/lib:prng",
        "//sw/device/sca/lib:sca",
        "//sw/device/tests/penetrationtests/firmware/lib:sca_lib",
        "//sw/device/tests/penetrationtests/json:otbn_sca_commands",
    ],
)

cc_library(
    name = "hmac_sca",
    srcs = ["hmac_sca.c"],
    hdrs = ["hmac_sca.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/impl:mac",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/sca/lib:prng",
        "//sw/device/sca/lib:sca",
        "//sw/device/tests/penetrationtests/firmware/lib:sca_lib",
        "//sw/device/tests/penetrationtests/json:hmac_sca_commands",
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
        "//sw/device/sca/lib:prng",
        "//sw/device/sca/lib:sca",
        "//sw/device/tests/penetrationtests/firmware/lib:sca_lib",
        "//sw/device/tests/penetrationtests/json:ibex_sca_commands",
    ],
)

cc_library(
    name = "kmac_sca",
    srcs = ["kmac_sca.c"],
    hdrs = ["kmac_sca.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/sca/lib:prng",
        "//sw/device/sca/lib:sca",
        "//sw/device/tests/penetrationtests/firmware/lib:sca_lib",
        "//sw/device/tests/penetrationtests/json:kmac_sca_commands",
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
        "//sw/device/tests/penetrationtests/json:prng_sca_commands",
    ],
)

cc_library(
    name = "sha3_sca",
    srcs = ["sha3_sca.c"],
    hdrs = ["sha3_sca.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/sca/lib:prng",
        "//sw/device/sca/lib:sca",
        "//sw/device/tests/penetrationtests/firmware/lib:sca_lib",
        "//sw/device/tests/penetrationtests/json:sha3_sca_commands",
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
        "//sw/device/tests/penetrationtests/json:trigger_sca_commands",
    ],
)
