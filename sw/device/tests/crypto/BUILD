# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "@bazel_skylib//lib:dicts.bzl",
    "dicts",
)
load("//rules:autogen.bzl", "autogen_cryptotest_header")
load(
    "//rules/opentitan:defs.bzl",
    "EARLGREY_SILICON_OWNER_ROM_EXT_ENVS",
    "EARLGREY_TEST_ENVS",
    "cw310_params",
    "fpga_params",
    "opentitan_test",
    "silicon_params",
    "verilator_params",
)
load(
    "@bazel_skylib//lib:dicts.bzl",
    "dicts",
)
load("@ot_python_deps//:requirements.bzl", "requirement")

package(default_visibility = ["//visibility:public"])

CRYPTOTEST_EXEC_ENVS = dicts.add(
    EARLGREY_TEST_ENVS,
    EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
)

opentitan_test(
    name = "aes_functest",
    srcs = ["aes_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        ":aes_testvectors",
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "aes_kwp_kat_functest",
    srcs = ["aes_kwp_kat_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/crypto/impl/aes_kwp",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "aes_kwp_functest",
    srcs = ["aes_kwp_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/crypto/impl:aes",
        "//sw/device/lib/crypto/impl:key_transport",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "aes_kwp_sideload_functest",
    srcs = ["aes_kwp_sideload_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/crypto/impl:aes",
        "//sw/device/lib/crypto/impl:key_transport",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "aes_sideload_functest",
    srcs = ["aes_sideload_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/crypto/drivers:aes",
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/crypto/drivers:keymgr",
        "//sw/device/lib/crypto/impl:aes",
        "//sw/device/lib/crypto/impl:key_transport",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

cc_library(
    name = "aes_testvectors",
    srcs = ["aes_testvectors.h"],
    deps = [
        "//sw/device/lib/crypto/impl:aes",
    ],
)

opentitan_test(
    name = "aes_gcm_functest",
    srcs = ["aes_gcm_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "eternal",
    ),
    deps = [
        ":aes_gcm_testutils",
        ":aes_gcm_testvectors",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

cc_library(
    name = "aes_gcm_testutils",
    srcs = ["aes_gcm_testutils.c"],
    hdrs = ["aes_gcm_testutils.h"],
    deps = [
        "//sw/device/lib/crypto/impl:aes",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing/test_framework:check",
    ],
)

cc_library(
    name = "aes_gcm_testvectors",
    srcs = ["aes_gcm_testvectors.h"],
    deps = [
        ":aes_gcm_testutils",
    ],
)

opentitan_test(
    name = "aes_gcm_timing_test",
    srcs = ["aes_gcm_timing_test.c"],
    exec_env = EARLGREY_TEST_ENVS,
    fpga = fpga_params(
        timeout = "long",
        tags = ["broken"],  # https://github.com/lowRISC/opentitan/issues/15788
        # [test-triage] test not constant time with icache enabled
    ),
    verilator = verilator_params(
        timeout = "long",
        tags = ["broken"],  # https://github.com/lowRISC/opentitan/issues/15788
        # [test-triage] test not constant time with icache enabled
    ),
    deps = [
        ":aes_gcm_testutils",
        ":aes_gcm_testvectors",
        "//sw/device/lib/crypto/impl/aes_gcm",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "drbg_functest",
    srcs = ["drbg_functest.c"],
    exec_env = EARLGREY_TEST_ENVS,
    verilator = verilator_params(
        timeout = "eternal",
    ),
    deps = [
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/crypto/impl:drbg",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:randomness_quality",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "ecdh_p256_functest",
    srcs = ["ecdh_p256_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "eternal",
    ),
    deps = [
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/impl:ecc",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "ecdh_p384_functest",
    srcs = ["ecdh_p384_functest.c"],
    exec_env = EARLGREY_TEST_ENVS,
    verilator = verilator_params(
        timeout = "eternal",
    ),
    deps = [
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/impl:ecc",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "ecdh_p256_sideload_functest",
    srcs = ["ecdh_p256_sideload_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "eternal",
    ),
    deps = [
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/impl:ecc",
        "//sw/device/lib/crypto/impl:key_transport",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "ecdh_p384_sideload_functest",
    srcs = ["ecdh_p384_sideload_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "eternal",
    ),
    deps = [
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/impl:ecc",
        "//sw/device/lib/crypto/impl:key_transport",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "ecdsa_p256_functest",
    srcs = ["ecdsa_p256_functest.c"],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            # Test is too large for ROM, so excluding rom_with_fake_keys.
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:fpga_cw310_test_rom": None,
            "//hw/top_earlgrey:sim_dv": None,
            "//hw/top_earlgrey:sim_verilator": None,
        },
    ),
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/impl:ecc",
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "ecdsa_p384_functest",
    srcs = ["ecdsa_p384_functest.c"],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            # Test is too large for ROM, so excluding rom_with_fake_keys.
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
            "//hw/top_earlgrey:fpga_cw310_test_rom": None,
            "//hw/top_earlgrey:sim_dv": None,
            "//hw/top_earlgrey:sim_verilator": None,
        },
    ),
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/impl:ecc",
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "ecdsa_p256_sideload_functest",
    srcs = ["ecdsa_p256_sideload_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "eternal",
    ),
    deps = [
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/crypto/drivers:keymgr",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/impl:ecc",
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/crypto/impl:key_transport",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "ecdsa_p384_sideload_functest",
    srcs = ["ecdsa_p384_sideload_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "eternal",
    ),
    deps = [
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/crypto/drivers:keymgr",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/impl:ecc",
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/crypto/impl:key_transport",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

autogen_cryptotest_header(
    name = "ecdsa_p256_verify_testvectors_hardcoded_header",
    hjson = "//sw/device/tests/crypto/testvectors:ecdsa_p256_verify_testvectors_hardcoded",
    template = ":ecdsa_p256_verify_testvectors.h.tpl",
    tool = "//sw/device/tests/crypto:ecdsa_p256_verify_set_testvectors",
)

autogen_cryptotest_header(
    name = "kmac_testvectors_hardcoded_header",
    hjson = "//sw/device/tests/crypto/testvectors:kmac_testvectors_hardcoded",
    template = ":kmac_testvectors.h.tpl",
    tool = "//sw/device/tests/crypto:kmac_set_testvectors",
)

autogen_cryptotest_header(
    name = "kdf_testvectors_random_header",
    hjson = "//sw/device/tests/crypto/testvectors:kdf_testvectors_random",
    template = ":kdf_testvectors.h.tpl",
    tool = "//sw/device/tests/crypto:kdf_set_testvectors",
)

autogen_cryptotest_header(
    name = "hmac_testvectors_random_header",
    hjson = "//sw/device/tests/crypto/testvectors:hmac_testvectors_random",
    template = ":hmac_testvectors.h.tpl",
    tool = "//sw/device/tests/crypto:hmac_set_testvectors",
)

opentitan_test(
    name = "kmac_functest_hardcoded",
    srcs = ["kmac_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        ":kmac_testvectors_hardcoded_header",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/crypto/drivers:kmac",
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:mac",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "kdf_hmac_ctr_functest",
    srcs = ["kdf_hmac_ctr_functest.c"],
    exec_env = EARLGREY_TEST_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/crypto/impl:kdf",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "kdf_kmac_functest",
    srcs = ["kdf_kmac_functest.c"],
    exec_env = EARLGREY_TEST_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        ":kdf_testvectors_random_header",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/crypto/drivers:kmac",
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/crypto/impl:kdf",
        "//sw/device/lib/crypto/impl:mac",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "hmac_functest",
    srcs = ["hmac_functest.c"],
    exec_env = EARLGREY_TEST_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        ":hmac_testvectors_random_header",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/crypto/impl:mac",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "hmac_multistream_functest",
    srcs = ["hmac_multistream_functest.c"],
    exec_env = EARLGREY_TEST_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        ":hmac_testvectors_random_header",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/crypto/impl:mac",
        "//sw/device/lib/testing:rand_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "kdf_kmac_sideload_functest_hardcoded",
    srcs = ["kdf_kmac_sideload_functest.c"],
    broken = fpga_params(tags = ["broken"]),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        {
            # FIXME broken in sival ROM_EXT, remove this line when fixed. See #21706.
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": "broken",
        },
    ),
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/base:macros",
        "//sw/device/lib/crypto/drivers:kmac",
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/crypto/impl:kdf",
        "//sw/device/lib/crypto/impl:mac",
        "//sw/device/lib/dif:keymgr",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "kmac_sideload_functest_hardcoded",
    srcs = ["kmac_sideload_functest.c"],
    broken = fpga_params(tags = ["broken"]),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        {
            # FIXME broken in sival ROM_EXT, remove this line when fixed. See #21706.
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": "broken",
        },
    ),
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/base:macros",
        "//sw/device/lib/crypto/drivers:kmac",
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:mac",
        "//sw/device/lib/dif:keymgr",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "ecdsa_p256_verify_functest_hardcoded",
    srcs = ["ecdsa_p256_verify_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        ":ecdsa_p256_verify_testvectors_hardcoded_header",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/crypto/impl/ecc:ecdsa_p256",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "rsa_2048_encryption_functest",
    srcs = ["rsa_2048_encryption_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "eternal",
    ),
    deps = [
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/crypto/impl:rsa",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "rsa_3072_encryption_functest",
    srcs = ["rsa_3072_encryption_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "eternal",
    ),
    deps = [
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/crypto/impl:rsa",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "rsa_4096_encryption_functest",
    srcs = ["rsa_4096_encryption_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "eternal",
    ),
    deps = [
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/crypto/impl:rsa",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "rsa_2048_key_from_cofactor_functest",
    srcs = ["rsa_2048_key_from_cofactor_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/crypto/impl:rsa",
        "//sw/device/lib/crypto/impl/rsa:rsa_datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "rsa_2048_keygen_functest",
    srcs = ["rsa_2048_keygen_functest.c"],
    # This test is too slow for Verilator/DV, so target FPGA only.
    exec_env = CRYPTOTEST_EXEC_ENVS,
    fpga = fpga_params(
        timeout = "long",
    ),
    verilator = verilator_params(
        timeout = "eternal",
    ),
    deps = [
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/crypto/impl:rsa",
        "//sw/device/lib/crypto/impl/rsa:rsa_datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "rsa_2048_signature_functest",
    srcs = ["rsa_2048_signature_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "eternal",
    ),
    deps = [
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:rsa",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "rsa_3072_keygen_functest",
    srcs = ["rsa_3072_keygen_functest.c"],
    # This test is too slow for Verilator/DV, so target FPGA only.
    exec_env = CRYPTOTEST_EXEC_ENVS,
    fpga = fpga_params(
        timeout = "long",
    ),
    silicon = silicon_params(
        timeout = "long",
    ),
    verilator = verilator_params(
        timeout = "eternal",
        tags = ["manual"],
    ),
    deps = [
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/crypto/impl:rsa",
        "//sw/device/lib/crypto/impl/rsa:rsa_datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "rsa_3072_signature_functest",
    srcs = ["rsa_3072_signature_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "eternal",
        tags = ["manual"],
    ),
    deps = [
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:rsa",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "rsa_4096_keygen_functest",
    srcs = ["rsa_4096_keygen_functest.c"],
    # This test is too slow for Verilator/DV, so target FPGA only.
    exec_env = CRYPTOTEST_EXEC_ENVS,
    fpga = fpga_params(
        timeout = "long",
    ),
    silicon = silicon_params(
        timeout = "long",
    ),
    verilator = verilator_params(
        timeout = "eternal",
        tags = ["manual"],
    ),
    deps = [
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/crypto/impl:rsa",
        "//sw/device/lib/crypto/impl/rsa:rsa_datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:entropy_testutils",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "rsa_4096_signature_functest",
    srcs = ["rsa_4096_signature_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "eternal",
        tags = ["manual"],
    ),
    deps = [
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:rsa",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

autogen_cryptotest_header(
    name = "rsa_3072_verify_testvectors_wycheproof_header",
    hjson = "//sw/device/tests/crypto/testvectors:rsa_3072_verify_testvectors_wycheproof",
    template = ":rsa_3072_verify_testvectors.h.tpl",
    tool = "//sw/device/tests/crypto:rsa_3072_verify_set_testvectors",
)

opentitan_test(
    name = "rsa_3072_verify_functest_wycheproof",
    srcs = ["rsa_3072_verify_functest.c"],
    # The test vectors don't fit in the flash allocated for ROM_EXT stage, so
    # we have to restrict the environments to run with the test_rom.
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_test_rom": None,
            "//hw/top_earlgrey:sim_verilator": None,
        },
    ),
    fpga = fpga_params(
        timeout = "moderate",
    ),
    verilator = verilator_params(
        timeout = "eternal",
    ),
    deps = [
        ":rsa_3072_verify_testvectors_wycheproof_header",
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/crypto/drivers:hmac",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/impl/rsa:rsa_3072_verify",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

autogen_cryptotest_header(
    name = "rsa_3072_verify_testvectors_hardcoded_header",
    hjson = "//sw/device/tests/crypto/testvectors:rsa_3072_verify_testvectors_hardcoded",
    template = ":rsa_3072_verify_testvectors.h.tpl",
    tool = "//sw/device/tests/crypto:rsa_3072_verify_set_testvectors",
)

opentitan_test(
    name = "rsa_3072_verify_functest_hardcoded",
    srcs = ["rsa_3072_verify_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        ":rsa_3072_verify_testvectors_hardcoded_header",
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/crypto/impl/rsa:rsa_3072_verify",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "sha384_functest",
    srcs = ["sha384_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "sha512_functest",
    srcs = ["sha512_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/crypto/impl:status",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "symmetric_keygen_functest",
    srcs = ["symmetric_keygen_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    deps = [
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/crypto/impl:drbg",
        "//sw/device/lib/crypto/impl:key_transport",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/impl:status",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:randomness_quality",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

py_binary(
    name = "ecdsa_p256_verify_set_testvectors",
    srcs = ["ecdsa_p256_verify_set_testvectors.py"],
    imports = ["."],
    deps = [
        "//util/design/lib:common",
        requirement("hjson"),
        requirement("mako"),
    ],
)

opentitan_test(
    name = "hkdf_functest",
    srcs = ["hkdf_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/crypto/impl:kdf",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "hmac_sha256_functest",
    srcs = ["hmac_sha256_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/crypto/drivers:hmac",
        "//sw/device/lib/crypto/impl:mac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "hmac_sha384_functest",
    srcs = ["hmac_sha384_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/crypto/impl:mac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "hmac_sha512_functest",
    srcs = ["hmac_sha512_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/crypto/impl:mac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

py_binary(
    name = "rsa_3072_verify_set_testvectors",
    srcs = ["rsa_3072_verify_set_testvectors.py"],
    imports = ["."],
    deps = [
        "//util/design/lib:common",
        requirement("hjson"),
        requirement("mako"),
    ],
)

py_binary(
    name = "kdf_set_testvectors",
    srcs = ["kdf_set_testvectors.py"],
    imports = ["."],
    deps = [
        "//util/design/lib:common",
        requirement("hjson"),
        requirement("mako"),
    ],
)

py_binary(
    name = "kmac_set_testvectors",
    srcs = ["kmac_set_testvectors.py"],
    imports = ["."],
    deps = [
        "//util/design/lib:common",
        requirement("hjson"),
        requirement("mako"),
    ],
)

py_binary(
    name = "hmac_set_testvectors",
    srcs = ["hmac_set_testvectors.py"],
    imports = ["."],
    deps = [
        "//util/design/lib:common",
        requirement("hjson"),
        requirement("mako"),
    ],
)

opentitan_test(
    name = "sha256_functest",
    srcs = ["sha256_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/crypto/drivers:hmac",
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "otcrypto_hash_test",
    srcs = ["otcrypto_hash_test.c"],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
        },
    ),
    deps = [
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "otcrypto_export_test",
    srcs = ["otcrypto_export_test.c"],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
        },
    ),
    deps = [
        "//sw/device/lib/crypto:crypto_exported_for_test",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

filegroup(
    name = "template_files",
    srcs = [
        "ecdsa_p256_verify_testvectors.h.tpl",
        "rsa_3072_verify_testvectors.h.tpl",
    ],
)

test_suite(
    name = "cryptolib_test_suite",
    tests = [
        ":aes_functest",
        ":aes_gcm_functest",
        ":aes_gcm_timing_test",
        ":aes_kwp_functest",
        ":aes_kwp_kat_functest",
        ":aes_kwp_sideload_functest",
        ":aes_sideload_functest",
        ":drbg_functest",
        ":ecdh_p256_functest",
        ":ecdh_p256_sideload_functest",
        ":ecdsa_p256_functest",
        ":ecdsa_p256_sideload_functest",
        ":ecdsa_p256_verify_functest_hardcoded",
        ":hkdf_functest",
        ":hmac_sha256_functest",
        ":hmac_sha384_functest",
        ":hmac_sha512_functest",
        ":otcrypto_export_test",
        ":otcrypto_hash_test",
        ":rsa_2048_encryption_functest",
        ":rsa_2048_key_from_cofactor_functest",
        ":rsa_2048_keygen_functest",
        ":rsa_2048_signature_functest",
        ":rsa_3072_encryption_functest",
        ":rsa_3072_keygen_functest",
        ":rsa_3072_signature_functest",
        ":rsa_3072_verify_functest_hardcoded",
        ":rsa_3072_verify_functest_wycheproof",
        ":rsa_4096_encryption_functest",
        ":rsa_4096_keygen_functest",
        ":rsa_4096_signature_functest",
        ":sha256_functest",
        ":sha384_functest",
        ":sha512_functest",
        ":symmetric_keygen_functest",
    ],
)
