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
    "fpga_params",
    "opentitan_binary",
    "opentitan_test",
    "silicon_params",
    "verilator_params",
)
load("@ot_python_deps//:requirements.bzl", "requirement")
load("//rules/coverage:view.bzl", "coverage_view_test")

package(default_visibility = ["//visibility:public"])

CRYPTOTEST_EXEC_ENVS = dicts.add(
    EARLGREY_TEST_ENVS,
    EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    {
        "//hw/top_earlgrey:fpga_cw340_sival_rom_ext": None,
    },
)

cc_library(
    name = "otcrypto_interface",
    srcs = ["otcrypto_interface.c"],
    hdrs = ["otcrypto_interface.h"],
    deps = [
        "//sw/device/lib/crypto:crypto_exported_for_test",
    ],
)

opentitan_binary(
    name = "otcrypto_export_size",
    testonly = True,
    srcs = [
        "otcrypto_export_size.c",
        "//sw/device/silicon_owner/bare_metal:bare_metal_start",
    ],
    # Disable link-time optimization to preserve unused cryptolib functions.
    copts = ["-fno-lto"],
    exec_env = [
        "//hw/top_earlgrey:fpga_cw310_rom_ext",
        "//hw/top_earlgrey:silicon_creator",
    ],
    linker_script = "//sw/device/silicon_owner/bare_metal:ld_slot_a",
    manifest = "//sw/device/silicon_owner/bare_metal:manifest",
    deps = [
        ":otcrypto_interface",
        "//sw/device/lib/crt",
        "//sw/device/silicon_creator/lib:manifest_def",
    ],
)

# ------------------------------------------------------------------------------
# Coverage Generation for Cryptolib
# ------------------------------------------------------------------------------
# To run coverage manually, use the `ot_coverage` config.
#
# 1. Run Unit Tests
#    bazel coverage --config=ot_coverage --nocache_test_results --test_output=errors \
#        //sw/device/lib/crypto/impl:impl_unittest_suite \
#        //sw/device/lib/base:base_unittest_suite \
#        //sw/device/tests/crypto:otcrypto_coverage_view \
#    bash ci/scripts/collect-coverage-report.sh /path/to/collect/dir/<name-a>
#
#
# 2. Run Device Tests
#    Note: This requires the Google A1 silicon provisioning git repository to be
#    available (PROV_EXTS_DIR). To run on FPGA instead, drop the two `--//signing`
#    flags and swap the suffix below to `fpga_cw340_sival_rom_ext`.
#    Note that the CW340 can provide garbled outputs during the KATs due to SPI
#    flakiness, hence why the silicon version is shown instead.
#
#    bazel coverage \
#        --//signing:token=@provisioning_exts//shared/tokens:cloud_kms_gb \
#        --//signing:appkey=@provisioning_exts//shared/rom_ext/gb/keys:keyset \
#        --config=ot_coverage --nocache_test_results --test_output=errors \
#        --test_arg=--timeout --test_arg=100s \
#        //sw/device/tests/crypto/cryptotest:crypto_kat_test_suite_silicon_owner_gb_rom_ext \
#        //sw/device/lib/base:base_functest_suite_silicon_owner_gb_rom_ext \
#        //sw/device/lib/crypto/drivers:drivers_test_suite_silicon_owner_gb_rom_ext \
#        //sw/device/tests/crypto:cryptolib_test_suite_silicon_owner_gb_rom_ext \
#        //sw/device/tests/crypto:cryptolib_keygen_test_suite_silicon_owner_gb_rom_ext \
#        //sw/device/tests/crypto:otcrypto_coverage_view
#   bash ci/scripts/collect-coverage-report.sh /path/to/collect/dir/<name-b>
#
# 3. Run OTBN Tests
#   bazel coverage --config=ot_coverage --nocache_test_results --test_output=errors \
#        //sw/otbn/crypto:cryptolib_coverage_view \
#        //sw/otbn/crypto/tests:cryptolib_sim_test_suite
#   bash ci/scripts/collect-coverage-report.sh /path/to/collect/dir/<name-c>
#
# 4. Collect and Bundle Viewer (available at /path/to/report/dir/viewer/index.html)
#    bash ci/scripts/merge-coverage-report.sh /path/to/collect/dir/ /path/to/report/dir/
# ------------------------------------------------------------------------------
coverage_view_test(
    name = "otcrypto_coverage_view",
    elf = "otcrypto_export_size",
)

opentitan_test(
    name = "aes_functest",
    srcs = ["aes_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
        # This test can take > 60 minutes, so mark it manual as it shouldn't
        # run in CI/nightlies.
        tags = ["manual"],
    ),
    deps = [
        ":aes_testvectors",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:entropy_src",
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
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:entropy_src",
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
        "//sw/device/lib/crypto/impl:aes",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:integrity",
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
        "//sw/device/lib/crypto/impl:aes",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:integrity",
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
        "//sw/device/lib/crypto/drivers:keymgr",
        "//sw/device/lib/crypto/impl:aes",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:entropy_src",
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
        # This test can take > 60 minutes, so mark it manual as it shouldn't
        # run in CI/nightlies.
        tags = ["manual"],
    ),
    deps = [
        ":aes_gcm_testutils",
        ":aes_gcm_testvectors",
        "//sw/device/lib/crypto/impl:aes_gcm",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:status",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

cc_library(
    name = "aes_gcm_testutils",
    srcs = ["aes_gcm_testutils.c"],
    hdrs = ["aes_gcm_testutils.h"],
    deps = [
        "//sw/device/lib/crypto/impl:aes_gcm",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/tests/crypto/lib:crypto_test_lib",
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
    name = "aes_gcm_timing_functest",
    srcs = ["aes_gcm_timing_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
        tags = ["broken"],
    ),
    deps = [
        ":aes_gcm_testvectors",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl/aes_gcm",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "ecc_p256_dice_functest",
    srcs = ["ecc_p256_dice_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "eternal",
    ),
    deps = [
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/crypto/drivers:keymgr",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:ecc_p256",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:key_transport",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/impl:status",
        "//sw/device/lib/crypto/impl/ecc:p256",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:hexstr",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/base:util",
        "//sw/device/silicon_creator/lib/cert:dice_keys",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/manuf/base:perso_tlv_data",
        "//sw/device/silicon_creator/manuf/lib:flash_info_fields",
    ],
)

opentitan_test(
    name = "config_functest",
    srcs = ["config_functest.c"],
    # This test does not work on cw310 since it does not connect the jittery clock
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw340_sival_rom_ext": None,
        },
    ),
    verilator = verilator_params(
        timeout = "eternal",
    ),
    deps = [
        "//hw/ip/aes/data:aes_c_regs",
        "//hw/ip/rv_core_ibex/data:rv_core_ibex_c_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:status",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:irq",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:randomness_quality",
        "//sw/device/lib/testing/test_framework:ottf_alerts",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "drbg_functest",
    srcs = ["drbg_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "eternal",
    ),
    deps = [
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:drbg",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:status",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:randomness_quality",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "ecc_p256_point_on_curve_check_functest",
    srcs = ["ecc_p256_point_on_curve_check_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:ecc_p256",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "ecc_p256_key_import_export_functest",
    srcs = ["ecc_p256_key_import_export_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:ecc_p256",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/impl:sha2",
        "//sw/device/lib/crypto/impl/ecc:p256",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "ecc_p256_base_point_mult_functest",
    srcs = ["ecc_p256_base_point_mult_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:ecc_p256",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/impl:sha2",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "ecc_p256_arith_share_private_key_functest",
    srcs = ["ecc_p256_arith_share_private_key_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:drbg",
        "//sw/device/lib/crypto/impl:ecc_p256",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/impl:sha2",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "ecc_p384_point_on_curve_check_functest",
    srcs = ["ecc_p384_point_on_curve_check_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:ecc_p384",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "ecc_p384_key_import_export_functest",
    srcs = ["ecc_p384_key_import_export_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:ecc_p384",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/impl:sha2",
        "//sw/device/lib/crypto/impl/ecc:p384",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "ecc_p384_base_point_mult_functest",
    srcs = ["ecc_p384_base_point_mult_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:ecc_p384",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "ecc_p384_arith_share_private_key_functest",
    srcs = ["ecc_p384_arith_share_private_key_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:drbg",
        "//sw/device/lib/crypto/impl:ecc_p384",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/impl:sha2",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:entropy_testutils",
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
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:ecc_p256",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:key_transport",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "ecdh_p384_functest",
    srcs = ["ecdh_p384_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "eternal",
        # This test can take > 60 minutes, so mark it manual as it shouldn't
        # run in CI/nightlies.
        tags = ["manual"],
    ),
    deps = [
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:ecc_p384",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:key_transport",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "ecdh_p256_sideload_functest",
    srcs = ["ecdh_p256_sideload_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "eternal",
        # This test can take > 60 minutes, so mark it manual as it shouldn't
        # run in CI/nightlies.
        tags = ["manual"],
    ),
    deps = [
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:ecc_p256",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:key_transport",
        "//sw/device/lib/runtime:log",
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
        # This test can take > 60 minutes, so mark it manual as it shouldn't
        # run in CI/nightlies.
        tags = ["manual"],
    ),
    deps = [
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:ecc_p384",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:key_transport",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "ecdsa_p256_functest",
    srcs = ["ecdsa_p256_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:ecc_p256",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/impl:sha2",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "ecdsa_p384_functest",
    srcs = ["ecdsa_p384_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
        # This test can take > 60 minutes, so mark it manual as it shouldn't
        # run in CI/nightlies.
        tags = ["manual"],
    ),
    deps = [
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:ecc_p384",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/impl:sha2",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "ecdsa_p256_sideload_functest",
    srcs = ["ecdsa_p256_sideload_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "eternal",
        # This test can take > 60 minutes, so mark it manual as it shouldn't
        # run in CI/nightlies.
        tags = ["manual"],
    ),
    deps = [
        "//sw/device/lib/crypto/drivers:keymgr",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:ecc_p256",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:key_transport",
        "//sw/device/lib/crypto/impl:sha2",
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
        # This test can take > 60 minutes, so mark it manual as it shouldn't
        # run in CI/nightlies.
        tags = ["manual"],
    ),
    deps = [
        "//sw/device/lib/crypto/drivers:keymgr",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:ecc_p384",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:key_transport",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/impl:sha2",
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

opentitan_test(
    name = "ed25519_functest",
    srcs = ["ed25519_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "eternal",
        # This test can take > 60 minutes, so mark it manual as it shouldn't
        # run in CI/nightlies.
        tags = ["manual"],
    ),
    deps = [
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/crypto/drivers:otbn",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:ecc_curve25519",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/impl:sha2",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "entropy_src_functest",
    srcs = ["entropy_src_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
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
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:kmac",
        "//sw/device/lib/crypto/impl:sha3",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "kdf_hmac_ctr_functest",
    srcs = ["kdf_hmac_ctr_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
        # This test can take > 60 minutes, so mark it manual as it shouldn't
        # run in CI/nightlies.
        tags = ["manual"],
    ),
    deps = [
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:kdf_ctr",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "kdf_kmac_functest",
    srcs = ["kdf_kmac_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
        # This test can take > 60 minutes, so mark it manual as it shouldn't
        # run in CI/nightlies.
        tags = ["manual"],
    ),
    deps = [
        ":kdf_testvectors_random_header",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/crypto/drivers:kmac",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:key_transport",
        "//sw/device/lib/crypto/impl:kmac",
        "//sw/device/lib/crypto/impl:kmac_kdf",
        "//sw/device/lib/crypto/impl:sha3",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "hmac_functest",
    srcs = ["hmac_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        ":hmac_testvectors_random_header",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:hmac",
        "//sw/device/lib/crypto/impl:sha2",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "hmac_multistream_functest",
    srcs = ["hmac_multistream_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
        # This test can take > 60 minutes, so mark it manual as it shouldn't
        # run in CI/nightlies.
        tags = ["manual"],
    ),
    deps = [
        ":hmac_testvectors_random_header",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:hmac",
        "//sw/device/lib/crypto/impl:sha2",
        "//sw/device/lib/testing:rand_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/tests/crypto/lib:crypto_test_lib",
    ],
)

opentitan_test(
    name = "kats_functest",
    srcs = ["kats_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:kats",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "kdf_kmac_sideload_functest_hardcoded",
    srcs = ["kdf_kmac_sideload_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/base:macros",
        "//sw/device/lib/crypto/drivers:kmac",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:key_transport",
        "//sw/device/lib/crypto/impl:kmac_kdf",
        "//sw/device/lib/crypto/impl:sha3",
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
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/base:macros",
        "//sw/device/lib/crypto/drivers:kmac",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:kmac",
        "//sw/device/lib/crypto/impl:sha3",
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
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:sha2",
        "//sw/device/lib/crypto/impl/ecc:p256",
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
        # This test can take > 60 minutes, so mark it manual as it shouldn't
        # run in CI/nightlies.
        tags = ["manual"],
    ),
    deps = [
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:rsa",
        "//sw/device/lib/crypto/impl:sha2",
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
        # This test can take > 60 minutes, so mark it manual as it shouldn't
        # run in CI/nightlies.
        tags = ["manual"],
    ),
    deps = [
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:rsa",
        "//sw/device/lib/crypto/impl:sha2",
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
        # This test can take > 60 minutes, so mark it manual as it shouldn't
        # run in CI/nightlies.
        tags = ["manual"],
    ),
    deps = [
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:rsa",
        "//sw/device/lib/crypto/impl:sha2",
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
        # This test can take > 60 minutes, so mark it manual as it shouldn't
        # run in CI/nightlies.
        tags = ["manual"],
    ),
    deps = [
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:rsa",
        "//sw/device/lib/crypto/impl:sha2",
        "//sw/device/lib/crypto/impl/rsa:rsa_datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "rsa_2048_keygen_functest",
    srcs = ["rsa_2048_keygen_functest.c"],
    # This test is slow, mark as manual.
    exec_env = CRYPTOTEST_EXEC_ENVS,
    fpga = fpga_params(
        timeout = "long",
        tags = ["manual"],
    ),
    verilator = verilator_params(
        timeout = "eternal",
        # This test can take > 60 minutes, so mark it manual as it shouldn't
        # run in CI/nightlies.
        tags = ["manual"],
    ),
    deps = [
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:rsa",
        "//sw/device/lib/crypto/impl:sha2",
        "//sw/device/lib/crypto/impl/rsa:rsa_datatypes",
        "//sw/device/lib/runtime:log",
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
        # This test can take > 60 minutes, so mark it manual as it shouldn't
        # run in CI/nightlies.
        tags = ["manual"],
    ),
    deps = [
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:rsa",
        "//sw/device/lib/crypto/impl:sha2",
        "//sw/device/lib/crypto/impl:sha3",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "rsa_3072_keygen_functest",
    srcs = ["rsa_3072_keygen_functest.c"],
    # This test is slow, mark as manual.
    exec_env = CRYPTOTEST_EXEC_ENVS,
    fpga = fpga_params(
        timeout = "long",
        tags = ["manual"],
    ),
    silicon = silicon_params(
        timeout = "long",
        tags = ["manual"],
    ),
    verilator = verilator_params(
        timeout = "eternal",
        tags = ["manual"],
    ),
    deps = [
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:rsa",
        "//sw/device/lib/crypto/impl:sha2",
        "//sw/device/lib/crypto/impl/rsa:rsa_datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "rsa_3072_key_from_cofactor_functest",
    srcs = ["rsa_3072_key_from_cofactor_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
        # This test can take > 60 minutes, so mark it manual as it shouldn't
        # run in CI/nightlies.
        tags = ["manual"],
    ),
    deps = [
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:rsa",
        "//sw/device/lib/crypto/impl:sha2",
        "//sw/device/lib/crypto/impl/rsa:rsa_datatypes",
        "//sw/device/lib/runtime:log",
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
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:rsa",
        "//sw/device/lib/crypto/impl:sha2",
        "//sw/device/lib/crypto/impl:sha3",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "rsa_4096_keygen_functest",
    srcs = ["rsa_4096_keygen_functest.c"],
    # This test is slow, mark as manual.
    exec_env = CRYPTOTEST_EXEC_ENVS,
    fpga = fpga_params(
        timeout = "long",
        tags = ["manual"],
    ),
    silicon = silicon_params(
        timeout = "long",
        tags = ["manual"],
    ),
    verilator = verilator_params(
        timeout = "eternal",
        tags = ["manual"],
    ),
    deps = [
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:rsa",
        "//sw/device/lib/crypto/impl:sha2",
        "//sw/device/lib/crypto/impl/rsa:rsa_datatypes",
        "//sw/device/lib/runtime:log",
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
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:rsa",
        "//sw/device/lib/crypto/impl:sha2",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "rsa_4096_key_from_cofactor_functest",
    srcs = ["rsa_4096_key_from_cofactor_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
        # This test can take > 60 minutes, so mark it manual as it shouldn't
        # run in CI/nightlies.
        tags = ["manual"],
    ),
    deps = [
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:rsa",
        "//sw/device/lib/crypto/impl:sha2",
        "//sw/device/lib/crypto/impl/rsa:rsa_datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:profile",
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
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:sha2",
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
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:sha2",
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
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:drbg",
        "//sw/device/lib/crypto/impl:entropy_src",
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
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:hkdf",
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
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:hmac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/tests/crypto/lib:crypto_test_lib",
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
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:hmac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/tests/crypto/lib:crypto_test_lib",
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
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:hmac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/tests/crypto/lib:crypto_test_lib",
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
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:entropy_src",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:sha2",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "otcrypto_hash_test",
    srcs = ["otcrypto_hash_test.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    deps = [
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "otcrypto_export_test",
    srcs = ["otcrypto_export_test.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    deps = [
        "//sw/device/lib/crypto:crypto_exported_for_test",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

filegroup(
    name = "template_files",
    srcs = [
        "ecdsa_p256_verify_testvectors.h.tpl",
    ],
)

opentitan_test(
    name = "status_functest",
    srcs = ["status_functest.c"],
    exec_env = CRYPTOTEST_EXEC_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:status",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

test_suite(
    name = "cryptolib_test_suite",
    tests = [
        ":aes_functest",
        ":aes_gcm_functest",
        ":aes_gcm_timing_functest",
        ":aes_kwp_functest",
        ":aes_kwp_kat_functest",
        ":aes_kwp_sideload_functest",
        ":aes_sideload_functest",
        ":config_functest",
        ":drbg_functest",
        ":ecc_p256_arith_share_private_key_functest",
        ":ecc_p256_base_point_mult_functest",
        ":ecc_p256_dice_functest",
        ":ecc_p256_key_import_export_functest",
        ":ecc_p256_point_on_curve_check_functest",
        ":ecc_p384_arith_share_private_key_functest",
        ":ecc_p384_base_point_mult_functest",
        ":ecc_p384_key_import_export_functest",
        ":ecc_p384_point_on_curve_check_functest",
        ":ecdh_p256_functest",
        ":ecdh_p256_sideload_functest",
        ":ecdh_p384_functest",
        ":ecdh_p384_sideload_functest",
        ":ecdsa_p256_functest",
        ":ecdsa_p256_sideload_functest",
        ":ecdsa_p256_verify_functest_hardcoded",
        ":ecdsa_p384_functest",
        ":ecdsa_p384_sideload_functest",
        ":ed25519_functest",
        ":entropy_src_functest",
        ":hkdf_functest",
        ":hmac_functest",
        ":hmac_multistream_functest",
        ":hmac_sha256_functest",
        ":hmac_sha384_functest",
        ":hmac_sha512_functest",
        ":kats_functest",
        ":kdf_hmac_ctr_functest",
        ":kdf_kmac_functest",
        ":kdf_kmac_sideload_functest_hardcoded",
        ":kmac_functest_hardcoded",
        ":kmac_sideload_functest_hardcoded",
        ":otcrypto_export_test",
        ":otcrypto_hash_test",
        ":rsa_2048_encryption_functest",
        ":rsa_2048_key_from_cofactor_functest",
        ":rsa_2048_signature_functest",
        ":rsa_3072_encryption_functest",
        ":rsa_3072_signature_functest",
        ":rsa_4096_encryption_functest",
        ":rsa_4096_signature_functest",
        ":sha256_functest",
        ":sha384_functest",
        ":sha512_functest",
        ":status_functest",
        ":symmetric_keygen_functest",
    ],
)

test_suite(
    name = "cryptolib_keygen_test_suite",
    tests = [
        ":rsa_2048_keygen_functest",
        ":rsa_3072_keygen_functest",
        ":rsa_4096_keygen_functest",
    ],
)
