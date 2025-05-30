# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:ujson.bzl", "ujson_rust")
load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library")

package(default_visibility = ["//visibility:public"])

ujson_rust(
    name = "commands_rust",
    srcs = ["//sw/device/tests/penetrationtests/json:commands"],
)

ujson_rust(
    name = "fi_crypto_commands_rust",
    srcs = ["//sw/device/tests/penetrationtests/json:crypto_fi_commands"],
)

ujson_rust(
    name = "fi_ibex_commands_rust",
    srcs = ["//sw/device/tests/penetrationtests/json:ibex_fi_commands"],
)

ujson_rust(
    name = "fi_lc_ctrl_commands_rust",
    srcs = ["//sw/device/tests/penetrationtests/json:lc_ctrl_fi_commands"],
)

ujson_rust(
    name = "fi_otbn_commands_rust",
    srcs = ["//sw/device/tests/penetrationtests/json:otbn_fi_commands"],
)

ujson_rust(
    name = "fi_otp_commands_rust",
    srcs = ["//sw/device/tests/penetrationtests/json:otp_fi_commands"],
)

ujson_rust(
    name = "fi_rng_commands_rust",
    srcs = ["//sw/device/tests/penetrationtests/json:rng_fi_commands"],
)

ujson_rust(
    name = "fi_rom_commands_rust",
    srcs = ["//sw/device/tests/penetrationtests/json:rom_fi_commands"],
)

ujson_rust(
    name = "pentest_lib_commands_rust",
    srcs = ["//sw/device/tests/penetrationtests/json:pentest_lib_commands"],
)

ujson_rust(
    name = "sca_aes_commands_rust",
    srcs = ["//sw/device/tests/penetrationtests/json:aes_sca_commands"],
)

ujson_rust(
    name = "sca_edn_commands_rust",
    srcs = ["//sw/device/tests/penetrationtests/json:edn_sca_commands"],
)

ujson_rust(
    name = "sca_hmac_commands_rust",
    srcs = ["//sw/device/tests/penetrationtests/json:hmac_sca_commands"],
)

ujson_rust(
    name = "sca_ibex_commands_rust",
    srcs = ["//sw/device/tests/penetrationtests/json:ibex_sca_commands"],
)

ujson_rust(
    name = "sca_kmac_commands_rust",
    srcs = ["//sw/device/tests/penetrationtests/json:kmac_sca_commands"],
)

ujson_rust(
    name = "sca_otbn_commands_rust",
    srcs = ["//sw/device/tests/penetrationtests/json:otbn_sca_commands"],
)

ujson_rust(
    name = "sca_sha3_commands_rust",
    srcs = ["//sw/device/tests/penetrationtests/json:sha3_sca_commands"],
)

rust_library(
    name = "pentest_commands",
    srcs = [
        "src/commands.rs",
        "src/fi_crypto_commands.rs",
        "src/fi_ibex_commands.rs",
        "src/fi_lc_ctrl_commands.rs",
        "src/fi_otbn_commands.rs",
        "src/fi_otp_commands.rs",
        "src/fi_rng_commands.rs",
        "src/fi_rom_commands.rs",
        "src/lib.rs",
        "src/pentest_lib_commands.rs",
        "src/sca_aes_commands.rs",
        "src/sca_edn_commands.rs",
        "src/sca_hmac_commands.rs",
        "src/sca_ibex_commands.rs",
        "src/sca_kmac_commands.rs",
        "src/sca_otbn_commands.rs",
        "src/sca_sha3_commands.rs",
    ],
    compile_data = [
        ":commands_rust",
        ":fi_crypto_commands_rust",
        ":fi_ibex_commands_rust",
        ":fi_lc_ctrl_commands_rust",
        ":fi_otbn_commands_rust",
        ":fi_otp_commands_rust",
        ":fi_rng_commands_rust",
        ":fi_rom_commands_rust",
        ":pentest_lib_commands_rust",
        ":sca_aes_commands_rust",
        ":sca_edn_commands_rust",
        ":sca_hmac_commands_rust",
        ":sca_ibex_commands_rust",
        ":sca_kmac_commands_rust",
        ":sca_otbn_commands_rust",
        ":sca_sha3_commands_rust",
    ],
    rustc_env = {
        "commands_loc": "$(execpath :commands_rust)",
        "fi_crypto_commands_loc": "$(execpath :fi_crypto_commands_rust)",
        "fi_ibex_commands_loc": "$(execpath :fi_ibex_commands_rust)",
        "fi_lc_ctrl_commands_loc": "$(execpath :fi_lc_ctrl_commands_rust)",
        "fi_otbn_commands_loc": "$(execpath :fi_otbn_commands_rust)",
        "fi_otp_commands_loc": "$(execpath :fi_otp_commands_rust)",
        "fi_rng_commands_loc": "$(execpath :fi_rng_commands_rust)",
        "fi_rom_commands_loc": "$(execpath :fi_rom_commands_rust)",
        "pentest_lib_commands_loc": "$(execpath :pentest_lib_commands_rust)",
        "sca_aes_commands_loc": "$(execpath :sca_aes_commands_rust)",
        "sca_edn_commands_loc": "$(execpath :sca_edn_commands_rust)",
        "sca_hmac_commands_loc": "$(execpath :sca_hmac_commands_rust)",
        "sca_ibex_commands_loc": "$(execpath :sca_ibex_commands_rust)",
        "sca_kmac_commands_loc": "$(execpath :sca_kmac_commands_rust)",
        "sca_otbn_commands_loc": "$(execpath :sca_otbn_commands_rust)",
        "sca_sha3_commands_loc": "$(execpath :sca_sha3_commands_rust)",
    },
    deps = [
        "//sw/host/opentitanlib",
        "@crate_index//:arrayvec",
        "@crate_index//:serde",
        "@crate_index//:strum",
    ],
)
