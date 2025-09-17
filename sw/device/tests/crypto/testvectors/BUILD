# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:autogen.bzl", "autogen_cryptotest_hjson_external")

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "ecdsa_p256_verify_testvectors_hardcoded",
    srcs = ["ecdsa_p256_verify_hardcoded.hjson"],
)

filegroup(
    name = "kmac_testvectors_hardcoded",
    srcs = ["kmac_hardcoded.hjson"],
)

filegroup(
    name = "sphincsplus_shake_128s_simple_testvectors_hardcoded",
    srcs = ["sphincsplus_shake_128s_simple_hardcoded.hjson"],
)

filegroup(
    name = "sphincsplus_sha2_128s_simple_testvectors_hardcoded",
    srcs = ["sphincsplus_sha2_128s_simple_hardcoded.hjson"],
)

filegroup(
    name = "hmac_testvectors_random",
    srcs = ["hmac_testvectors_random.hjson"],
)

filegroup(
    name = "kdf_testvectors_random",
    srcs = ["kdf_testvectors_random.hjson"],
)

exports_files([
    "sha3_224_hardcoded.hjson",
])
