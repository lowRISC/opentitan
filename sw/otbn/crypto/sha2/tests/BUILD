# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otbn.bzl", "otbn_sim_test")

package(default_visibility = ["//visibility:public"])

otbn_sim_test(
    name = "sha256_masked_test",
    srcs = [
        "sha256_masked_test.s",
    ],
    testcase = "sha256_masked_test.hjson",
    deps = [
        "//sw/otbn/crypto/sha2:sha256_masked",
    ],
)

otbn_sim_test(
    name = "sha384_masked_test",
    srcs = [
        "sha384_masked_test.s",
    ],
    testcase = "sha384_masked_test.hjson",
    deps = [
        "//sw/otbn/crypto/sha2:sha384_masked",
    ],
)

otbn_sim_test(
    name = "sha512_masked_test",
    srcs = [
        "sha512_masked_test.s",
    ],
    testcase = "sha512_masked_test.hjson",
    deps = [
        "//sw/otbn/crypto/sha2:sha512_masked",
    ],
)
