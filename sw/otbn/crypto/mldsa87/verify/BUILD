# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otbn.bzl", "otbn_binary", "otbn_library")

package(default_visibility = ["//visibility:public"])

otbn_binary(
    name = "run_mldsa87_verify",
    srcs = [
        # do not sort
        "//sw/otbn/crypto/mldsa87:mldsa87_utils.s",
        "//sw/otbn/crypto/mldsa87:mldsa87_arith.s",
        "//sw/otbn/crypto/mldsa87:mldsa87_ntt.s",
        "//sw/otbn/crypto/mldsa87:mldsa87_sample.s",
        "//sw/otbn/crypto/mldsa87:mldsa87_encoding.s",
        "//sw/otbn/crypto/mldsa87:mldsa87_xof.s",
        "//sw/otbn/crypto/mldsa87:mldsa87_expand.s",
        "mldsa87_verify_encoding.s",
        "mldsa87_verify_norm.s",
        "mldsa87_verify_rounding.s",
        "mldsa87_verify_ops.s",
        "mldsa87_verify_mem.s",
        "mldsa87_verify.s",
    ],
)
