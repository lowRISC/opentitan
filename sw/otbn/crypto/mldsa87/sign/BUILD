# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otbn.bzl", "otbn_binary", "otbn_library")

package(default_visibility = ["//visibility:public"])

otbn_binary(
    name = "run_mldsa87_sign",
    srcs = [
        # do not sort
        "//sw/otbn/crypto/mldsa87:mldsa87_utils.s",
        "//sw/otbn/crypto/mldsa87:mldsa87_arith.s",
        "//sw/otbn/crypto/mldsa87:mldsa87_ntt.s",
        "//sw/otbn/crypto/mldsa87:mldsa87_sample.s",
        "//sw/otbn/crypto/mldsa87:mldsa87_encoding.s",
        "//sw/otbn/crypto/mldsa87:mldsa87_xof.s",
        "//sw/otbn/crypto/mldsa87:mldsa87_expand.s",
        "//sw/otbn/crypto/mldsa87:mldsa87_gadgets.s",
        "mldsa87_sign_sample.s",
    ],
)