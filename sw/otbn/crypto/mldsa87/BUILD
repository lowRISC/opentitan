# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otbn.bzl", "otbn_binary", "otbn_library")

package(default_visibility = ["//visibility:public"])

# ML-DSA-87 routines source files.
MLDSA87_ROUTINES_SRCS = [
    "mldsa87_arith.s",
    "mldsa87_encoding.s",
    "mldsa87_expand.s",
    "mldsa87_gadgets.s",
    "mldsa87_ntt.s",
    "mldsa87_ops.s",
    "mldsa87_rounding.s",
    "mldsa87_sample.s",
    "mldsa87_utils.s",
    "//sw/otbn/crypto:mai_gadgets.s",
    "//sw/otbn/crypto:xof.s",
]

otbn_library(
    name = "mldsa87_routines",
    srcs = MLDSA87_ROUTINES_SRCS,
    includes = ["mldsa87.inc"],
)

# OTBN apps can link this library and call `mldsa87_keygen`, `mldsa87_sign` and
# `mldsa87_verify` as subroutines.
otbn_library(
    name = "mldsa87",
    srcs = MLDSA87_ROUTINES_SRCS + [
        "mldsa87_keygen.s",
        "mldsa87_mem.s",
        "mldsa87_sign.s",
        "mldsa87_verify.s",
    ],
    includes = ["mldsa87.inc"],
)

# Standalone ML-DSA-87 app.
otbn_binary(
    name = "run_mldsa87",
    srcs = ["run_mldsa87.s"],
    includes = ["mldsa87.inc"],
    deps = [":mldsa87"],
)
