# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otbn.bzl", "otbn_library")

package(default_visibility = ["//visibility:public"])

otbn_library(
    name = "mldsa87_ntt",
    srcs = [
        "mldsa87_ntt.s",
    ],
    includes = ["mldsa87.inc"],
)

otbn_library(
    name = "mldsa87_arith",
    srcs = [
        "mldsa87_arith.s",
    ],
    includes = ["mldsa87.inc"],
)

otbn_library(
    name = "xof",
    srcs = [
        "xof.s",
    ],
)

otbn_library(
    name = "mldsa87_sample",
    srcs = [
        "mldsa87_sample.s",
    ],
    includes = ["mldsa87.inc"],
)

otbn_library(
    name = "mldsa87_expand",
    srcs = [
        "mldsa87_expand.s",
    ],
    includes = ["mldsa87.inc"],
)

otbn_library(
    name = "mldsa87_utils",
    srcs = [
        "mldsa87_utils.s",
    ],
    includes = ["mldsa87.inc"],
)

otbn_library(
    name = "mldsa87_encoding",
    srcs = [
        "mldsa87_encoding.s",
    ],
    includes = ["mldsa87.inc"],
)

otbn_library(
    name = "mldsa87_decoding",
    srcs = [
        "mldsa87_decoding.s",
    ],
    includes = ["mldsa87.inc"],
)

otbn_library(
    name = "mldsa87_gadgets",
    srcs = [
        "mldsa87_gadgets.s",
        "//sw/otbn/crypto:mai_gadgets.s",
    ],
    includes = ["mldsa87.inc"],
)
