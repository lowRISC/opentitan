# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otbn.bzl", "otbn_binary")

package(default_visibility = ["//visibility:public"])

otbn_binary(
    name = "mlkem1024_encaps",
    srcs = [
        "mlkem1024_encaps.s",
        "mlkem1024_encaps_mem.s",
        "mlkem1024_encrypt.s",
        "//sw/otbn/crypto:xof.s",
        "//sw/otbn/crypto/mlkem1024:mlkem1024_arith.s",
        "//sw/otbn/crypto/mlkem1024:mlkem1024_decoding.s",
        "//sw/otbn/crypto/mlkem1024:mlkem1024_encoding.s",
        "//sw/otbn/crypto/mlkem1024:mlkem1024_expand.s",
        "//sw/otbn/crypto/mlkem1024:mlkem1024_ntt.s",
        "//sw/otbn/crypto/mlkem1024:mlkem1024_sample.s",
    ],
)
