# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otbn.bzl", "otbn_sim_test")

package(default_visibility = ["//visibility:public"])

otbn_sim_test(
    name = "mlkem1024_decrypt_test",
    srcs = [
        "mlkem1024_decrypt_test.s",
        "//sw/otbn/crypto:mai_gadgets.s",
        "//sw/otbn/crypto:xof.s",
        "//sw/otbn/crypto/mlkem1024:mlkem1024_arith.s",
        "//sw/otbn/crypto/mlkem1024:mlkem1024_decoding.s",
        "//sw/otbn/crypto/mlkem1024:mlkem1024_encoding.s",
        "//sw/otbn/crypto/mlkem1024:mlkem1024_expand.s",
        "//sw/otbn/crypto/mlkem1024:mlkem1024_ntt.s",
        "//sw/otbn/crypto/mlkem1024:mlkem1024_sample.s",
        "//sw/otbn/crypto/mlkem1024/decaps:mlkem1024_decrypt.s",
        "//sw/otbn/crypto/mlkem1024/decaps:mlkem1024_decrypt_mem.s",
        "//sw/otbn/crypto/mlkem1024/encaps:mlkem1024_encrypt.s",
    ],
    testcase = "mlkem1024_decrypt_test.hjson",
)

# Trigger cache invalidation for decaps memory layout changes
otbn_sim_test(
    name = "mlkem1024_decaps_test",
    srcs = [
        "//sw/otbn/crypto:mai_gadgets.s",
        "//sw/otbn/crypto:xof.s",
        "//sw/otbn/crypto/mlkem1024:mlkem1024_arith.s",
        "//sw/otbn/crypto/mlkem1024:mlkem1024_decoding.s",
        "//sw/otbn/crypto/mlkem1024:mlkem1024_encoding.s",
        "//sw/otbn/crypto/mlkem1024:mlkem1024_expand.s",
        "//sw/otbn/crypto/mlkem1024:mlkem1024_ntt.s",
        "//sw/otbn/crypto/mlkem1024:mlkem1024_sample.s",
        "//sw/otbn/crypto/mlkem1024/decaps:mlkem1024_decaps.s",
        "//sw/otbn/crypto/mlkem1024/decaps:mlkem1024_decaps_mem.s",
        "//sw/otbn/crypto/mlkem1024/decaps:mlkem1024_decrypt.s",
        "//sw/otbn/crypto/mlkem1024/encaps:mlkem1024_encrypt.s",
    ],
    testcase = "mlkem1024_decaps_test.hjson",
)

otbn_sim_test(
    name = "mlkem1024_decaps_reject_test",
    srcs = [
        "//sw/otbn/crypto:mai_gadgets.s",
        "//sw/otbn/crypto:xof.s",
        "//sw/otbn/crypto/mlkem1024:mlkem1024_arith.s",
        "//sw/otbn/crypto/mlkem1024:mlkem1024_decoding.s",
        "//sw/otbn/crypto/mlkem1024:mlkem1024_encoding.s",
        "//sw/otbn/crypto/mlkem1024:mlkem1024_expand.s",
        "//sw/otbn/crypto/mlkem1024:mlkem1024_ntt.s",
        "//sw/otbn/crypto/mlkem1024:mlkem1024_sample.s",
        "//sw/otbn/crypto/mlkem1024/decaps:mlkem1024_decaps.s",
        "//sw/otbn/crypto/mlkem1024/decaps:mlkem1024_decaps_mem.s",
        "//sw/otbn/crypto/mlkem1024/decaps:mlkem1024_decrypt.s",
        "//sw/otbn/crypto/mlkem1024/encaps:mlkem1024_encrypt.s",
    ],
    testcase = "mlkem1024_decaps_reject_test.hjson",
)
