# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "fake",
    srcs = [
        "fake_keys.c",
    ],
    hdrs = [
        "rma_unlock_token_export_key.pk_hsm.h",
    ],
    deps = [
        "//sw/device/lib/crypto/impl:ecc",
    ],
)

exports_files([
    "rma_unlock_token_export_key.sk_hsm.der",
])
