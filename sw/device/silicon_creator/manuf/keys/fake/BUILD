# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

exports_files(glob(["**"]))

filegroup(
    name = "ca_data",
    srcs = [
        ":dice_ca.pem",
        ":ext_ca.pem",
        ":rma_unlock_enc_rsa3072.pub.der",
        ":sk.pkcs8.der",
    ],
)
