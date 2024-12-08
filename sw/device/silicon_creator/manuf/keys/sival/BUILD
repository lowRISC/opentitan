# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

exports_files(glob(["**"]))

filegroup(
    name = "ca_data",
    srcs = [
        ":ca_config.json",
        ":dice_ca.pem",
        ":rma_unlock_enc_rsa3072.pub.der",
        # The fake RMA unlock token wrapping key is used for FPGA testing.
        "//sw/device/silicon_creator/manuf/keys/fake:rma_unlock_enc_rsa3072.pub.der",
    ],
)
