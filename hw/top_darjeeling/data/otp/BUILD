# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load(
    "//rules:otp.bzl",
    "otp_json_overlay",
)

exports_files(["otp_ctrl_mmap.hjson"])

# This is a set of overlays to generate a generic, standard OTP image.
# Additional overlays can be applied on top to further customize the OTP.
otp_json_overlay(
    name = "std_otp_overlay",
    overlays = [
    ],
)
