# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//rules:common_settings.bzl", "int_flag", "string_flag")

package(default_visibility = ["//visibility:public"])

exports_files(glob(["**"]))

# These configurations expose the OTP image generation tool's command line
# arguments to enable dvsim to pass this through Bazel to the underlying OTP
# image generation script. This is required to enable dvsim to invoke OTP image
# generation as part of the Bazel build process, while still enabling the use of
# multiple seeds needed to achieve DV coverage.
int_flag(
    name = "img_seed",
    build_setting_default = 0,
)

string_flag(
    name = "lc_seed",
    # Default must match value in hw/top_earlgrey/data/otp/lc_ctrl.hjson.
    build_setting_default = "40182201019264397688411770949626922549663256047001778394918990008320537410392",
)

string_flag(
    name = "otp_seed",
    # Default must match value in hw/top_earlgrey/data/otp/otp_ctrl_mmap.hjson.
    build_setting_default = "36021179872380457113239299468132194022238108125576166239904535336103582949069",
)

string_flag(
    name = "data_perm",
    build_setting_default = "",
)
