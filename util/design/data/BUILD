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

string_flag(
    name = "data_perm",
    build_setting_default = "",
)
