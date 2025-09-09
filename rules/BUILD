# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:autogen.bzl", "autogen_stamp_include")
load("//rules:stamp.bzl", "stamp_flag")
load("//rules/opentitan:defs.bzl", "OPENTITAN_PLATFORM")

package(default_visibility = ["//visibility:public"])

# See stamp.bzl for explanation.
stamp_flag(name = "stamp_flag")

# This target provides a C header containing all stamping variables.
#
#  By default, or when building with --nostamp, this rule produces an empty
#  C header file.
#
#  When building with --stamp, this rule will output a C header like the
#  following example:
#    #define BAZEL_BUILD_SCM_REVISION_SHORT 0d6b3555
#    #define BAZEL_BUILD_SCM_STATUS clean
#    #define BAZEL_BUILD_TIMESTAMP 1743189267
#    ...
#
# To avoid rebuilding to all dependents as transitive header, this generated
# file should be included in srcs instead of deps.
autogen_stamp_include(
    name = "autogen_stamp_include",
)
