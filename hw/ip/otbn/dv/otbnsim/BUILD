# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_binary")

package(default_visibility = ["//visibility:public"])

# Make standalone simulator visible to OTBN tests within Bazel (see
# rules/otbn.bzl). Note that this means other files in this directory and
# subdirectories are not included in all_files targets for higher-level
# directories.
exports_files(["standalone.py"])
