# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//rules:build_test.bzl", "build_test")
load("@bazel_skylib//rules:diff_test.bzl", "diff_test")
load("@bazel_skylib//rules:write_file.bzl", "write_file")
load("//third_party/python:requirements.bzl", "all_data_requirements", "all_requirements", "all_whl_requirements")

package(default_visibility = ["//visibility:public"])

exports_files([
    "gen_requirements.sh",
])

# The requirements.bzl file is using the hub repo to access packages via the
# `requirement` macro and when the requirements.bzl is vendored, the hub
# repo won't be present. As a result, we have to adjust the label scheme in
# the requirements.bzl to make sure that they continue to work.
genrule(
    name = "requirements_bzl",
    srcs = ["@ot_python_deps//:requirements.bzl"],
    outs = ["requirements.clean.bzl"],
    cmd = " | ".join([
        "cat $<",
        # Substitute the name of the hub to ensure that the dependencies do
        # not require the hub repo initialized in the WORKSPACE.
        "sed -e 's/ot_python_deps/ot_python_deps_vendored/g'",
        # Change the labels from using the hub repo to using the spoke repos
        # directly.
        "sed -e 's|//\\([^:]*\\):pkg|_\\1//:pkg|g'",
        "sed -e 's|//\\([^:]*\\):whl|_\\1//:whl|g'",
        "sed -e 's|//\\([^:]*\\):data|_\\1//:data|g'",
        # Change the convenience macros to use the same naming.
        "sed -e 's|//{}:{}|_{}//:{}|g' >$@",
    ]),
)

write_file(
    name = "gen_update",
    out = "update.sh",
    content = [
        "#!/usr/bin/env bash",
        "cd $BUILD_WORKSPACE_DIRECTORY",
        "cp -fv bazel-bin/third_party/python/requirements.clean.bzl third_party/python/requirements.bzl",
    ],
)

sh_binary(
    name = "vendor_requirements",
    srcs = ["update.sh"],
    data = [":requirements_bzl"],
)

# Similarly ensures that the requirements.bzl file is updated based on the
# requirements.txt lockfile.
diff_test(
    name = "test_vendored",
    failure_message = "Please run:  bazel run //third_party/python:vendor_requirements",
    file1 = "requirements.bzl",
    file2 = "requirements_bzl",
)

build_test(
    name = "test_requirement_lists",
    targets = all_requirements + all_whl_requirements + all_data_requirements,
)
