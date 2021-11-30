# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

exports_files(glob(["**"]))

genrule(
    name = "ot_version_file",
    outs = ["ot_version.txt"],
    cmd = """awk '/BUILD_GIT_VERSION/ { print $$2 }' bazel-out/volatile-status.txt > $@""",
    stamp = 1,  # this provides volatile-status.txt
)
