# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python/entry_points:py_console_script_binary.bzl", "py_console_script_binary")
load("@rules_rust//crate_universe:defs.bzl", "crate", "crates_vendor")

package(default_visibility = ["//visibility:public"])

crates_vendor(
    name = "tock_index",
    cargo_lockfile = "//third_party/tock:Cargo.lock",
    manifests = ["//third_party/tock:Cargo.toml"],
    mode = "remote",
    tags = ["manual"],
    vendor_path = "crates",
)

py_console_script_binary(
    name = "tockloader",
    pkg = "@ot_python_deps//tockloader",
)
