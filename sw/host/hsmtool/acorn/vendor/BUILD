# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//bindgen:defs.bzl", "rust_bindgen_library")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "acorn_hdr",
    hdrs = ["acorn.h"]
)

rust_bindgen_library(
    name = "acorn_bindgen",
    bindgen_flags = [
        "--with-derive-default",
        "--impl-debug",
        "--allowlist-type=acorn_(request|response|command|cmd|free)_.*",
        "--allowlist-type=acorn_.*",
    ],
    cc_lib = ":acorn_hdr",
    header = "acorn.h",
    rustc_flags = [
        "--allow=non_snake_case",
        "--allow=non_upper_case_globals",
        "--allow=non_camel_case_types",
    ],
)
