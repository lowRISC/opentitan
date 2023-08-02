# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:ujson.bzl", "ujson_rust")

package(default_visibility = ["//visibility:public"])

exports_files(["roundtrip_test.rs"])

ujson_rust(
    name = "example",
    srcs = ["//sw/lib/sw/device/ujson:example"],
)
