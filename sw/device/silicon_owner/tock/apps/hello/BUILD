# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary")
load("//rules:linker.bzl", "ld_library")
load("//rules:tock.bzl", "tock_elf2tab")

package(default_visibility = ["//visibility:public"])

ld_library(
    name = "libtock_layout",
    includes = [
        "libtock_layout.ld",
    ],
)

ld_library(
    name = "layout",
    script = "layout.ld",
    deps = [
        ":libtock_layout",
    ],
)

rust_binary(
    name = "hello_elf",
    srcs = [
        "src/hello.rs",
    ],
    deps = [
        ":layout",
        "@libtock",
    ],
)

tock_elf2tab(
    name = "hello",
    src = ":hello_elf",
)
