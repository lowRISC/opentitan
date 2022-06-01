# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:repositories.bzl", "rules_rust_dependencies", "rust_register_toolchains", "rust_repository_set")
load("//third_party/rust/crates:crates.bzl", "raze_fetch_remote_crates")
load("@rules_rust//tools/rust_analyzer/raze:crates.bzl", "rules_rust_tools_rust_analyzer_fetch_remote_crates")
load(
    "@safe_ftdi//third_party/rust:deps.bzl",
    ftdi_fetch_remote_crates = "fetch_remote_crates",
)

def rust_deps():
    rules_rust_dependencies()
    rust_register_toolchains(
        include_rustc_srcs = True,
        edition = "2018",
        version = "1.60.0",
    )
    rust_repository_set(
        name = "rust_opentitan_rv32imc",
        version = "nightly",
        exec_triple = "x86_64-unknown-linux-gnu",
        extra_target_triples = ["riscv32imc-unknown-none-elf"],
        iso_date = "2022-03-22",
        edition = "2021",
    )
    raze_fetch_remote_crates()
    ftdi_fetch_remote_crates()
    rules_rust_tools_rust_analyzer_fetch_remote_crates()
