# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//bindgen:repositories.bzl", "rust_bindgen_dependencies", "rust_bindgen_register_toolchains")
load("@rules_rust//rust:repositories.bzl", "rules_rust_dependencies", "rust_register_toolchains", "rust_repository_set")
load("//third_party/rust/crates:crates.bzl", "raze_fetch_remote_crates")
load("@rules_rust//tools/rust_analyzer:deps.bzl", "rust_analyzer_dependencies")
load(
    "@safe_ftdi//third_party/rust:deps.bzl",
    ftdi_fetch_remote_crates = "fetch_remote_crates",
)
load(
    "@serde_annotate//third_party/rust:deps.bzl",
    serde_annotate_fetch_remote_crates = "fetch_remote_crates",
)

def rust_deps():
    rules_rust_dependencies()
    rust_register_toolchains(
        # TODO(#15300): set this to `True` to support rust-analyzer, after fixing
        # upstream `rules_rust`.
        include_rustc_srcs = False,
        edition = "2021",
        version = "nightly",
        iso_date = "2022-09-21",
    )
    rust_repository_set(
        name = "rust_opentitan_rv32imc",
        version = "nightly",
        exec_triple = "x86_64-unknown-linux-gnu",
        extra_target_triples = ["riscv32imc-unknown-none-elf"],
        iso_date = "2022-03-22",
        edition = "2021",
    )
    rust_bindgen_dependencies()
    rust_bindgen_register_toolchains()
    raze_fetch_remote_crates()
    ftdi_fetch_remote_crates()
    serde_annotate_fetch_remote_crates()
    rust_analyzer_dependencies()
