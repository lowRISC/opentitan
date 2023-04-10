# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//bindgen:repositories.bzl", "rust_bindgen_dependencies", "rust_bindgen_register_toolchains")
load("@rules_rust//rust:repositories.bzl", "rules_rust_dependencies", "rust_register_toolchains", "rust_repository_set")
load("@rules_rust//tools/rust_analyzer:deps.bzl", "rust_analyzer_dependencies")

def rust_deps():
    rules_rust_dependencies()
    rust_register_toolchains(
        # TODO(#15300): set this to `True` to support rust-analyzer, after fixing
        # upstream `rules_rust`.
        #include_rustc_srcs = False,
        edition = "2021",
        versions = ["1.67.0", "nightly/2023-01-26"],
        extra_target_triples = [
            "riscv32imc-unknown-none-elf",
        ],
    )

    rust_bindgen_dependencies()
    rust_bindgen_register_toolchains()
    rust_analyzer_dependencies()
