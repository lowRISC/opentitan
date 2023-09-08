# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//bindgen:repositories.bzl", "rust_bindgen_dependencies")
load("@rules_rust//rust:repositories.bzl", "rules_rust_dependencies", "rust_register_toolchains", "rust_repository_set")
load("@rules_rust//tools/rust_analyzer:deps.bzl", "rust_analyzer_dependencies")

def rust_deps():
    rules_rust_dependencies()
    rust_register_toolchains(
        # TODO(#15300): set this to `True` to support rust-analyzer, after fixing
        # upstream `rules_rust`.
        #include_rustc_srcs = False,
        edition = "2021",
        versions = ["1.71.1", "nightly/2023-07-30"],
        extra_target_triples = [
            "riscv32imc-unknown-none-elf",
        ],
    )

    rust_bindgen_dependencies()
    native.register_toolchains(
        "//third_party/rust:bindgen_toolchain",
    )

    rust_analyzer_dependencies()
