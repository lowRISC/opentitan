# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust_bindgen//:repositories.bzl", "rust_bindgen_dependencies")
load(
    "@rules_rust//rust:repositories.bzl",
    "rules_rust_dependencies",
    "rust_analyzer_toolchain_repository",
    "rust_repository_set",
    "rustfmt_toolchain_repository",
)
load("@rules_rust//tools/rust_analyzer:deps.bzl", "rust_analyzer_dependencies")

def rust_deps():
    rules_rust_dependencies()
    rust_repository_set(
        name = "rust_host",
        exec_triple = "x86_64-unknown-linux-gnu",
        edition = "2021",
        # Nightly that Rust 1.85 branches from.
        versions = ["nightly/2024-11-22"],
        sha256s = {
            "2024-11-22/rustc-nightly-x86_64-unknown-linux-gnu.tar.xz": "02ef1e3ca25a03ccb9828a4e932b27f59a0625ed9772463d556539da38b7fd7b",
            "2024-11-22/clippy-nightly-x86_64-unknown-linux-gnu.tar.xz": "9f888010e1f01373d401c65ab0adf6f9fc76cbd0034f4346352c1bd211471339",
            "2024-11-22/cargo-nightly-x86_64-unknown-linux-gnu.tar.xz": "19cb321daca3e733a6b0baf06f70112ea037842e2c716d8eebb1791047fa1d88",
            "2024-11-22/llvm-tools-nightly-x86_64-unknown-linux-gnu.tar.xz": "8f245a660be95f0b45fb174f0af5f0401a436bf67c332543dfd829db8b9d6f1f",
            "2024-11-22/rust-std-nightly-x86_64-unknown-linux-gnu.tar.xz": "7e74dd19bb929dc7d53dacd595c3dff8d498a3f5485ea7ab057188c9d2f50224",
        }
    )

    rustfmt_toolchain_repository(
        name = "rustfmt_host",
        version = "nightly/2025-01-03",
        exec_triple = "x86_64-unknown-linux-gnu",
        sha256s = {
            "2025-01-03/rustc-nightly-x86_64-unknown-linux-gnu.tar.xz": "a7e713b2c38d2c16a2025d228480909a2281c91ad8fd225b1dacc3eda933724c",
            "2025-01-03/rustfmt-nightly-x86_64-unknown-linux-gnu.tar.xz": "78d9ffe673adf9762aeda32888754686155c366ac64b3da580c7c3da5d2ea820",
        },
    )

    rust_analyzer_toolchain_repository(
        name = "rust_analyzer_host",
        version = "nightly/2025-01-03",
        sha256s = {
            "rust-src-nightly.tar.xz": "3d1619643a2ffa0959b9ecaa78df09756c7f1fcd5010efa2f299c4332de90cb8",
            "2025-01-03/rustc-nightly-x86_64-unknown-linux-gnu.tar.xz": "a7e713b2c38d2c16a2025d228480909a2281c91ad8fd225b1dacc3eda933724c",
        },
    )

    rust_repository_set(
        name = "rust_tock",
        exec_triple = "x86_64-unknown-linux-gnu",
        edition = "2021",
        # Nightly that Tock uses:
        versions = ["nightly/2023-07-30"],
        # rustfmt_version = "nightly/2023-07-30",
        extra_target_triples = ["riscv32imc-unknown-none-elf"],
        sha256s = {
            "2023-07-30/rustc-nightly-x86_64-unknown-linux-gnu.tar.xz": "ecdee8821a57efbb699b7e3aa4cbfbd60b7970bce89a8cfb9bc7d65b9058ee42",
            "2023-07-30/clippy-nightly-x86_64-unknown-linux-gnu.tar.xz": "76ee5aac81d1348bfebd3d94d5fb65c3f4ea0cf5fc2de834926f93772547380c",
            "2023-07-30/cargo-nightly-x86_64-unknown-linux-gnu.tar.xz": "4ddb3ed2dd2acedf9097f4a1fe17b8cd571fdd7c9a49b1e31c228a284ec95049",
            "2023-07-30/llvm-tools-nightly-x86_64-unknown-linux-gnu.tar.xz": "dc71b9ae6a4a4b9fa259724b29f4ad19467197ced89a8aad675f5af112c4fb77",
            "2023-07-30/rust-std-nightly-riscv32imc-unknown-none-elf.tar.xz": "9790d50d4510443bbf4c13b68227a273345d28b84d29372bc5f5ea2d14d05f2d",
            "2023-07-30/rust-std-nightly-x86_64-unknown-linux-gnu.tar.xz": "b5a589a243923c5fa2a1f08e7b902bb0a64ae08010067b9074501a6e1fb8b042",
        },
    )

    rust_bindgen_dependencies()
    native.register_toolchains(
        "@lowrisc_opentitan//third_party/rust:bindgen_toolchain",
        "@rustfmt_host//:toolchain",
        "@rust_analyzer_host//:toolchain",
    )

    rust_analyzer_dependencies()
