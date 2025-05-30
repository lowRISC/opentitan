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
        versions = ["nightly/2025-01-03"],
        sha256s = {
            "2025-01-03/rustc-nightly-x86_64-unknown-linux-gnu.tar.xz": "a7e713b2c38d2c16a2025d228480909a2281c91ad8fd225b1dacc3eda933724c",
            "2025-01-03/clippy-nightly-x86_64-unknown-linux-gnu.tar.xz": "5d04b1e1a23c054cbb1775a32ece3d09f7bb158601b82a038f51bb998fce8ee8",
            "2025-01-03/cargo-nightly-x86_64-unknown-linux-gnu.tar.xz": "e28f21e048490c2cc212169799b5ac3a01651e6946aca2f120adf0be6f3a70d9",
            "2025-01-03/llvm-tools-nightly-x86_64-unknown-linux-gnu.tar.xz": "67e9e52780680c3a4b0dadc138864a9da0fb99a4af882d3477b90c8b2efe474c",
            "2025-01-03/rust-std-nightly-x86_64-unknown-linux-gnu.tar.xz": "a5f96b464ace329963eef9e358303a17b5544cbd49b450474f4bc16cae0cc191",
        },
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
