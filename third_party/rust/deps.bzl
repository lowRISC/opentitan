# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust_bindgen//:repositories.bzl", "rust_bindgen_dependencies")

def rust_deps():
    rust_bindgen_dependencies()
    native.register_toolchains(
        "@lowrisc_opentitan//third_party/rust:bindgen_toolchain",
    )
