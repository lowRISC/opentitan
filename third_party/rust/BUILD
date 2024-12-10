# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//rules:common_settings.bzl", "string_flag")
load("@rules_rust//bindgen:defs.bzl", "rust_bindgen_toolchain")
load("@rules_cc//cc:defs.bzl", "cc_import")

package(default_visibility = ["//visibility:public"])

config_setting(
    name = "specify_bindgen_libstdcxx",
    values = {"define": "SPECIFY_BINDGEN_LIBSTDCXX=true"},
)

string_flag(
    name = "openssl_pkg_config_path",
    build_setting_default = "",
    make_variable = "OPENSSL_PKG_CONFIG_PATH",
)

# Since rules_rust 0.23.0, bindgen depends on the llvm project and builds the
# llvm libaries from source. Building llvm from source has a huge impact on
# build times. Instead, we depend on a pre-built llvm release and instantiate
# the bindgen toolchain with the prebuilt binaries.
cc_import(
    name = "libclang",
    shared_library = "@llvm_toolchain_llvm//:lib/libclang.so",
)

cc_import(
    name = "libc++",
    shared_library = "@llvm_toolchain_llvm//:lib/libc++.so",
)

rust_bindgen_toolchain(
    name = "bindgen_toolchain_impl",
    bindgen = "@rules_rust//bindgen/3rdparty:bindgen",
    clang = "@llvm_toolchain_llvm//:bin/clang",
    libclang = ":libclang",
    libstdcxx = ":libc++",
)

toolchain(
    name = "bindgen_toolchain",
    toolchain = "bindgen_toolchain_impl",
    toolchain_type = "@rules_rust//bindgen:toolchain_type",
)
