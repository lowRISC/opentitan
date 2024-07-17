# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//rules:common_settings.bzl", "string_flag")
load("@rules_cc//cc:defs.bzl", "cc_import")
load("@rules_rust//bindgen:defs.bzl", "rust_bindgen_toolchain")
load("@rules_rust//crate_universe:defs.bzl", "crate", "crates_vendor")

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
    libstdcxx = select({
        ":specify_bindgen_libstdcxx": ":libc++",
        "//conditions:default": None,
    }),
)

toolchain(
    name = "bindgen_toolchain",
    toolchain = "bindgen_toolchain_impl",
    toolchain_type = "@rules_rust//bindgen:toolchain_type",
)
