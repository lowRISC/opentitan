# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//rules:common_settings.bzl", "string_flag")
load("@rules_rust_bindgen//:defs.bzl", "rust_bindgen_toolchain")

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

rust_bindgen_toolchain(
    name = "bindgen_toolchain_impl",
    bindgen = "@rules_rust_bindgen//3rdparty:bindgen",
    clang = "@bindgen_clang_linux//:clang",
    libclang = "@bindgen_clang_linux//:libclang",
    libstdcxx = select({
        ":specify_bindgen_libstdcxx": "@bindgen_libstdcxx_linux//:libstdc++",
        "//conditions:default": None,
    }),
)

toolchain(
    name = "bindgen_toolchain",
    toolchain = "bindgen_toolchain_impl",
    toolchain_type = "@rules_rust_bindgen//:toolchain_type",
)
