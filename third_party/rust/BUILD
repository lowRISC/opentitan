# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//rules:common_settings.bzl", "string_flag")
load("@rules_rust//bindgen:bindgen.bzl", "rust_bindgen_toolchain")
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

rust_bindgen_toolchain(
    name = "bindgen_toolchain_impl",
    bindgen = "@rules_rust//bindgen/3rdparty:bindgen",
    clang = "@bindgen_clang_linux//:clang",
    libclang = "@bindgen_clang_linux//:libclang",
    libstdcxx = select({
        ":specify_bindgen_libstdcxx": "@bindgen_libstdcxx_linux//:libstdc++",
        "//conditions:default": None,
    }),
    system_includes = "@bindgen_clang_linux//:system_includes",
)

toolchain(
    name = "bindgen_toolchain",
    toolchain = "bindgen_toolchain_impl",
    toolchain_type = "@rules_rust//bindgen:toolchain_type",
)

crates_vendor(
    name = "crate_index",
    annotations = {
        "libudev-sys": [crate.annotation(
            patch_args = ["-p1"],
            patches = ["@lowrisc_opentitan//third_party/rust/patches:libudev-sys-0.1.4.patch"],
        )],
        "mdbook": [crate.annotation(
            gen_binaries = True,
            patch_args = ["-p1"],
            patches = ["@lowrisc_opentitan//third_party/rust/patches:mdbook-landing-page-links.patch"],
        )],
        "cryptoki": [crate.annotation(
            patch_args = ["-p2"],
            patches = [
                "@lowrisc_opentitan//third_party/rust/patches:cryptoki-vendor-defined-mechanism-type.patch",
            ],
        )],
        "cryptoki-sys": [crate.annotation(
            additive_build_file_content = """
                filegroup(
                    name = "binding_srcs",
                    srcs = [
                        "src/lib.rs",
                        "src/bindings/x86_64-unknown-linux-gnu.rs",
                    ],
                )
            """,
        )],
        "openssl-sys": [crate.annotation(
            build_script_env = {
                "PKG_CONFIG_PATH": "$(OPENSSL_PKG_CONFIG_PATH)",
                "OPENSSL_STATIC": "1",
            },
            build_script_toolchains = ["@lowrisc_opentitan//third_party/rust:openssl_pkg_config_path"],
        )],
    },
    cargo_lockfile = "@lowrisc_opentitan//third_party/rust:Cargo.lock",
    manifests = ["@lowrisc_opentitan//third_party/rust:Cargo.toml"],
    mode = "remote",
    tags = ["manual"],
    vendor_path = "crates",
)
