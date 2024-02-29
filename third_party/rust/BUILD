# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//rules:common_settings.bzl", "string_flag")
load("@rules_rust//bindgen:bindgen.bzl", "rust_bindgen_toolchain")
load("@rules_rust//crate_universe:defs.bzl", "crate", "crates_vendor")
load("@rules_rust//proto/prost:defs.bzl", "rust_prost_toolchain")

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

rust_prost_toolchain(
    name = "prost_toolchain_impl",
    prost_plugin = "@crate_index//:protoc-gen-prost__protoc-gen-prost",
    prost_runtime = "@crate_index//:prost",
    prost_types = "@crate_index//:prost-types",
    proto_compiler = "@com_google_protobuf//:protoc",
    # Disable tonic.
    tonic_plugin_flag = "",
)

toolchain(
    name = "prost_toolchain",
    toolchain = "prost_toolchain_impl",
    toolchain_type = "@rules_rust//proto/prost:toolchain_type",
)

crates_vendor(
    name = "crate_index",
    annotations = {
        "libudev-sys": [crate.annotation(
            patch_args = ["-p1"],
            patches = ["@//third_party/rust/patches:libudev-sys-0.1.4.patch"],
        )],
        "mdbook": [crate.annotation(
            gen_binaries = True,
            patch_args = ["-p1"],
            patches = ["@//third_party/rust/patches:mdbook-landing-page-links.patch"],
        )],
        "cryptoki": [crate.annotation(
            patch_args = ["-p2"],
            patches = [
                "@//third_party/rust/patches:cryptoki-vendor-defined-mechanism-type.patch",
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
            build_script_toolchains = ["@//third_party/rust:openssl_pkg_config_path"],
        )],
        "pqcrypto-internals": [crate.annotation(
            additive_build_file_content = """
                filegroup(name="include", srcs=glob(["include/*", "include/**"]))
            """,
        )],
        "pqcrypto-sphincsplus": [crate.annotation(
            # This patch is necessary because pqcrypto-sphincsplus expects an include file
            # from pqcrypto-internals to re-define `PQCLEAN_randombytes` as
            # `PQCRYPTO_RUST_randombytes` during the build process.  Since cargo repackages
            # repositories when creating downloadable crates _and_ since bazel sandboxes
            # builds, access to `pqcrypto-internals` is rather difficult.
            #
            # In the past, we overcame this by adding an environment variable pointing to
            # the pqcryptos-internals includes directory, but this was unreliable and bound
            # to break from either a bazel or rules_rust upgrade (indeed, I think updating
            # rules_rust broke this, as the `depenv` from pqcrypto-internals got added to
            # the dependencies of the build.rs for pqcrypto-sphincsplus, overriding the
            # value set in the env var).
            #
            # Instead, we set a custom env var and patch the build.rs script to pick up
            # our custom environment variable.  Since we aren't trying to reuse the
            # original env var, we can use standard bazel methods to expand the path and
            # modify the value appropriately in the build.rs script.
            # Like the prior solution, this is also a hack.
            build_script_data = [
                "@crate_index__pqcrypto-internals-0.2.5//:include",
            ],
            build_script_env = {
                "BAZEL_PQCRYPTO_INTERNALS_INCLUDES": "$(rootpaths @crate_index__pqcrypto-internals-0.2.5//:include)",
            },
            patch_args = ["-p2"],
            patches = [
                "@//third_party/rust/patches:pqcrypto-sphincsplus-includedir.patch",
            ],
        )],
        "protoc-gen-prost": [crate.annotation(
            gen_binaries = ["protoc-gen-prost"],
        )],
    },
    cargo_lockfile = "//third_party/rust:Cargo.lock",
    manifests = ["//third_party/rust:Cargo.toml"],
    mode = "remote",
    tags = ["manual"],
    vendor_path = "crates",
)
