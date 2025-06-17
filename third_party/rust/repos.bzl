# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@//rules:repo.bzl", "http_archive_or_local")

_CLANG_BUILD_FILE = """\
load("@rules_cc//cc:defs.bzl", "cc_import")

package(default_visibility = ["//visibility:public"])

sh_binary(
    name = "clang",
    srcs = ["bin/clang"],
)

filegroup(
    name = "system_includes",
    srcs = glob(["lib/clang/{version}/include/**"]),
)

cc_import(
    name = "libclang",
    shared_library = "lib/libclang.{suffix}",
)

cc_import(
    name = "libc++",
    shared_library = "lib/libc++.{suffix}"
)
"""

_LIBSTDCXX_BUILD_FILE = """\
load("@rules_cc//cc:defs.bzl", "cc_import")

package(default_visibility = ["//visibility:public"])

cc_import(
    name = "libstdc++",
    shared_library = "lib64/libstdc++.so.6"
)
"""

_NO_LIBSTDCXX_BUILD_FILE = """\
package(default_visibility = ["//visibility:public"])

filegroup(
    name = "libstdc++",
    srcs = [],
)
"""

def _rust_bindgen_libstdcxx_impl(rctx):
    libstdcxx_path = rctx.os.environ.get("RULES_RUST_BINDGEN_LIBSTDCXX_DIR")
    if libstdcxx_path:
        rctx.file("BUILD.bazel", _LIBSTDCXX_BUILD_FILE)
        rctx.symlink(libstdcxx_path, "lib64")
    else:
        # We need an empty `libstdc++` target for the analysis performed
        # by the airgapped environment preparation.
        rctx.file("BUILD.bazel", _NO_LIBSTDCXX_BUILD_FILE)

rust_bindgen_libstdcxx = repository_rule(
    implementation = _rust_bindgen_libstdcxx_impl,
    environ = ["RULES_RUST_BINDGEN_LIBSTDCXX_DIR"],
)

def rust_repos(rules_rust = None, serde_annotate = None, rules_rust_bindgen = None):
    # Since rules_rust 0.23.0, bindgen depedns on the llvm project and
    # builds the llvm libaries from source.  Building llvm from source has a
    # huge impact on build times.  Instead, we depend on a pre-built llvm
    # release and instantiate the bindgen toolchain with the prebuilt
    # binaries.
    # Releases @ http://releases.llvm.org/download.html
    http_archive_or_local(
        name = "bindgen_clang_linux",
        urls = ["https://github.com/llvm/llvm-project/releases/download/llvmorg-10.0.0/clang+llvm-10.0.0-x86_64-linux-gnu-ubuntu-18.04.tar.xz"],
        strip_prefix = "clang+llvm-10.0.0-x86_64-linux-gnu-ubuntu-18.04",
        sha256 = "b25f592a0c00686f03e3b7db68ca6dc87418f681f4ead4df4745a01d9be63843",
        build_file_content = _CLANG_BUILD_FILE.format(
            version = "10.0.0",
            suffix = "so",
        ),
    )

    # If an appropriate version of `libstdc++.so.6` is not available as part of
    # the default system libraries (e.g. if running on an old OS because of
    # EDA tooling), then an appopriate version can be supplied by setting
    # RULES_RUST_BINDGEN_LIBSTDCXX_DIR to the location of the library.
    rust_bindgen_libstdcxx(name = "bindgen_libstdcxx_linux")

    # We use forked/patched Rust Bazel rules to enable caching repository rules
    # required for air-gapped Bazel builds. See lowRISC/opentitan:#15300 for
    # more details.
    http_archive_or_local(
        name = "rules_rust",
        local = rules_rust,
        integrity = "sha256-CeF7R8AVBGVjGqMZ8nQnYKQ+3tqy6cAS+R0K4u/wImg=",
        urls = ["https://github.com/bazelbuild/rules_rust/releases/download/0.59.2/rules_rust-0.59.2.tar.gz"],
        patches = [
            "@lowrisc_opentitan//third_party/rust/patches:rules_rust.extra_rustc_toolchain_dirs.patch",
            "@lowrisc_opentitan//third_party/rust/patches:rules_rust.experimental.patch",
        ],
    )

    http_archive_or_local(
        name = "rules_rust_bindgen",
        local = rules_rust_bindgen,
        integrity = "sha256-CeF7R8AVBGVjGqMZ8nQnYKQ+3tqy6cAS+R0K4u/wImg=",
        strip_prefix = "extensions/bindgen",
        urls = ["https://github.com/bazelbuild/rules_rust/releases/download/0.59.2/rules_rust-0.59.2.tar.gz"],
        patches = [
            "@lowrisc_opentitan//third_party/rust/patches:rules_rust.bindgen_static_lib.patch",
            "@lowrisc_opentitan//third_party/rust/patches:rules_rust.transition.patch",
        ],
    )

    http_archive_or_local(
        name = "lowrisc_serde_annotate",
        local = serde_annotate,
        sha256 = "7300ed093fa3de679512ffdab7d0f1824be2b11f499bb852df29c3ae12e1348d",
        strip_prefix = "serde-annotate-0.0.12",
        url = "https://github.com/lowRISC/serde-annotate/archive/refs/tags/v0.0.12.tar.gz",
    )
