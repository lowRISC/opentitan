# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_cc//cc:find_cc_toolchain.bzl", "find_cc_toolchain")

"""Rust generation rules for `ujson`."""

def _ujson_rust(ctx):
    cc_toolchain = find_cc_toolchain(ctx)
    module = ctx.actions.declare_file("{}.rs".format(ctx.label.name))
    ujson_lib = ctx.attr.ujson_lib[CcInfo].compilation_context.headers.to_list()

    # Get the include search path for ujson.
    ujson_lib_root = ctx.attr.ujson_lib[CcInfo].compilation_context.quote_includes.to_list()

    srcs = []
    includes = []
    for src in ctx.attr.srcs:
        srcs.extend(src[CcInfo].compilation_context.direct_public_headers)
        includes.extend(src[CcInfo].compilation_context.headers.to_list())

    # TODO(cfrantz): Is there a better way to find the `rustfmt` binary?
    rustfmt_files = ctx.attr._rustfmt.data_runfiles.files.to_list()
    rustfmt = [f for f in rustfmt_files if f.basename == "rustfmt"][0]

    defines = ["-D{}".format(d) for d in ctx.attr.defines]

    # The pipeline for generating rust code from a ujson header file:
    # 1. Preprocess the file with RUST_PREPROCESSOR_EMIT
    # 2. Grep out all the preprocessor noise (which starts with `#`).
    # 3. Substitute all `rust_attr` for `#`, thus creating rust attributes.
    # 4. Format it with `rustfmt` so it looks nice and can be inspected.
    command = """
        {preprocessor} -nostdinc -I{ujson_lib_root_includes} \
        -DRUST_PREPROCESSOR_EMIT=1 -DNOSTDINC=1 {defines} $@ \
        | grep -v '#' \
        | sed -e "s/rust_attr/#/g" \
        | {rustfmt} > {module}""".format(
        preprocessor = cc_toolchain.preprocessor_executable,
        defines = " ".join(defines),
        module = module.path,
        rustfmt = rustfmt.path,
        ujson_lib_root_includes = " -I".join(ujson_lib_root),
    )

    ctx.actions.run_shell(
        outputs = [module],
        inputs = ujson_lib + srcs + includes,
        tools = cc_toolchain.all_files.to_list() + rustfmt_files,
        arguments = [src.path for src in srcs],
        command = command,
    )
    return [
        DefaultInfo(files = depset([module]), runfiles = ctx.runfiles([module])),
    ]

ujson_rust = rule(
    implementation = _ujson_rust,
    attrs = {
        "srcs": attr.label_list(
            providers = [CcInfo],
            doc = "ujson cc_library targets to generate Rust for",
        ),
        "defines": attr.string_list(
            doc = "C preprocessor defines",
        ),
        "ujson_lib": attr.label(
            default = "//sw/device/lib/ujson",
            doc = "Location of the ujson library",
            providers = [CcInfo],
        ),
        "_cc_toolchain": attr.label(default = Label("@bazel_tools//tools/cpp:current_cc_toolchain")),
        "_rustfmt": attr.label(
            default = "@rules_rust//rust/toolchain:current_rustfmt_files",
            cfg = "exec",
        ),
    },
    toolchains = ["@rules_cc//cc:toolchain_type"],
)
