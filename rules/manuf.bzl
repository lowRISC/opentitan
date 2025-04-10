# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:toolchain.bzl", "LOCALTOOLS_TOOLCHAIN")

def _device_id_header_gen_impl(ctx):
    tc = ctx.toolchains[LOCALTOOLS_TOOLCHAIN]

    # Output files before/after autoformatting.
    pre_formatted_c = ctx.actions.declare_file("{}.pre.c".format(ctx.attr.name))
    formatted_c = ctx.actions.declare_file("{}.c".format(ctx.attr.name))

    # Generate CP or FT device ID C file from a template.
    args = [
        "--mode={}".format(ctx.attr.mode),
        "--sku-config={}".format(ctx.file.sku_config.path),
        "--output={}".format(pre_formatted_c.path),
        "--template={}".format(ctx.file.template.path),
    ]
    if ctx.attr.mode == "ft":
        if hasattr(ctx.attr, "ast_cfg_version"):
            args.append(
                "--ast-cfg-version={}".format(ctx.attr.ast_cfg_version),
            )
        else:
            fail("Error: ast_cfg_version attribute must be provided when mode is \"ft\".")

    ctx.actions.run(
        outputs = [pre_formatted_c],
        inputs = [
            ctx.file.sku_config,
            ctx.file.template,
        ],
        arguments = args,
        executable = tc.tools.gen_devid,
        mnemonic = "GenDeviceId",
    )

    # Run clang-format on header file.
    ctx.actions.run_shell(
        outputs = [formatted_c],
        inputs = [pre_formatted_c, ctx.executable.clang_format],
        command = "{} {} > {}".format(
            ctx.executable.clang_format.path,
            pre_formatted_c.path,
            formatted_c.path,
        ),
        mnemonic = "ClangFormat",
    )

    return [
        DefaultInfo(files = depset([formatted_c])),
        OutputGroupInfo(
            sources = depset([formatted_c]),
        ),
    ]

device_id_header_gen = rule(
    implementation = _device_id_header_gen_impl,
    attrs = {
        # TODO(timothytrippel): remove this and fold into SKU config HJSON.
        "ast_cfg_version": attr.int(
            doc = "AST configuration version for the SKU config.",
        ),
        "sku_config": attr.label(
            allow_single_file = True,
            doc = "Path to the hjson SKU config file.",
        ),
        "template": attr.label(
            allow_single_file = True,
            doc = "Path to the template C file that script will fill in.",
        ),
        "clang_format": attr.label(
            default = "@lowrisc_rv32imcb_files//:bin/clang-format",
            allow_single_file = True,
            cfg = "host",
            executable = True,
            doc = "The clang-format executable",
        ),
        "mode": attr.string(
            mandatory = True,
            values = ["cp", "ft"],
            doc = "The device ID portion to generate (cp or ft).",
        ),
    },
    toolchains = [LOCALTOOLS_TOOLCHAIN],
)

def device_id_header(name, mode, headers, sku_config, template, ast_cfg_version = 0):
    device_id_header_gen(
        name = name,
        mode = mode,
        ast_cfg_version = ast_cfg_version,
        sku_config = sku_config,
        template = template,
    )
    native.filegroup(
        name = "{}_srcs".format(name),
        srcs = [":{}".format(name)],
        output_group = "sources",
    )
    native.cc_library(
        name = "{}_library".format(name),
        srcs = [":{}_srcs".format(name)],
        hdrs = headers,
    )
