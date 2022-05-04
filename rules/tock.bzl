# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Rules for assembling Tock binaries.
"""
load("@rules_cc//cc:find_cc_toolchain.bzl", "find_cc_toolchain")
load(
    "//rules:rv.bzl",
    "rv_rule",
    _OPENTITAN_CPU = "OPENTITAN_CPU",
    _OPENTITAN_PLATFORM = "OPENTITAN_PLATFORM",
)

TockApplication = provider(
    fields = {
        "tab": "TAB file for this application",
        "tbf": "TBF file for this application",
        "elf": "ELF file for this application",
    },
)

def _tock_elf2tab_impl(ctx):
    name = ctx.attr.package_name if ctx.attr.package_name else ctx.attr.name

    tabfile = ctx.actions.declare_file("{}.tab".format(name))
    tbffile = ctx.actions.declare_file("{}.tbf".format(name))

    elffile = ctx.actions.declare_file("{}.elf".format(name))
    ctx.actions.symlink(output = elffile, target_file = ctx.file.src)

    outputs = [tabfile, tbffile]
    args = [
        "--kernel-major={}".format(ctx.attr.kernel_major),
        "--kernel-minor={}".format(ctx.attr.kernel_minor),
        "--package-name={}".format(name),
        "--output-file={}".format(tabfile.path),
    ]
    if ctx.attr.protected_region_size:
        args.append("--protected-region-size={}".format(ctx.attr.protected_region_size))
    if ctx.attr.stack:
        args.append("--stack={}".format(ctx.attr.stack))
    if ctx.attr.verbose:
        args.append("--verbose")
    args.append(elffile.path)

    ctx.actions.run(
        mnemonic = "ELF2TAB",
        outputs = outputs,
        inputs = [elffile, ctx.executable._elf2tab],
        arguments = args,
        executable = ctx.executable._elf2tab,
    )

    outputs.append(elffile)
    return [
        TockApplication(tab = tabfile, tbf = tbffile, elf = elffile),
        DefaultInfo(
            files = depset(outputs),
            data_runfiles = ctx.runfiles(files = outputs),
        ),
    ]

tock_elf2tab = rule(
    implementation = _tock_elf2tab_impl,
    attrs = {
        "kernel_major": attr.int(default = 2, doc = "Kernel major version required by the app"),
        "kernel_minor": attr.int(default = 0, doc = "Minimum kernel minor version required by the app"),
        "package_name": attr.string(default = "", doc = "Package name"),
        "protected_region_size": attr.int(default = 0, doc = "Size of the TBF header"),
        "stack": attr.int(default = 0, doc = "Stack size"),
        "verbose": attr.bool(default = True, doc = "Verbose output"),
        "src": attr.label(mandatory = True, allow_single_file = True, doc = "ELF binary to convert"),
        "_elf2tab": attr.label(
            default = "@raze__elf2tab__0_10_0_dev//:cargo_bin_elf2tab",
            executable = True,
            cfg = "exec",
        ),
    },
)

def _tock_image_impl(ctx):
    cc_toolchain = find_cc_toolchain(ctx).cc

    intermediate_elf = ctx.actions.declare_file("{}.elf".format(ctx.attr.name))
    output = ctx.actions.declare_file("{}.bin".format(ctx.attr.name))
    tab = ctx.attr.app[TockApplication].tbf

    ctx.actions.run(
        outputs = [intermediate_elf],
        inputs = [ctx.file.kernel, tab] + cc_toolchain.all_files.to_list(),
        arguments = [
            "--update-section",
            ".apps={}".format(tab.path),
            ctx.file.kernel.path,
            intermediate_elf.path,
        ],
        executable = cc_toolchain.objcopy_executable,
    )
    ctx.actions.run(
        outputs = [output],
        inputs = [intermediate_elf] + cc_toolchain.all_files.to_list(),
        arguments = [
            "--output-target=binary",
            intermediate_elf.path,
            output.path,
        ],
        executable = cc_toolchain.objcopy_executable,
    )
    return [
        DefaultInfo(files = depset([output]), data_runfiles = ctx.runfiles(files = [output])),
        OutputGroupInfo(
            bin = depset([output]),
            elf = depset([intermediate_elf]),
        ),
    ]

tock_image = rv_rule(
    implementation = _tock_image_impl,
    attrs = {
        "kernel": attr.label(mandatory = True, allow_single_file = True, doc = "Kernel ELF file"),
        "app": attr.label(mandatory = True, providers = [TockApplication], doc = "Application TAB label"),
        "_cc_toolchain": attr.label(default = Label("@bazel_tools//tools/cpp:current_cc_toolchain")),
    },
    toolchains = ["@rules_cc//cc:toolchain_type"],
)
