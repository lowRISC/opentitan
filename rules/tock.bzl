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
load("@tockloader_deps//:requirements.bzl", "entry_point")

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
    if ctx.attr.disable:
        args.append("--disable")
    args.append("{},{}".format(elffile.path, ctx.attr.arch))

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
        "protected_region_size": attr.int(doc = "Size of the TBF header"),
        "stack": attr.int(default = 0, doc = "Stack size"),
        "verbose": attr.bool(default = True, doc = "Verbose output"),
        "src": attr.label(mandatory = True, allow_single_file = True, doc = "ELF binary to convert"),
        "disable": attr.bool(default = False, doc = "Mark the application as disabled"),
        "arch": attr.string(mandatory = True, doc = "Target architecture for the ELF binary (e.g., `rv32imc`)"),
        "_elf2tab": attr.label(
            default = "@elf2tab//:bin",
            executable = True,
            cfg = "exec",
        ),
    },
)

# This `opt_mode` transition is used by the `tock_image` rule to transition the
# kernel and apps builds into the `opt` compilation mode.  This is required
# because `fastbuild` and `dbg` builds of tock will not fit into flash.
def _opt_mode_impl(settings, attr):
    return {"//command_line_option:compilation_mode": "opt"}

opt_mode = transition(
    implementation = _opt_mode_impl,
    inputs = [],
    outputs = ["//command_line_option:compilation_mode"],
)

def _tock_image_impl(ctx):
    cc_toolchain = find_cc_toolchain(ctx).cc

    kernel_binary = ctx.actions.declare_file("{}_kernel.bin".format(ctx.attr.name))
    images = [ctx.actions.declare_file("{}0.bin".format(ctx.attr.name))]

    ctx.actions.run(
        outputs = [kernel_binary],
        inputs = [ctx.file.kernel] + cc_toolchain.all_files.to_list(),
        arguments = [
            "--output-target=binary",
            ctx.file.kernel.path,
            kernel_binary.path,
        ],
        executable = cc_toolchain.objcopy_executable,
    )

    ctx.actions.run(
        outputs = [images[0]],
        inputs = [kernel_binary],
        arguments = [
            "flash",
            "--board",
            "opentitan_earlgrey",
            "--flash-file",
            images[0].path,
            "--address",
            "0x20000000",
            kernel_binary.path,
        ],
        executable = ctx.executable._tockloader,
    )

    for app in ctx.attr.apps:
        tab = app[TockApplication].tab
        input_image = images[-1]
        output_image = ctx.actions.declare_file("{}{}.bin".format(ctx.attr.name, len(images)))
        images += [output_image]

        ctx.actions.run_shell(
            outputs = [output_image],
            inputs = [input_image, tab, ctx.executable._tockloader],
            command = "\
              cp {} {} &&\
              chmod +rw {} &&\
              {} install\
                --board opentitan_earlgrey\
                --flash-file {}\
                --app-address {}\
                {}\
                {}\
            ".format(
                input_image.path,
                output_image.path,
                output_image.path,
                ctx.executable._tockloader.path,
                output_image.path,
                ctx.attr.app_flash_start,
                "--debug" if ctx.attr.debug else "",
                tab.path,
            ),
        )

    output = ctx.actions.declare_file("{}.bin".format(ctx.attr.name))
    ctx.actions.symlink(
        output = output,
        target_file = images[-1],
    )

    return [
        DefaultInfo(files = depset([output]), data_runfiles = ctx.runfiles(files = [output])),
        OutputGroupInfo(
            bin = depset([output]),
        ),
    ]

tock_image = rv_rule(
    implementation = _tock_image_impl,
    attrs = {
        "kernel": attr.label(mandatory = True, allow_single_file = True, doc = "Kernel ELF file", cfg = opt_mode),
        "app_flash_start": attr.int(mandatory = True, doc = "Start of flash region for applications"),
        "apps": attr.label_list(mandatory = True, providers = [TockApplication], doc = "Application TAB labels", cfg = opt_mode),
        "debug": attr.bool(default = True, doc = "Tockloader debug output"),
        "_cc_toolchain": attr.label(default = Label("@bazel_tools//tools/cpp:current_cc_toolchain")),
        "_tockloader": attr.label(
            default = entry_point(
                pkg = "tockloader",
                script = "tockloader",
            ),
            executable = True,
            cfg = "exec",
        ),
    },
    toolchains = ["@rules_cc//cc:toolchain_type"],
)
