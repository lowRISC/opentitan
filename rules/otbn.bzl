# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "OPENTITAN_PLATFORM", "opentitan_transition")
load("//rules:bugfix.bzl", "find_cc_toolchain")

def _otbn_binary(ctx):
    """The build process for otbn resources currently invokes
    `//hw/ip/otbn/util/otbn-{as,ld,...}` to build the otbn resource.
    These programs are python scripts which translate otbn special
    instructions into the proper opcode sequences and _then_ invoke the normal
    `rv32-{as,ld,...}` programs to produce the resource.  These "native"
    otbn resources are the `otbn_objs` and `elf` output groups.

    In order to make the otbn resource useful to the the main CPU, the
    otbn resource needs to be included as a blob of data that the main
    CPU can dump into the otbn `imem` area and ask otbn to execute it.
    `util/otbn-build.py` does this with some objcopy-fu, emitting
    `foo.rv32embed.o`.  Bazel's `cc_*` rules really want dependency objects
    expressed as archives rather than raw object files, so I've modified
    `otbn-build` to also emit an archive file.

    _Morally_, the otbn resource is a data dependency.  However the
    practical meaning of a `data` dependency in bazel is a file made
    available at runtime, which is not how we're using the otbn resource.
    The closest analog is something like `cc_embed_data`, which is like
    a data dependency that needs to be linked into the main program.
    We achieve by having `otbn-build` emit a conventional RV32I library
    that other rules can depend on in their `deps`.
    """
    cc_toolchain = find_cc_toolchain(ctx)
    objs = [
        ctx.actions.declare_file(src.basename.replace("." + src.extension, ".o"))
        for src in ctx.files.srcs
    ]
    elf = ctx.actions.declare_file(ctx.attr.name + ".elf")
    rv32embed = ctx.actions.declare_file(ctx.attr.name + ".rv32embed.o")
    archive = ctx.actions.declare_file(ctx.attr.name + ".rv32embed.a")
    outputs = objs + [elf, rv32embed, archive]

    # Note: the toolchain config doesn"t appear to have a good way to get
    # access to the assembler.  We should be able to access it via the
    # the compiler, but I had trouble with //hw/ip/otbn/util/otbn-as invoking
    # the compiler as assembler.
    assembler = [f for f in cc_toolchain.all_files.to_list() if f.basename.endswith("as")][0]

    ctx.actions.run(
        outputs = outputs,
        inputs = (ctx.files.srcs +
                  cc_toolchain.all_files.to_list() +
                  ctx.files._otbn_as +
                  ctx.files._otbn_ld +
                  ctx.files._otbn_data +
                  ctx.files._wrapper),
        env = {
            "OTBN_AS": ctx.file._otbn_as.path,
            "OTBN_LD": ctx.file._otbn_ld.path,
            "RV32_TOOL_AS": assembler.path,
            "RV32_TOOL_AR": cc_toolchain.ar_executable,
            "RV32_TOOL_LD": cc_toolchain.ld_executable,
            "RV32_TOOL_OBJCOPY": cc_toolchain.objcopy_executable,
        },
        arguments = [
            "--app-name={}".format(ctx.attr.name),
            "--archive",
            "--out-dir={}".format(elf.dirname),
        ] + [src.path for src in ctx.files.srcs],
        executable = ctx.file._wrapper,
    )

    feature_configuration = cc_common.configure_features(
        ctx = ctx,
        cc_toolchain = cc_toolchain,
        requested_features = ctx.features,
        unsupported_features = ctx.disabled_features,
    )

    return [
        DefaultInfo(files = depset(outputs), data_runfiles = ctx.runfiles(files = outputs)),
        OutputGroupInfo(
            otbn_objs = depset(objs),
            elf = depset([elf]),
            rv32embed = depset([rv32embed]),
            archive = depset([archive]),
        ),
        # Emit a CcInfo provider so that this rule can be a dependency in other
        # cc_* rules.
        CcInfo(
            linking_context = cc_common.create_linking_context(
                linker_inputs = depset([cc_common.create_linker_input(
                    owner = ctx.label,
                    libraries = depset([cc_common.create_library_to_link(
                        actions = ctx.actions,
                        feature_configuration = feature_configuration,
                        cc_toolchain = cc_toolchain,
                        static_library = archive,
                    )]),
                )]),
            ),
        ),
    ]

otbn_binary = rule(
    implementation = _otbn_binary,
    cfg = opentitan_transition,
    attrs = {
        "srcs": attr.label_list(allow_files = True),
        "platform": attr.string(default = OPENTITAN_PLATFORM),
        "_cc_toolchain": attr.label(default = Label("@bazel_tools//tools/cpp:current_cc_toolchain")),
        "_otbn_as": attr.label(default = "//hw/ip/otbn/util:otbn-as", allow_single_file = True),
        "_otbn_ld": attr.label(default = "//hw/ip/otbn/util:otbn-ld", allow_single_file = True),
        "_otbn_data": attr.label(default = "//hw/ip/otbn/data:all_files", allow_files = True),
        "_wrapper": attr.label(default = "//util:otbn_build.py", allow_single_file = True),
        "_allowlist_function_transition": attr.label(
            default = "@bazel_tools//tools/allowlists/function_transition_allowlist",
        ),
    },
    fragments = ["cpp"],
    toolchains = ["@rules_cc//cc:toolchain_type"],
    incompatible_use_toolchain_transition = True,
)
