# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//lib:dicts.bzl", "dicts")
load("@nonhermetic//:env.bzl", "BIN_PATHS", "ENV")
load("@rules_pkg//pkg:tar.bzl", "pkg_tar")

"""Rules for running FuseSoC.

FuseSoC is a package manager and set of build tools for HDL code.

Because we want the output of some FuseSoC built resources to be
available to bazel (such as the verilated chip model for running
tests), the `fusesoc_build` rule allows bazel to delegate certain
targets to FuseSoC.

This rule is not fully hermetic, as our current configuration depends
verible, verilator, etc already having been installed.
"""

load("@bazel_skylib//rules:common_settings.bzl", "BuildSettingInfo")

def _corefiles2rootarg(core):
    return core.dirname

FUSESOC_BUILD_COMMAND = """
# Copy output of the setup step to the build directory.
cp -ra "$FUSESOC_SETUP_OUT_DIR"/. "$FUSESOC_BUILD_OUT_DIR"
# Build everything.
make -C "$FUSESOC_BUILD_OUT_DIR"
"""

def _fusesoc_build_impl(ctx):
    # TODO(#27346): Use of `/tmp` here isn't hermetic.
    cache_dir = "/tmp/fusesoc-cache"
    cfg_file_path = "{}.fusesoc_config.toml".format(ctx.label.name)
    cfg_file = ctx.actions.declare_file(cfg_file_path)
    cfg_str = "[main]\n  cache_root = {}".format(cache_dir)
    ctx.actions.write(cfg_file, cfg_str)

    # Setup stage: we first run FuseSoC to create a build directory containing all files
    # which are really needed. This directory will be the output of the first FuseSoC action.
    setup_work_dir = ctx.actions.declare_directory("{}.setup".format(ctx.label.name))
    setup_flags = [ctx.expand_location(f, ctx.attr.srcs) for f in ctx.attr.flags]
    if ctx.attr.verilator_options:
        verilator_options = ctx.attr.verilator_options[BuildSettingInfo].value
        setup_flags.append("--verilator_options={}".format(" ".join(verilator_options)))

    if ctx.attr.make_options:
        make_options = ctx.attr.make_options[BuildSettingInfo].value
        setup_flags.append("--make_options={}".format(" ".join(make_options)))

    setup_args = ctx.actions.args()
    setup_args.add(cfg_file.path, format = "--config=%s")
    setup_args.add_all(
        ctx.files.cores,
        uniquify = True,
        map_each = _corefiles2rootarg,
        format_each = "--cores-root=%s",
    )
    setup_args.add("run")
    setup_args.add(ctx.attr.target, format = "--target=%s")
    setup_args.add("--setup")
    setup_args.add(setup_work_dir.path, format = "--work-root=%s")
    setup_args.add_all(ctx.attr.systems)
    setup_args.add_all(setup_flags)

    ctx.actions.run(
        mnemonic = "FuseSoC",
        outputs = [setup_work_dir],
        inputs = ctx.files.srcs + ctx.files.cores + ctx.files._fusesoc + [
            cfg_file,
        ],
        arguments = [setup_args],
        executable = ctx.executable._fusesoc,
        use_default_shell_env = False,
    )

    # Build stage: we now take as input the build directory created by the setup stage and run
    # the actual build. There is a small difficulty: since the build directory created above is
    # a declare directory, it cannot be changed so we can't just use that as the build directory.
    # Instead, we need to create a new one and copy the content before running FuseSoc.

    # Vivado expects `HOME` environment variable to exist. Redirect it to a fake directory.
    build_work_dir_name = "{}.build".format(ctx.label.name)

    # Trick to get the path of the directory.
    empty_file_for_bazel = ctx.actions.declare_file(build_work_dir_name + "/.empty_file_for_bazel")
    ctx.actions.write(empty_file_for_bazel, "")
    build_work_dir = empty_file_for_bazel.dirname
    build_home_dir = "{}/homeless-shelter".format(setup_work_dir.path)

    groups = {
        "files": depset([setup_work_dir]),
    }
    outputs = []
    for group, files in ctx.attr.output_groups.items():
        # If hashing only, ignore all output groups but one.
        if ctx.attr.files_to_hash_only and group != "files_to_hash":
            continue

        deps = []
        for file in files:
            path = "{}/{}".format(build_work_dir_name, file)
            if file.endswith("/"):
                deps.append(ctx.actions.declare_directory(path))
            else:
                deps.append(ctx.actions.declare_file(path))
        outputs.extend(deps)
        groups[group] = depset(deps)

    ctx.actions.run_shell(
        mnemonic = "FuseSoC",
        outputs = outputs,
        inputs = [setup_work_dir] + ctx.files._fusesoc + [
            cfg_file,
        ],
        command = FUSESOC_BUILD_COMMAND,
        arguments = ["CXX=g++"],
        use_default_shell_env = False,
        env = dicts.add(
            # Verilator build doesn't need nonhermetic environment variables
            ENV if ctx.attr.target == "synth" else {},
            {
                "HOME": build_home_dir,
                # Obtain the non-hermetic binary path and append Bazel's default PATH.
                "PATH": BIN_PATHS["vivado" if ctx.attr.target == "synth" else "verilator"] + ":/bin:/usr/bin:/usr/local/bin",
                "FUSESOC_SETUP_OUT_DIR": setup_work_dir.path,
                "FUSESOC_BUILD_OUT_DIR": build_work_dir,
            },
        ),
    )

    return [
        DefaultInfo(
            files = depset(outputs),
            data_runfiles = ctx.runfiles(files = outputs + ctx.files.data),
        ),
        OutputGroupInfo(**groups),
    ]

fusesoc_build = rule(
    implementation = _fusesoc_build_impl,
    attrs = {
        "cores": attr.label_list(allow_files = True, doc = "FuseSoC core specification files"),
        "srcs": attr.label_list(allow_files = True, doc = "Source files"),
        "data": attr.label_list(allow_files = True, doc = "Files needed at runtime"),
        "target": attr.string(mandatory = True, doc = "Target name (e.g. 'sim')"),
        "systems": attr.string_list(mandatory = True, doc = "Systems to build"),
        "flags": attr.string_list(doc = "Flags controlling the FuseSOC system build"),
        "output_groups": attr.string_list_dict(
            allow_empty = True,
            doc = """
                Mappings from output group names to lists of paths contained in
                that group.

                Paths to directories must have a trailing `/`. It is not
                possible to output both a directory and a file from within that
                directory.
            """,
        ),
        "files_to_hash_only": attr.bool(
            default = False,
            doc = "If set, only --setup will be passed to fusesoc and only the files_to_hash output group will be emitted",
        ),
        "verilator_options": attr.label(),
        "make_options": attr.label(),
        "_fusesoc": attr.label(
            default = "//util:fusesoc_build",
            executable = True,
            cfg = "exec",
        ),
    },
)

def fusesoc_hash_and_build(
        name,
        # All other attributes of fusesoc_build
        **kwargs):
    """
    This rule is similar to fusesoc_build but in addition, it will also create a target named
    `{name}_hash` containing the hash of all input files listed by fusesoc. The output group `files_to_hash`
    must contain the list of files/directories in the fusesoc build directory which need to be hashed.
    """
    testonly = kwargs.get("testonly", False)
    fusesoc_build(
        name = name,
        **kwargs
    )
    native.filegroup(
        name = name + "_files",
        srcs = [":" + name],
        output_group = "files",
        testonly = testonly,
    )
    pkg_tar(
        name = name + "_files_tar",
        srcs = [":{}_files".format(name)],
        testonly = testonly,
    )
    tar = ":" + name + "_files_tar"
    native.genrule(
        name = name + "_hash",
        srcs = [tar],
        outs = [name + ".hash"],
        cmd = "sha1sum $(location {}) | cut -d\\  -f 1 > $@".format(tar),
        testonly = testonly,
    )
