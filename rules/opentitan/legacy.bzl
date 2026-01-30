# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "@lowrisc_opentitan//rules/opentitan:transform.bzl",
    "convert_to_vmem",
    "scramble_flash",
    _obj_transform = "obj_transform",
)
load("@lowrisc_opentitan//rules:rv.bzl", "rv_rule")
load("@lowrisc_opentitan//rules/opentitan:defs.bzl", "exec_env_to_top_map")
load(
    "@lowrisc_opentitan//hw/top:defs.bzl",
    "opentitan_select_top",
)

def legacy_rom_targets(target, suffixes, testonly = False):
    """Create filegroups for legacy ROM rule target names.

    For each `<suffix>` (i.e. key in the `exec_env` argument), a target
    `<name>_<suffix>` will be created which extracts from `target` the relevant
    files. An alias `<name>_<suffix>_scr_vmem` will also be created. The values
    in the `exec_env` dictionary must be lists of execution environment label-strings.
    For each key (suffix), one or more execution environment can be listed and this
    macros will automatically select() the right one based on the selected top.

    Args:
      target: The name of the new `opentitan_binary` ROM target.
      suffix: A map from suffixes (strings) to list of execution environments.
    """

    # Filter execution environments by top.
    ev_map = exec_env_to_top_map([ev for ev_list in suffixes.values() for ev in ev_list])

    for (suffix, ev_list) in suffixes.items():
        valid_tops = [ev_map[ev] for ev in ev_list]

        native.filegroup(
            name = "{}_{}".format(target, suffix),
            srcs = [":{}".format(target)],
            output_group = select({
                "@lowrisc_opentitan//sw/device:is_english_breakfast": "{}_rom32".format(suffix),
                "@lowrisc_opentitan//conditions:default": "{}_rom".format(suffix),
            }),
            testonly = testonly,
            target_compatible_with = opentitan_select_top(
                {
                    top: []
                    for top in valid_tops
                },
                ["@platforms//:incompatible"],
            ),
        )
        native.alias(
            name = "{}_{}_scr_vmem".format(target, suffix),
            actual = ":{}_{}".format(target, suffix),
            testonly = testonly,
        )

def _obj_transform_impl(ctx):
    outputs = [_obj_transform(ctx)]
    return [
        DefaultInfo(
            files = depset(outputs),
            data_runfiles = ctx.runfiles(files = outputs),
        ),
    ]

obj_transform = rv_rule(
    implementation = _obj_transform_impl,
    attrs = {
        "src": attr.label(allow_single_file = True),
        "suffix": attr.string(default = "bin"),
        "format": attr.string(default = "binary"),
        "_cc_toolchain": attr.label(default = Label("@bazel_tools//tools/cpp:current_cc_toolchain")),
    },
    fragments = ["cpp"],
    toolchains = ["@rules_cc//cc:toolchain_type"],
)

def _vmem_file_impl(ctx):
    outputs = [convert_to_vmem(ctx)]
    return [
        DefaultInfo(
            files = depset(outputs),
            data_runfiles = ctx.runfiles(files = outputs),
        ),
    ]

vmem_file = rv_rule(
    implementation = _vmem_file_impl,
    attrs = {
        "src": attr.label(
            allow_single_file = True,
            doc = "Binary file to convert to vmem format",
        ),
        "word_size": attr.int(
            default = 64,
            doc = "Word size of VMEM file",
            mandatory = True,
            values = [32, 64],
        ),
    },
)

def _scramble_flash_vmem_impl(ctx):
    outputs = [scramble_flash(ctx, suffix = "src.vmem")]
    return [
        DefaultInfo(
            files = depset(outputs),
            data_runfiles = ctx.runfiles(files = outputs),
        ),
    ]

scramble_flash_vmem = rv_rule(
    implementation = _scramble_flash_vmem_impl,
    attrs = {
        "src": attr.label(allow_single_file = True),
        "otp": attr.label(allow_single_file = True),
        "top_secret_cfg": attr.label(
            allow_single_file = True,
            default = "@lowrisc_opentitan//hw/top:secrets",
            doc = "Generated top configuration file including secrets.",
        ),
        "otp_data_perm": attr.label(
            default = "@lowrisc_opentitan//util/design/data:data_perm",
            doc = "Option to indicate OTP VMEM file bit layout.",
        ),
        "_tool": attr.label(
            default = "@lowrisc_opentitan//util/design:gen-flash-img",
            executable = True,
            cfg = "exec",
        ),
    },
)
