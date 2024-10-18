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

def legacy_rom_targets(target, suffixes, testonly = False):
    """Create filegroups for legacy ROM rule target names.

    Creates the `<name>_rom` and `<name>_scr_vmem` targets required by the
    `opentitan_functest` macro.

    Args:
      target: The name of the new `opentitan_binary` ROM target.
      targets: The suffix names to use when creating filegroups.
    """
    for suffix in suffixes:
        native.filegroup(
            name = "{}_{}".format(target, suffix),
            srcs = [":{}".format(target)],
            output_group = select({
                "//sw/device:is_english_breakfast": "{}_rom32".format(suffix),
                "//conditions:default": "{}_rom".format(suffix),
            }),
            testonly = testonly,
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
        "otp_mmap": attr.label(
            allow_single_file = True,
            default = "//hw/ip/otp_ctrl/data:otp_ctrl_mmap.hjson",
            doc = "OTP memory map configuration HJSON file.",
        ),
        "otp_seed": attr.label(
            default = "//hw/ip/otp_ctrl/data:otp_seed",
            doc = "Configuration override seed used to randomize OTP netlist constants.",
        ),
        "otp_data_perm": attr.label(
            default = "//hw/ip/otp_ctrl/data:data_perm",
            doc = "Option to indicate OTP VMEM file bit layout.",
        ),
        "_tool": attr.label(
            default = "@//util/design:gen-flash-img",
            executable = True,
            cfg = "exec",
        ),
    },
)
