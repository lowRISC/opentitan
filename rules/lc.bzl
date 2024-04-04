# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Rules for generating lc_ctrl netlist constants used in SW."""

load("@bazel_skylib//rules:common_settings.bzl", "BuildSettingInfo")

def _lc_raw_unlock_token_impl(ctx):
    output = ctx.actions.declare_file("src/" + ctx.attr.name + ".rs")
    args = ctx.actions.args()
    args.add(
        "--lc-state-def-file",
        ctx.file.lc_state_def,
    )
    args.add(
        "--raw-unlock-rs-template",
        ctx.file.src,
    )
    args.add(
        "--raw-unlock-rs-output",
        output,
    )
    args.add(
        "--seed",
        ctx.attr.lc_seed[BuildSettingInfo].value,
    )
    ctx.actions.run(
        outputs = [output],
        inputs = [
            ctx.file.lc_state_def,
            ctx.file.src,
        ],
        arguments = [args],
        executable = ctx.executable._tool,
    )
    return [DefaultInfo(files = depset([output]), runfiles = ctx.runfiles(files = [output]))]

lc_raw_unlock_token = rule(
    implementation = _lc_raw_unlock_token_impl,
    attrs = {
        "src": attr.label(
            allow_single_file = [".rs.tpl"],
            default = "//sw/device/silicon_creator/manuf/data:lc_raw_unlock_token.rs.tpl",
            doc = "Life-cycle state definition file in Hjson format.",
        ),
        "lc_state_def": attr.label(
            allow_single_file = True,
            default = "//hw/ip/lc_ctrl/data:lc_ctrl_state.hjson",
            doc = "Life-cycle state definition file in Hjson format.",
        ),
        "lc_raw_unlock_rust_template": attr.label(
            allow_single_file = True,
            default = "//sw/device/silicon_creator/manuf/data:lc_raw_unlock_token.rs.tpl",
            doc = "Life-cycle state definition file in Hjson format.",
        ),
        "lc_seed": attr.label(
            default = "//hw/ip/otp_ctrl/data:lc_seed",
            doc = "Configuration override seed used to randomize LC netlist constants.",
        ),
        "_tool": attr.label(
            default = "//util/design:gen-lc-state-enc",
            executable = True,
            cfg = "exec",
        ),
    },
)
