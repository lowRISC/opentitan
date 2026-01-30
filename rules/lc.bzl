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
        "--top-secret-cfg",
        ctx.file.top_secret_cfg,
    )
    ctx.actions.run(
        outputs = [output],
        inputs = [
            ctx.file.lc_state_def,
            ctx.file.src,
            ctx.file.top_secret_cfg,
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
            default = "@lowrisc_opentitan//sw/device/silicon_creator/manuf/data:lc_raw_unlock_token.rs.tpl",
            doc = "Life-cycle state definition file in Hjson format.",
        ),
        "lc_state_def": attr.label(
            allow_single_file = True,
            default = "@lowrisc_opentitan//hw/ip/lc_ctrl/data:lc_ctrl_state.hjson",
            doc = "Life-cycle state definition file in Hjson format.",
        ),
        "lc_raw_unlock_rust_template": attr.label(
            allow_single_file = True,
            default = "@lowrisc_opentitan//sw/device/silicon_creator/manuf/data:lc_raw_unlock_token.rs.tpl",
            doc = "Life-cycle state definition file in Hjson format.",
        ),
        "top_secret_cfg": attr.label(
            allow_single_file = True,
            default = "@lowrisc_opentitan//hw/top:secrets",
            doc = "Generated top configuration file including secrets.",
        ),
        "_tool": attr.label(
            default = "@lowrisc_opentitan//util/design:gen-lc-state-enc",
            executable = True,
            cfg = "exec",
        ),
    },
)
