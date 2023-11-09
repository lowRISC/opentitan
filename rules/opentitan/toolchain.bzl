# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:host.bzl", "host_tools_transition")

LOCALTOOLS_TOOLCHAIN = "@lowrisc_opentitan//rules/opentitan:localtools_type"

LocalToolInfo = provider(fields = [
    "opentitantool",
    "gen_mem_image",
])

def _localtools_toolchain(ctx):
    tools = LocalToolInfo(
        opentitantool = ctx.attr.opentitantool[0].files_to_run,
        gen_mem_image = ctx.attr.gen_mem_image[0].files_to_run,
    )
    return platform_common.ToolchainInfo(
        name = ctx.label.name,
        tools = tools,
    )

localtools_toolchain = rule(
    implementation = _localtools_toolchain,
    attrs = {
        "opentitantool": attr.label(
            default = "//sw/host/opentitantool:opentitantool",
            executable = True,
            cfg = host_tools_transition,
        ),
        "gen_mem_image": attr.label(
            default = "//hw/ip/rom_ctrl/util:gen_vivado_mem_image",
            executable = True,
            cfg = host_tools_transition,
        ),
        "_allowlist_function_transition": attr.label(
            default = "@bazel_tools//tools/allowlists/function_transition_allowlist",
        ),
    },
    doc = "Toolchain for local in-tree tools",
    provides = [platform_common.ToolchainInfo],
)
