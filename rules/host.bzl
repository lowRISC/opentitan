# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Transition rules for accessing the host platform

This file contains transition rules for accessing the host platform's
configuration. Primarily, this provides transitions for rules where a tool runs
on the host but the target configuration is not the host. For rules where
the host configuration is not adequate, toolchains should be used instead.
"""

def _host_tools_transition_impl(settings, attr):
    """Returns a dictionary with the platforms command line option set to host.

    This transition is used for building host tools, passing through all build
    settings specified on the command line.
    """
    ret = {
        "//command_line_option:platforms": "@local_config_platform//:host",
        "//command_line_option:copt": settings["//command_line_option:copt"],
        "//command_line_option:features": settings["//command_line_option:features"],
        # WARNING This is a horrible hack: when we transition to host, we pretend
        # that this is earlgrey so opentitantool can compile...
        "//hw/top": "earlgrey",
    }
    return ret

host_tools_transition = transition(
    implementation = _host_tools_transition_impl,
    inputs = [
        "//command_line_option:copt",
        "//command_line_option:features",
    ],
    outputs = [
        "//command_line_option:platforms",
        "//command_line_option:copt",
        "//command_line_option:features",
        "//hw/top",
    ],
)

def _host_tool_impl(ctx):
    default_info = ctx.attr.target[0][DefaultInfo]
    new_executable = ctx.actions.declare_file(ctx.attr.name)

    # The executable returned by a rule must always be created by that rule so create a symlink to work around it.
    ctx.actions.symlink(
        output = new_executable,
        target_file = default_info.files_to_run.executable,
        is_executable = True,
    )

    runfiles = default_info.default_runfiles.merge(ctx.runfiles([new_executable], transitive_files = default_info.files))

    return [
        DefaultInfo(
            files = depset(direct = [new_executable]),
            runfiles = runfiles,
            executable = new_executable,
        ),
    ]

host_tool = rule(
    implementation = _host_tool_impl,
    attrs = {
        "target": attr.label(
            allow_files = True,
            executable = True,
            mandatory = True,
            cfg = host_tools_transition,
        ),
        "_allowlist_function_transition": attr.label(
            default = "@bazel_tools//tools/allowlists/function_transition_allowlist",
        ),
    },
    doc = """Create an alias for a target and apply the host tools transition.
    This transition is used for building host tools, passing through all build
    settings specified on the command line.
    """,
    executable = True,
)
