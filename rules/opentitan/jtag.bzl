# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@lowrisc_opentitan//rules/opentitan:exec_env.bzl", "ExecEnvInfo")
load("@lowrisc_opentitan//rules/opentitan:util.bzl", "get_fallback", "get_override")
load("@bazel_skylib//lib:shell.bzl", "shell")

_COMMAND = """#!/bin/bash

{opentitantool} --rcfile= --interface={interface} {setup} no-op

{openocd} \
    -f {adapter_config} \
    {openocd_commands} \
    -f {chip_config} \
"""

def _jtag_server(ctx):
    exec_env = ctx.attr.exec_env[ExecEnvInfo]
    adapter_config = get_fallback(ctx, "attr.openocd_adapter_config", exec_env)
    adapter_config = adapter_config.files.to_list()
    if len(adapter_config) != 1:
        fail("Expected only one file for openocd_adapter_config")
    adapter_config = adapter_config[0]

    setup = ["--exec={}".format(shell.quote(s)) for s in ctx.attr.chip_setup]
    commands = ["-c {}".format(shell.quote(c)) for c in ctx.attr.openocd_commands]

    file = ctx.actions.declare_file("{}.sh".format(ctx.attr.name))
    script = _COMMAND.format(
        opentitantool = exec_env._opentitantool.executable.short_path,
        interface = exec_env.param["interface"],
        setup = " ".join(setup),
        openocd = exec_env.openocd.files_to_run.executable.short_path,
        adapter_config = adapter_config.short_path,
        openocd_commands = " ".join(commands),
        chip_config = ctx.file.openocd_chip_config.short_path,
    )
    ctx.actions.write(
        output = file,
        content = script,
        is_executable = True,
    )

    return DefaultInfo(
        executable = file,
        runfiles = ctx.runfiles(files = [
            exec_env._opentitantool.executable,
            exec_env.openocd.files_to_run.executable,
            adapter_config,
            ctx.file.openocd_chip_config,
        ]),
    )

jtag_server = rule(
    implementation = _jtag_server,
    attrs = {
        "exec_env": attr.label(
            providers = [ExecEnvInfo],
            doc = "List of exeuction environments for this target.",
        ),
        "chip_setup": attr.string_list(
            doc = "OpenTitanTool commands to configure the chip for JTAG",
        ),
        "openocd_adapter_config": attr.label(
            allow_single_file = True,
            doc = "OpenOCD adapter configuration override",
        ),
        "openocd_chip_config": attr.label(
            allow_single_file = True,
            doc = "OpenOCD chip configuration override",
        ),
        "openocd_commands": attr.string_list(
            doc = "OpenOCD commands to execute",
        ),
    },
    executable = True,
    doc = "Configure a chip for jtag and spawn an OpenOCD server process",
)
