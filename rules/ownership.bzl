# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

def _owner_block_binary_impl(ctx):
    output = ctx.attr.output
    if not output:
        output = ctx.attr.name + ".bin"
    out_bin = ctx.actions.declare_file(output)
    inputs = [ctx.file.src] + ctx.files.keys

    command = "set -euo pipefail"

    # Handle relative_to if provided
    if ctx.attr.relative_to:
        relative_to_files = ctx.attr.relative_to.files.to_list()
        if not relative_to_files:
            fail("relative_to target has no files")
        ref_file = relative_to_files[0]
        workspace_root = ref_file.owner.workspace_root

        if workspace_root:
            command += """
            WORKSPACE_ROOT="{workspace_root}"
            if [ -n "$WORKSPACE_ROOT" ]; then
              for f in $WORKSPACE_ROOT/*; do
                name=$(basename "$f")
                if [ ! -e "$name" ]; then
                  ln -s "$f" "$name"
                fi
              done
            fi
            """.format(workspace_root = workspace_root)
            inputs.append(ref_file)

    command += """
    {opentitantool} --rcfile= \
        ownership config --input {input} {output}
    """.format(
        opentitantool = ctx.executable.opentitantool.path,
        input = ctx.file.src.path,
        output = out_bin.path,
    )

    ctx.actions.run_shell(
        inputs = inputs,
        outputs = [out_bin],
        command = command,
        tools = [ctx.executable.opentitantool],
        use_default_shell_env = True,
        mnemonic = "OwnerBlockGen",
        progress_message = "Generating owner block binary %s" % ctx.attr.name,
    )

    return [DefaultInfo(files = depset([out_bin]))]

owner_block_binary = rule(
    implementation = _owner_block_binary_impl,
    attrs = {
        "src": attr.label(allow_single_file = True, mandatory = True),
        "keys": attr.label_list(allow_files = True),
        "output": attr.string(doc = "Optional output filename"),
        "relative_to": attr.label(allow_single_file = True),
        "opentitantool": attr.label(
            default = Label("//sw/host/opentitantool"),
            executable = True,
            cfg = "exec",
        ),
    },
)

def _bin2c_impl(ctx):
    out_c = ctx.actions.declare_file(ctx.attr.name + ".c")

    ctx.actions.run(
        inputs = [ctx.file.src, ctx.file._hexdump_config],
        outputs = [out_c],
        executable = ctx.executable._bin2c_tool,
        arguments = [
            "--input",
            ctx.file.src.path,
            "--output",
            out_c.path,
            "--name",
            ctx.attr.var_name,
        ],
        mnemonic = "Bin2C",
        progress_message = "Converting binary %s to C" % ctx.file.src.basename,
    )
    return [DefaultInfo(files = depset([out_c]))]

bin2c = rule(
    implementation = _bin2c_impl,
    attrs = {
        "src": attr.label(allow_single_file = True, mandatory = True),
        "var_name": attr.string(mandatory = True),
        "_bin2c_tool": attr.label(
            default = Label("//util/sh/scripts:bin2c.sh"),
            executable = True,
            allow_single_file = True,
            cfg = "exec",
        ),
        "_hexdump_config": attr.label(
            default = Label("//util/sh/scripts:c.hexdump"),
            allow_single_file = True,
        ),
    },
)
