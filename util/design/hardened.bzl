# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:providers.bzl",
    "get_binary_files",
)

_TEST_SCRIPT = """\
#!/bin/bash
exec {tool} {disassemblies}
"""

def _hardened_comparison_test_impl(ctx):
    """Implementation of the hardened_comparison_test rule."""

    check_tool = ctx.executable._check_tool
    disassemblies = get_binary_files(ctx.attr.srcs, field = "disassembly")
    test_script = ctx.actions.declare_file(ctx.label.name + ".sh")

    script_content = _TEST_SCRIPT.format(
        tool = check_tool.short_path,
        disassemblies = " ".join([f.short_path for f in disassemblies]),
    )

    ctx.actions.write(
        output = test_script,
        content = script_content,
        is_executable = True,
    )

    return [
        DefaultInfo(
            executable = test_script,
            runfiles = ctx.runfiles(files = disassemblies).merge(
                ctx.attr._check_tool[DefaultInfo].default_runfiles,
            ),
        ),
    ]

hardened_comparison_test = rule(
    implementation = _hardened_comparison_test_impl,
    attrs = {
        "srcs": attr.label_list(
            mandatory = True,
            doc = "Targets (e.g., opentitan_binary) whose disassembly files will be scanned.",
        ),
        "_check_tool": attr.label(
            default = "//util/design:check-hardened-comparison",
            executable = True,
            cfg = "exec",
            doc = "The underlying python script that performs the regex analysis.",
        ),
    },
    test = True,
    doc = """
        Defines a test that scans disassembly files for compiler optimizations
         that break hardening.

        Specifically, it looks for RISC-V branch instructions where both
        source registers are identical (e.g., `beq a0, a0, ...`), which
        suggests a hardened comparison was simplified into a nop or an
        unconditional jump.
    """,
)
