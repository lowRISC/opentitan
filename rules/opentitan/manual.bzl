# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

def _opentitan_manual_test_impl(ctx):
    executable = ctx.actions.declare_file("manual_test_wrapper")
    ctx.actions.write(
        output = executable,
        content = "{runner} {testplan}".format(
            runner = ctx.executable._runner.short_path,
            testplan = ctx.file.testplan.short_path,
        ),
    )
    return [
        DefaultInfo(
            runfiles = ctx.runfiles(
                files = [
                    ctx.executable._runner,
                    ctx.file.testplan,
                ],
            ).merge(ctx.attr._runner[DefaultInfo].default_runfiles),
            executable = executable,
        ),
    ]

opentitan_manual_test = rule(
    _opentitan_manual_test_impl,
    attrs = {
        "testplan": attr.label(
            allow_single_file = [".hjson"],
            doc = "Testplan with manual testpoints",
            mandatory = True,
        ),
        "_runner": attr.label(
            default = "//util:run_manual_tests",
            executable = True,
            cfg = "exec",
        ),
    },
    doc = "Walks through the manual testpoints in a testplan",
    test = True,
)
