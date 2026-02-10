# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:providers.bzl",
    "SiliconBinaryInfo",
    "get_binary_files",
)

_TEST_SCRIPT = """\
set -eu

{generate_coverage_view} \
  --elf="{elf_file}" \
  --kind="{kind}" \
  --output="$COVERAGE_OUTPUT_FILE" \
  --temp-dir="$TEST_UNDECLARED_OUTPUTS_DIR" \
"""

def _coverage_view_test(ctx):
    # This suffix is required to distinguish the coverage view LCOV files from
    # the coverage data of other tests.
    if not ctx.label.name.endswith("_coverage_view"):
        fail("The name of the coverage_view_test rule must end with '_coverage_view'")

    elf_label = ctx.attr.elf
    groups = elf_label.output_groups

    if "silicon_creator_elf" in groups:
        elf_list = groups["silicon_creator_elf"].to_list()
    elif "elf" in ctx.attr.elf.output_groups:
        elf_list = groups["elf"].to_list()
    else:
        elf_list = get_binary_files(elf_label, field = "elf", providers = [SiliconBinaryInfo])

    if len(elf_list) != 1:
        fail("The target must have exactly one elf file.")
    elf = elf_list[0]

    runfiles = ctx.runfiles()

    # Coverage view tests are only applicable when coverage is enabled.
    if ctx.var.get("ot_coverage_enabled", "false") == "true":
        runfiles = runfiles.merge(ctx.runfiles(files = [elf]))
        runfiles = runfiles.merge(ctx.attr._generate_coverage_view[DefaultInfo].default_runfiles)

        script_content = _TEST_SCRIPT.format(
            generate_coverage_view = ctx.executable._generate_coverage_view.short_path,
            elf_file = elf.short_path,
            kind = ctx.attr.kind,
        )
    else:
        script_content = ""

    script = ctx.actions.declare_file(ctx.label.name + ".sh")
    ctx.actions.write(
        output = script,
        content = script_content,
        is_executable = True,
    )

    return DefaultInfo(
        executable = script,
        runfiles = runfiles,
    )

coverage_view_test = rule(
    implementation = _coverage_view_test,
    attrs = {
        "elf": attr.label(
            allow_files = True,
            doc = "ELF file to extract coverage view",
        ),
        "kind": attr.string(
            doc = "Kind of given elf file",
            default = "ibex",
            values = ["ibex", "otbn"],
        ),
        "_generate_coverage_view": attr.label(
            default = "//util/coverage/collect_cc_coverage:generate_coverage_view",
            executable = True,
            cfg = "exec",
        ),
    },
    fragments = ["cpp"],
    test = True,
)
