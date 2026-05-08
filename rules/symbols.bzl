# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Rules for inspecting symbols in ELF files"""

load("//rules:rv.bzl", "rv_rule")
load("//rules/opentitan:providers.bzl", "OpenTitanBinaryInfo")
load("//rules/opentitan:transform.bzl", "obj_list_symbols")

CHECK_SYMBOLS_SCRIPT = """#!/bin/bash
set -e

function check_file() {{
    # $1: elf file
    # $2: sym file
    if cat "$2" | awk '{{ print($3) }}' | grep -E "^({forbidden_syms})$"
    then
        echo "$1 contains some forbidden symbols"
        exit 1
    fi
}}

{checks}
"""

def _check_elf_symbols(ctx):
    if OpenTitanBinaryInfo in ctx.attr.target:
        ot_info = ctx.attr.target[OpenTitanBinaryInfo]

        # For each execution environment, look at the corresponding provider and
        # extract the elf.
        elfs = [
            getattr(ctx.attr.target[prov], "elf")
            for prov in ot_info.exec_env
        ]
    else:
        elfs = ctx.attr.target[DefaultInfo].files.to_list()

    # For each elf file, we use nm to list the symbols.
    syms = {}
    for elf in elfs:
        syms[elf] = obj_list_symbols(
            ctx,
            src = elf,
            output = "{}_{}.nm".format(ctx.attr.name, elf.basename),
        )

    executable = ctx.actions.declare_file(ctx.attr.name + ".sh")
    ctx.actions.write(
        executable,
        CHECK_SYMBOLS_SCRIPT.format(
            checks = "\n".join([
                "check_file \"{}\" \"{}\"".format(elf.short_path, sym.short_path)
                for (elf, sym) in syms.items()
            ]),
            forbidden_syms = "|".join(ctx.attr.forbidden),
        ),
    )

    return [
        DefaultInfo(executable = executable, runfiles = ctx.runfiles(syms.values())),
    ]

check_elf_symbols_test = rv_rule(
    implementation = _check_elf_symbols,
    test = True,
    attrs = {
        "target": attr.label(
            mandatory = True,
            doc = "Target on which to check the symbols. If the target has an OpenTitanBinaryInfo provider, the elf file of every execution environent will be checked. Otherwise every file in the DefaultInfo provider will be checked",
        ),
        "forbidden": attr.string_list(
            doc = "List of symbols which must not appear in the ELF file(s)",
        ),
        "_cc_toolchain": attr.label(default = Label("@bazel_tools//tools/cpp:current_cc_toolchain")),
    },
    fragments = ["cpp"],
    toolchains = ["@rules_cc//cc:toolchain_type"],
)
