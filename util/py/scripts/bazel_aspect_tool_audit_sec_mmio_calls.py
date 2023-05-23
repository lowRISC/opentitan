# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Audit calls to sec_mmio_* functions within a single translation unit.

This script is meant to be invoked by a Bazel aspect. To generate a report,
users should run audit_sec_mmio_calls.py.

For context, see <https://github.com/lowRISC/opentitan/issues/18634>.
"""

import subprocess
import sys
from pathlib import Path

import clang.cindex

from util.py.packages.lib.register_usage_report import CallSiteAnalyzer
from util.py.packages.lib.register_usage_report import \
    RegisterTokenPattern as TokPat
from util.py.packages.lib.register_usage_report import RegisterUsageReportGroup

# Define analyzers for each of the sec_mmio_* functions we care about. We give
# each analyzer a list of token patterns where None is a stand-in for a register
# offset.
#
# If the list of token patterns is incomplete, we will fail the Bazel build by
# raising an uncaught exception.
#
# NOTE: This list is likely to become out of date as the codebase evolves.
SEC_MMIO_FUNCTION_ANALYZERS = [
    CallSiteAnalyzer(
        function_name="sec_mmio_read32",
        arg_index=0,
        reg_token_patterns=[
            TokPat('kBase + reg_offset + sizeof ( uint32_t )'.split()),
            TokPat('kBase + reg_offset + i * sizeof ( uint32_t )'.split()),
            TokPat(['kBase', '+', None, '+', 'address']),
            TokPat([
                'kBase', '+', None, '+', 'i', '*', 'sizeof', '(', 'uint32_t',
                ')'
            ]),
            TokPat(['kBase', '+', None]),
            TokPat(['info_page', '->', 'cfg_addr']),
        ]),
    CallSiteAnalyzer(function_name="sec_mmio_write32",
                     arg_index=0,
                     reg_token_patterns=[
                         TokPat(['cfg_addr']),
                         TokPat([
                             'kBase', '+', None, '+', 'i', '*', 'sizeof', '(',
                             'uint32_t', ')'
                         ]),
                         TokPat(['kBase', '+', None]),
                         TokPat(['kPwrMgrBase', '+', None]),
                         TokPat(['regs', '.', 'cfg_addr']),
                         TokPat(['regs', '.', 'cfg_wen_addr']),
                         TokPat(['info_page', '->', 'cfg_addr']),
                         TokPat(['info_page', '->', 'cfg_wen_addr']),
                     ]),
    CallSiteAnalyzer(function_name="sec_mmio_write32_shadowed",
                     arg_index=0,
                     reg_token_patterns=[
                         TokPat(['kBase', '+', None]),
                     ])
]


def main():
    generated_file = Path(sys.argv[1])
    source_file = Path(sys.argv[2])
    clang_args = sys.argv[3:]

    assert not generated_file.exists()
    assert source_file.exists()

    index = clang.cindex.Index.create()

    try:
        translation_unit = index.parse(source_file, args=clang_args)
    except clang.cindex.TranslationUnitLoadError as e:
        # Something went wrong inside of libclang, but it is not forthcoming
        # with details. Manually run `clang` and hope that it produces a more
        # helpful error message.
        command = ["clang"] + clang_args + [source_file]
        print("command:", command)
        subprocess.run(command, check=True)

        raise Exception(f"Failed to process {source_file}") from e

    # Run each call-site analyzer and accumulate the results.
    report_group = RegisterUsageReportGroup(reports={})
    for analyzer in SEC_MMIO_FUNCTION_ANALYZERS:
        report = analyzer.run(translation_unit.cursor)
        if report is None:
            continue
        report_group.reports[analyzer.function_name] = report

    # Serialize the report group and write it to the output file.
    report_group_bytes = report_group.serialize()
    generated_file.write_bytes(report_group_bytes)


if __name__ == "__main__":
    main()
