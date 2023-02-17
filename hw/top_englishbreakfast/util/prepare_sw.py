#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Script to patch the OpenTitan tree for building english-breakfast-friendly
software.

This script and its associated mechanism will eventually be transitioned to
a pure-Bazel solution.
"""

import argparse
import shutil
import subprocess
from pathlib import Path

# This file is in /hw/top_.../util
REPO_TOP = Path(__file__).resolve().parents[3]

BINARIES = [
    'sw/device/lib/testing/test_rom/test_rom_export_fpga_cw305',
    'sw/device/sca/aes_serial_export_fpga_cw305',
    'sw/device/lib/testing/test_rom/test_rom_export_sim_verilator',
    'sw/device/tests/aes_smoketest_export_sim_verilator',
    'sw/device/examples/hello_world/hello_world_export_sim_verilator',
]

BAZEL_BINARIES = [
    '//sw/device/lib/testing/test_rom',
    '//sw/device/sca:aes_serial',
    '//sw/device/tests:aes_smoketest_prog',
    '//sw/device/examples/hello_world',
]


def find_dirs(root, names):
    """
    Finds all directories under `root` with the given name and
    yields them.
    """
    for p in root.iterdir():
        if not p.is_dir():
            continue
        if p.name in names:
            yield p
        else:
            find_dirs(p, names)


def delete_path(path):
    """
    Deletes a path; will delete directories recursively.
    """
    print(f'* Deleting: {path}')
    if not path.exists():
        return
    if path.is_dir():
        shutil.rmtree(str(path))
    else:
        path.unlink()


def shell_out(cmd):
    print(f"Running {cmd}")
    # Let the resulting exception from `check` propagate out.
    subprocess.run(cmd, check=True)


def main():
    parser = argparse.ArgumentParser(
        prog="prepare_sw",
        description="Script to prepare SW sources for English Breakfast",
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--build',
                        '-b',
                        default=False,
                        action='store_true',
                        help='Build ROM based on reduced design')
    parser.add_argument(
        '--delete-only',
        '-d',
        default=False,
        action='store_true',
        help='Delete previously generated auto-gen files without running topgen'
    )
    parser.add_argument('--top',
                        '-t',
                        default='englishbreakfast',
                        type=str,
                        help='The alternative top to use')
    args = parser.parse_args()
    name = args.top
    topname = f'top_{name}'

    # We start by removing any previously generated auto-gen files for the
    # selected non-earlgrey top. These might be stale and confuse topgen.
    print('Purging previously generated auto-gen files')
    for d in find_dirs(REPO_TOP / 'hw' / topname, ['autogen', 'ip_autogen']):
        delete_path(d)

    delete_path(REPO_TOP / 'build' / str(topname + '-autogen'))
    delete_path(REPO_TOP / 'hw' / topname / 'data/autogen')
    delete_path(REPO_TOP / 'hw' / topname / 'dv/autogen')
    delete_path(REPO_TOP / 'hw' / topname / 'dv/env/autogen')
    delete_path(REPO_TOP / 'hw' / topname / 'ip/ast/rtl')
    delete_path(REPO_TOP / 'hw' / topname / 'ip/clkmgr')
    delete_path(REPO_TOP / 'hw' / topname / 'ip/flash_ctrl')
    delete_path(REPO_TOP / 'hw' / topname / 'ip/pinmux')
    delete_path(REPO_TOP / 'hw' / topname / 'ip/pwrmgr')
    delete_path(REPO_TOP / 'hw' / topname / 'ip/rstmgr')
    delete_path(REPO_TOP / 'hw' / topname / 'ip/sensor_ctrl/rtl')
    delete_path(REPO_TOP / 'hw' / topname / 'ip/xbar_main')
    delete_path(REPO_TOP / 'hw' / topname / 'ip/xbar_peri')
    delete_path(REPO_TOP / 'hw' / topname / 'rtl/autogen')
    delete_path(REPO_TOP / 'hw' / topname / 'sw/autogen')

    if args.delete_only:
        return

    # Next, we need to re-run topgen in order to create all auto-generated files.
    shell_out([
        REPO_TOP / 'util/topgen.py',
        '-t',
        REPO_TOP / 'hw' / topname / 'data' / f"{topname}.hjson",
        '-o',
        REPO_TOP / 'hw' / topname,
    ])

    # We need to patch some files:
    # 1. Build system files need to be pointed to the proper auto-gen files.
    #    Specifically, we overwrite the earlgrey autogen-ed files with the
    #    englishbreakfast equivalents where they differ (i.e. any needed ip in
    #    `hw/topname/{ip, ip_autogen}`).
    # 2. SW sources currently contain
    #    hardcoded references to top_earlgrey. We
    #    need to change some file and variable names in auto-generated files.
    # 3. The build system still uses some sources from the original top level.
    #    We thus need to replace those with the new sources patched in 2.

    # Patch hjson files for Bazel
    print("Transplanting autogen-ed hjson files")
    REG_FILES = [
        'ip_autogen/alert_handler/data/alert_handler.hjson',
        'ip/clkmgr/data/autogen/clkmgr.hjson',
        'ip/flash_ctrl/data/autogen/flash_ctrl.hjson',
        'ip/pwrmgr/data/autogen/pwrmgr.hjson',
        'ip/rstmgr/data/autogen/rstmgr.hjson',
        'ip/pinmux/data/autogen/pinmux.hjson',
        'ip_autogen/rv_plic/data/rv_plic.hjson',
        'ip/ast/data/ast.hjson',
        'ip/sensor_ctrl/data/sensor_ctrl.hjson',
    ]
    for reg_file in REG_FILES:
        src = REPO_TOP / 'hw' / topname / reg_file
        dst = REPO_TOP / 'hw' / 'top_earlgrey' / reg_file
        print(f"* Copying {src} -> {dst}")
        dst.write_text(src.read_text())

    for suffix in ['.c', '.h', '_memory.h', '_memory.ld']:
        old = REPO_TOP / 'hw' / topname / 'sw/autogen' / (topname + suffix)
        new = REPO_TOP / 'hw/top_earlgrey/sw/autogen' / ('top_earlgrey' +
                                                         suffix)
        print(f"* {old} -> {new}")

        text = old.read_text()
        text = text.replace(name, 'earlgrey')
        text = text.replace(name.capitalize(), 'Earlgrey')
        text = text.replace(name.upper(), 'EARLGREY')

        # The SW build expects to find this file both in the top_earlgrey dir AND
        # in the top_englishbreakfast dir.
        new.write_text(text)
        (old.parent / new.name).write_text(text)

    if not args.build:
        return

    # Build the software including test_rom to enable the FPGA build.
    shell_out([
        REPO_TOP / 'bazelisk.sh',
        'build',
        '--copt=-DOT_IS_ENGLISH_BREAKFAST_REDUCED_SUPPORT_FOR_INTERNAL_USE_ONLY_',
    ] + BAZEL_BINARIES)


if __name__ == "__main__":
    main()
