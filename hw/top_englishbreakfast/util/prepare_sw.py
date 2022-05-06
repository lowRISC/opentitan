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
    'sw/device/lib/testing/test_rom/test_rom_export_fpga_nexysvideo',
    'sw/device/sca/aes_serial_export_fpga_nexysvideo',
    'sw/device/lib/testing/test_rom/test_rom_export_sim_verilator',
    'sw/device/tests/aes_smoketest_export_sim_verilator',
    'sw/device/examples/hello_world/hello_world_export_sim_verilator',
]

BAZEL_BINARIES = [
    '//sw/device/lib/testing/test_rom',
    '//sw/device/sca:aes_serial',
    '//sw/device/tests:aes_smoketest',
    '//sw/device/examples/hello_world',
]

def find_dirs(root, names):
    """
    Finds all directories under `root` with the given name and
    yields them.
    """
    for p in root.iterdir():
        if not p.is_dir(): continue
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
    parser.add_argument(
        '--build',
        '-b',
        default=False,
        action='store_true',
        help='Build ROM based on reduced design')
    parser.add_argument(
        '--delete-only',
        '-d',
        default=False,
        action='store_true',
        help='Delete previously generated auto-gen files without running topgen')
    parser.add_argument(
        '--top',
        '-t',
        default='englishbreakfast',
        type=str,
        help='The alternative top to use')
    parser.add_argument(
        '--bazel',
        default=False,
        action='store_true',
        help='Whether to build with Bazel instead')
    args = parser.parse_args()
    name = args.top
    topname = f'top_{name}'

    # We start by removing any previously generated auto-gen files for the
    # selected non-earlgrey top. These might be stale and confuse topgen.
    print('Purging previously generated auto-gen files')
    for d in find_dirs(REPO_TOP / 'hw' / topname, ['autogen', 'ip_autogen']):
        delete_path(d)

    delete_path(REPO_TOP / 'build' / str(topname + '-autogen'))
    delete_path(REPO_TOP / 'hw' / topname / 'ip/ast/rtl')
    delete_path(REPO_TOP / 'hw' / topname / 'ip/sensor_ctrl/rtl')
    delete_path(REPO_TOP / 'hw' / topname / 'ip/xbar_main/xbar_main.core')
    delete_path(REPO_TOP / 'hw' / topname / 'ip/xbar_peri/xbar_peri.core')

    if args.delete_only:
        return;

    # Next, we need to re-run topgen in order to create all auto-generated files.
    shell_out([
        REPO_TOP / 'util/topgen.py',
        '-t', REPO_TOP / 'hw' / topname / 'data' / f"{topname}.hjson",
        '-o', REPO_TOP / 'hw' / topname,
    ])

    # We need to patch some files:
    # 1. meson.build needs to be pointed to the proper auto-gen files.
    # 2. SW sources currently contain hardcoded references to top_earlgrey. We
    #    need to change some file and variable names in auto-generated files.
    # 3. The build system still uses some sources from the original top level.
    #    We thus need to replace those with the new sources patched in 2.

    if not args.bazel:
        print("Rewriting $REPO_TOP/meson.build's TOPNAME")
        meson_build = (REPO_TOP / 'meson.build').read_text()
        meson_build = meson_build.replace("TOPNAME='top_earlgrey'", f"TOPNAME='{topname}'")
        (REPO_TOP / 'meson.build').write_text(meson_build)

    for suffix in ['.c', '.h', '_memory.h', '_memory.ld']:
        old = REPO_TOP / 'hw' / topname / 'sw/autogen' / (topname + suffix)
        new = REPO_TOP / 'hw/top_earlgrey/sw/autogen' / ('top_earlgrey' + suffix)
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
        return;

    # Build the software including test_rom to enable the FPGA build.
    if args.bazel:
        shell_out([
            'bazel', 'build',
            '--copt=-DOT_IS_ENGLISH_BREAKFAST_REDUCED_SUPPORT_FOR_INTERNAL_USE_ONLY_',
        ] + BAZEL_BINARIES)
    else:
        shell_out(['ninja', '-C', REPO_TOP / 'build-out'] + BINARIES)

if __name__ == "__main__":
    main()
