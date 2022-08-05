#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Regression script for running the Spike UVM testbench"""

import argparse
import logging
import os
import shutil
import sys
from typing import Set

from scripts_lib import run_one

_THIS_DIR = os.path.normpath(os.path.join(os.path.dirname(__file__)))
_IBEX_ROOT = os.path.normpath(os.path.join(_THIS_DIR, 4 * '../'))


def find_cov_dirs(start_dir: str, simulator: str) -> Set[str]:
    assert simulator in ['xlm', 'vcs']

    # For VCS, all generated coverage databases will be named "test.vdb"
    vdb_dir_name = "test.vdb"

    cov_dirs = set()
    for path, dirs, files in os.walk(start_dir):
        for file in files:
            if file.endswith(".ucd") and simulator == 'xlm':
                logging.info("Found coverage database (ucd) at %s" % path)
                cov_dirs.add(path)
        if vdb_dir_name in dirs and simulator == 'vcs':
            vdb_path = os.path.join(path, vdb_dir_name)
            logging.info("Found coverage database (vdb) at %s" % vdb_path)
            cov_dirs.add(vdb_path)

    return cov_dirs


def merge_cov_vcs(cov_dir: str, verbose: bool, cov_dirs: Set[str]) -> int:
    logging.info("Generating merged coverage directory")
    cmd = (['urg', '-full64',
            '-format', 'both',
            '-dbname', os.path.join(cov_dir, 'merged.vdb'),
            '-report', os.path.join(cov_dir, 'report'),
            '-log', os.path.join(cov_dir, 'merge.log'),
            '-dir'] +
           list(cov_dirs))
    return run_one(verbose, cmd, redirect_stdstreams='/dev/null')


def merge_cov_xlm(cov_dir: str, verbose: bool, cov_dirs: Set[str]) -> int:
    xcelium_scripts = os.path.join(_IBEX_ROOT,
                                   'vendor/lowrisc_ip/dv/tools/xcelium')

    # The merge TCL code uses a glob to find all available scopes and previous
    # runs. In order to actually get the databases we need to go up once so
    # that the "*" finds the directory we've seen.
    cov_dir_parents = {os.path.normpath(os.path.join(d, '..'))
                       for d in cov_dirs}

    merge_dir = os.path.join(cov_dir, 'merged')
    report_dir = os.path.join(cov_dir, 'report')

    # Get all needed directories for merge and report stages.
    xlm_cov_dirs = {
        'cov_merge_db_dir': merge_dir,
        'cov_report_dir': report_dir
    }

    # Finally, set an environment variable containing all the directories that
    # should be merged (this is how the list gets passed down to the TCL script
    # that handles them)
    xlm_cov_dirs['cov_db_dirs'] = ' '.join(cov_dir_parents)

    xlm_env = os.environ.copy()
    xlm_env.update(xlm_cov_dirs)

    # First do the merge
    imc_cmd = ["imc", "-64bit", "-licqueue"]
    os.makedirs(merge_dir, exist_ok=True)
    cov_merge_tcl = os.path.join(xcelium_scripts, "cov_merge.tcl")
    merge_ret = run_one(verbose,
                        imc_cmd + ["-exec", cov_merge_tcl,
                                   "-logfile", os.path.join(cov_dir,
                                                            'merge.log'),
                                   "-nostdout"],
                        env=xlm_env)
    if merge_ret:
        return merge_ret

    # Then do the reporting
    cov_report_tcl = os.path.join(xcelium_scripts, "cov_report.tcl")
    os.makedirs(report_dir, exist_ok=True)
    report_ret = run_one(verbose,
                         imc_cmd + ["-load", merge_dir,
                                    "-exec", cov_report_tcl,
                                    "-logfile", os.path.join(cov_dir,
                                                             'report.log'),
                                    "-nostdout"],
                         env=xlm_env)
    return report_ret


def main():
    '''Entry point when run as a script'''
    parser = argparse.ArgumentParser()

    parser.add_argument("--working-dir")
    parser.add_argument("--simulator")
    parser.add_argument("--verbose", action="store_true")

    args = parser.parse_args()

    if args.simulator not in ['xlm', 'vcs']:
        raise ValueError(f'Unsupported simulator: {args.simulator}.')

    output_dir = os.path.join(args.working_dir, 'coverage')

    # If output_dir exists, delete it: we'll re-generate its contents in a sec
    # and we don't want to accidentally pick them up as part of the merge.
    try:
        shutil.rmtree(output_dir)
    except FileNotFoundError:
        pass

    # Now make output_dir again (but empty)
    os.makedirs(output_dir)

    # Compile a list of all directories that contain coverage databases
    cov_dirs = find_cov_dirs(args.working_dir, args.simulator)
    if not cov_dirs:
        logging.info(f"No coverage found for {args.simulator}.")
        return 1

    merge_funs = {
        'vcs': merge_cov_vcs,
        'xlm': merge_cov_xlm
    }
    return merge_funs[args.simulator](output_dir, args.verbose, cov_dirs)


if __name__ == '__main__':
    try:
        sys.exit(main())
    except RuntimeError as err:
        sys.stderr.write('Error: {}\n'.format(err))
        sys.exit(1)
