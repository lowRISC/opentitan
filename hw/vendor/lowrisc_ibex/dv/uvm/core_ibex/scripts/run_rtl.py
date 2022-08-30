#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import os
import sys
import pathlib3x as pathlib

from ibex_cmd import get_sim_opts
import riscvdv_interface
from scripts_lib import run_one, format_to_cmd
from test_entry import read_test_dot_seed, get_test_entry
from metadata import RegressionMetadata
from test_run_result import TestRunResult

import logging
logger = logging.getLogger(__name__)


def _main() -> int:
    """Generate and run rtl simulation commands."""
    parser = argparse.ArgumentParser()
    parser.add_argument('--dir-metadata', type=pathlib.Path, required=True)
    parser.add_argument('--test-dot-seed', type=read_test_dot_seed, required=True)
    args = parser.parse_args()
    tds = args.test_dot_seed
    md = RegressionMetadata.construct_from_metadata_dir(args.dir_metadata)
    trr = TestRunResult.construct_from_metadata_dir(args.dir_metadata, f"{tds[0]}.{tds[1]}")

    testopts = get_test_entry(trr.testname)  # From testlist.yaml

    if not os.path.exists(trr.binary):
        raise RuntimeError(
            "When computing simulation command for running "
            f"seed {trr.seed} of test {trr.testname}, cannot find the "
            f"expected binary at {trr.binary!r}.")

    # Each test in testlist.yaml can (optionally) specify 'sim_opts'
    # which are to be passed to the simulator when running the test.
    sim_opts = ''
    sim_opts_raw = testopts.get('sim_opts')
    if sim_opts_raw:
        sim_opts += sim_opts_raw.replace('\n', '')

    trr.rtl_log         = trr.dir_test / 'rtl_sim.log'
    trr.rtl_trace       = trr.dir_test / 'trace_core_00000000.log'
    trr.iss_cosim_trace = trr.dir_test / f'{md.iss}_cosim_trace_core_00000000.log'
    subst_vars_dict = {
        'cwd': md.ibex_root,
        'test_name': testopts['test'],
        'rtl_test': testopts['rtl_test'],
        'seed': str(trr.seed),
        'binary': trr.binary,
        'test_dir': trr.dir_test,
        'tb_dir': md.dir_tb,
        'dir_shared_cov': md.dir_shared_cov,
        'rtl_sim_log': trr.rtl_log,
        'rtl_trace': trr.rtl_trace.parent/'trace_core',
        'iss_cosim_trace': trr.iss_cosim_trace,
        'sim_opts': (f"+signature_addr={md.signature_addr}\n" +
                     f"{get_sim_opts(md.ibex_config, md.simulator)}\n" +
                     sim_opts)
    }

    # Look up how to run the simulator
    sim_cmds = riscvdv_interface.get_tool_cmds(
        yaml_path=md.ibex_riscvdv_simulator_yaml,
        simulator=md.simulator,
        cmd_type='sim',
        user_enables={
            'cov_opts': md.cov,
            'wave_opts': md.waves,
            },
        user_subst_options=subst_vars_dict)
    logger.info(sim_cmds)

    trr.dir_test.mkdir(exist_ok=True, parents=True)
    trr.rtl_cmds   = [format_to_cmd(cmd) for cmd in sim_cmds]
    trr.rtl_stdout = trr.dir_test / 'rtl_sim_stdstreams.log'
    trr.export(write_yaml=True)

    # Write all sim_cmd output into a single logfile
    with open(trr.rtl_stdout, 'wb') as sim_fd:

        for cmd in trr.rtl_cmds:
            # Note that we don't capture the success or failure of the subprocess:

            sim_fd.write(f"Running run-rtl command :\n{' '.join(cmd)}\n".encode())
            run_one(md.verbose, cmd, redirect_stdstreams=sim_fd, timeout_s=1800)

    # Always return 0 (success), even if the test failed. We've successfully
    # generated a log either way.
    return 0


if __name__ == '__main__':
    sys.exit(_main())
