#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
from typing import List
import os
import shlex
import sys
import subprocess
import pathlib3x as pathlib

from metadata import RegressionMetadata, LockedMetadata
from ibex_cmd import get_compile_opts
from scripts_lib import run_one
import riscvdv_interface

import logging
logger = logging.getLogger(__name__)


def _get_iss_pkgconfig_flags(specifiers: List[str], iss_pc: List[str], simulator: str) -> str:
    all_tokens = []

    # Seperate pkg-config calls for each specifier as combining them has been
    # observed misbehaving on CentOS 7
    # Generate a list of tokens for each call, and append it to the all_tokens variable
    for s in specifiers:
        cmd = ['pkg-config', s] + iss_pc
        stdout = subprocess.check_output(cmd, universal_newlines=True).strip()
        tokens = shlex.split(stdout)
        logger.debug(f"pkgconfig_tokens = {tokens}")

        rpath_prefix = '-Wl,-rpath,'
        def fixup_xcelium_rpath_token(t: str) -> str:
            """Re-format rpath flags to ensure reliable passing to Xcelium.

            When passing rpath flags to xcelium through the xrun tool, we need to re-format the string
            output from pkg-config to ensure reliability.
            This routine detects rpath flags and reformats them according to the Cadence support site
            article.
            """
            if simulator == 'xlm' and t.startswith(rpath_prefix):
                logger.debug(f"rpath token => {t}")
                # https://support.cadence.com/apex/ArticleAttachmentPortal?id=a1Od0000000sdF8EAI
                # See xcelium documentation for the -Wld syntax for passing
                # user specified arguments to the C++ linker.
                # Passing -rpath,<path> options is tricky, so use the following workaround as
                # suggested in the support article.
                # INPUT:  '-Wl,-rpath,/opt/spike/lib'
                # OUTPUT: '-Wld,-Xlinker,-rpath,-Xlinker,/opt/spike/lib',
                rpaths = (t[len(rpath_prefix):]).split(',')
                xlinker_rpaths_str = ','.join((f"-Xlinker,{p}" for p in rpaths))
                rpath_token = f"-Wld,-Xlinker,-rpath,{xlinker_rpaths_str}"
                logger.debug(f"new rpath token => {rpath_token}")
                return rpath_token
            else:
                return t

        tokens = map(fixup_xcelium_rpath_token, tokens)

        all_tokens += tokens

    flags_str = shlex.join(all_tokens)
    logger.debug(f"flags = {flags_str}")
    return flags_str


def _main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--dir-metadata', type=pathlib.Path, required=True)
    args = parser.parse_args()

    # We have some required environment variables down in various scripts
    # that are easier to set here at a high level part of the build.
    # It would be nice to be more explicit somehow...
    expected_env_vars = ['PRJ_DIR', 'LOWRISC_IP_DIR']
    for var in expected_env_vars:
        if os.getenv(var) is None:
            raise RuntimeError(f'The environment variable {var!r} is not set.')

    with LockedMetadata(args.dir_metadata, __file__) as md:
        md.dir_tb.mkdir(exist_ok=True, parents=True)
        md.tb_build_log = md.dir_tb/'compile_tb.log'

        # Locate the spike .pc files to allow us to link against it when
        # building, riscv-fesvr isn't strictly required but the DV flow has been
        # observed to see build failures where it isn't present with CentOS 7.
        spike_iss_pc = ['riscv-riscv', 'riscv-disasm', 'riscv-fdt',
            'riscv-fesvr']
        try:
            subprocess.check_output(['pkg-config', '--exists'] + spike_iss_pc)
        except subprocess.CalledProcessError as err:
            raise RuntimeError(
                f'Failed to find {spike_iss_pc} pkg-config packages. '
                f'Did you set the PKG_CONFIG_PATH correctly?') from err

        # Now call out to pkg-config to return the appropriate flags for compilation
        # (The keys here are the substitution placeholders in rtl_simulation.yaml)
        iss_pkgconfig_dict = {
            'ISS_CFLAGS'  : ['--cflags'],
            'ISS_LDFLAGS' : ['--libs-only-other'],
            'ISS_LIBS'    : ['--libs-only-l', '--libs-only-L'],
        }
        iss_cc_subst_vars_dict = \
            {k: _get_iss_pkgconfig_flags(v, spike_iss_pc, md.simulator)
             for k, v in iss_pkgconfig_dict.items()}

        # Populate the entire set of variables to substitute in the templated
        # compilation command, including the compiler flags for the ISS.
        subst_vars_dict = {
            'core_ibex': md.ibex_dv_root,
            'tb_dir': md.dir_tb,
            'tb_build_log': md.tb_build_log,
            'cmp_opts': get_compile_opts(md.ibex_config,
                                         md.simulator),
            'dir_shared_cov': (md.dir_shared_cov if md.cov else ''),
            'xlm_cov_cfg_file': f"{md.ot_xcelium_cov_scripts}/cover.ccf",
            'dut_cov_rtl_path': md.dut_cov_rtl_path
        }
        subst_vars_dict.update(iss_cc_subst_vars_dict)

        md.tb_build_stdout = md.dir_tb/'compile_tb_stdstreams.log'
        md.tb_build_cmds = riscvdv_interface.get_tool_cmds(
            yaml_path=md.ibex_riscvdv_simulator_yaml,
            simulator=md.simulator,
            cmd_type='compile',
            user_enables={
                'cov_opts': md.cov,
                'wave_opts': md.waves,
                'cosim_opts': True  # Always enable now post_compare is deprecated
            },
            user_subst_options=subst_vars_dict)

    # Write all compile-tb output into a single logfile
    with md.tb_build_stdout.open('wb') as compile_fd:
        for cmd in md.tb_build_cmds:
            compile_fd.write(f"Running compile_tb command :\n{' '.join(cmd)}\n".encode())
            retcode = run_one(md.verbose, cmd, redirect_stdstreams=compile_fd)
            if retcode:
                return retcode

    return 0


if __name__ == '__main__':
    sys.exit(_main())
