#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import os
import sys
import subprocess
import pathlib3x as pathlib

from metadata import RegressionMetadata, LockedMetadata
from ibex_cmd import get_compile_opts
from scripts_lib import run_one
import riscvdv_interface

import logging
logger = logging.getLogger(__name__)


def _get_iss_pkgconfig_flags(specifiers, iss_pc, simulator):
    _flags = subprocess.check_output(
        args=(['pkg-config'] + specifiers + iss_pc),
        universal_newlines=True,
        ).strip()
    if simulator == 'xlm':
        # See xcelium documentation for the -Wld syntax for passing
        # flags to the linker. Passing -rpath,<path> options is tricky
        # because commas are parsed strangely between xrun and the xmsc
        # tool, and its easy for the options to arrive malformed. Use
        # the following hack to get it through.
        if '-Wl' in _flags:  # This should be in LDFLAGS only
            _flags = "'-Xlinker {}'".format(_flags.replace('-Wl,', ''))
    return _flags


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

        subst_vars_dict = {
            'core_ibex': md.ibex_dv_root,
            'tb_dir': md.dir_tb,
            'tb_build_log': md.tb_build_log,
            'cmp_opts': get_compile_opts(md.ibex_config,
                                         md.simulator),
            'dir_shared_cov': (md.dir_shared_cov if md.cov else ''),
        }

        # Locate the spike .pc files to allow us to link against it when building
        spike_iss_pc = ['riscv-riscv', 'riscv-disasm', 'riscv-fdt']
        iss_pkgconfig_dict = {
            'ISS_CFLAGS'  : ['--cflags'],
            'ISS_LDFLAGS' : ['--libs-only-other'],
            'ISS_LIBS'    : ['--libs-only-l', '--libs-only-L'],
        }
        md.envvar_PKG_CONFIG_PATH = dict(os.environ).get('PKG_CONFIG_PATH')
        try:
            subprocess.check_output(['pkg-config', '--exists'] + spike_iss_pc)
        except subprocess.CalledProcessError as err:
            raise RuntimeError(
                f'Failed to find {spike_iss_pc} pkg-config packages. '
                f'Did you set the PKG_CONFIG_PATH correctly?') from err
        subst_vars_dict.update(
            {k: _get_iss_pkgconfig_flags(v,
                                         spike_iss_pc,
                                         md.simulator)
             for k, v in iss_pkgconfig_dict.items()})

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
