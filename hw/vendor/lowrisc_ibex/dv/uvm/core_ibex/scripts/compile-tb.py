#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import os
import sys
import subprocess

from ibex_cmd import get_compile_opts
from scripts_lib import THIS_DIR, run_one, subst_vars
from sim_cmd import get_simulator_cmd


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


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--verbose', action='store_true')

    parser.add_argument('--ibex-config', required=True)
    parser.add_argument('--output', required=True)
    parser.add_argument('--shared-cov-dir', required=True)
    parser.add_argument('--simulator', required=True)
    parser.add_argument('--en_cov', action='store_true')
    parser.add_argument('--en_wave', action='store_true')
    parser.add_argument('--en_cosim', action='store_true')

    args = parser.parse_args()

    expected_env_vars = ['PRJ_DIR', 'LOWRISC_IP_DIR']
    for var in expected_env_vars:
        if os.getenv(var) is None:
            raise RuntimeError(f'The environment variable {var!r} is not set.')

    core_ibex = os.path.normpath(os.path.join(THIS_DIR, '..'))

    os.makedirs(args.output, exist_ok=True)

    subst_vars_dict = {
        'core_ibex': core_ibex,
        'out': args.output,
        'cmp_opts': get_compile_opts(args.ibex_config,
                                     args.simulator)
    }

    # Find the correct flags for the tb to link against the compiled ISS
    spike_iss_pc = ['riscv-riscv', 'riscv-disasm', 'riscv-fdt']
    iss_pkgconfig_dict = {
        'ISS_CFLAGS'  : ['--cflags'],
        'ISS_LDFLAGS' : ['--libs-only-other'],
        'ISS_LIBS'    : ['--libs-only-l', '--libs-only-L'],
    }
    if args.en_cosim:
        try:
            subprocess.check_output(['pkg-config', '--exists'] + spike_iss_pc)
        except subprocess.CalledProcessError as err:
            raise RuntimeError(
                f'Failed to find {spike_iss_pc} pkg-config packages. '
                f'Did you set the PKG_CONFIG_PATH correctly?') from err
        subst_vars_dict.update(
            {k: _get_iss_pkgconfig_flags(v,
                                         spike_iss_pc,
                                         args.simulator)
             for k, v in iss_pkgconfig_dict.items()})

    if args.en_cov:
        subst_vars_dict.update({'shared_cov_dir': args.shared_cov_dir})

    enables = {
        'cov_opts': args.en_cov,
        'wave_opts': args.en_wave,
        'cosim_opts': args.en_cosim
    }
    compile_cmds, _ = get_simulator_cmd(args.simulator, enables)

    for pre_cmd in compile_cmds:
        cmd = subst_vars(pre_cmd, subst_vars_dict)
        retcode = run_one(args.verbose, ['sh', '-c', cmd],
                          redirect_stdstreams='/dev/null')
        if retcode:
            return retcode

    return 0


if __name__ == '__main__':
    sys.exit(main())
