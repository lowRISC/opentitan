# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import os
import subprocess

_THIS_DIR = os.path.normpath(os.path.join(os.path.dirname(__file__)))
_IBEX_ROOT = os.path.normpath(os.path.join(_THIS_DIR, 4 * '../'))

# For each simulator, a tuple
#
#    (needs_compile_opts, needs_sim_opts)
#
SIM_CFGS = {
    'vcs': (True, False),
    'riviera': (True, True),
    'questa': (True, True),
    'xlm': (True, False),
    'dsim': (True, False)
}


class GenError(Exception):
    pass


def run_ibex_config(config_name: str, output_type: str) -> str:
    script_path = os.path.join(_IBEX_ROOT, 'util', 'ibex_config.py')
    yaml_path = os.path.join(_IBEX_ROOT, 'ibex_configs.yaml')

    ibex_config_cmd = [
        script_path,
        '--config_filename', yaml_path,
        config_name,
        output_type,
        '--ins_hier_path', 'core_ibex_tb_top',
        '--string_define_prefix', 'IBEX_CFG_'
    ]
    proc = subprocess.run(ibex_config_cmd,
                          stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE,
                          universal_newlines=True)

    if proc.returncode != 0:
        raise GenError("Error running {0} got:\n{1}\n{2}"
                       .format(script_path, proc.stdout, proc.stderr))

    return proc.stdout.strip()


def get_x_opts(config_name: str, simulator: str, stage: str) -> str:
    try:
        needs_compile_opts, needs_sim_opts = SIM_CFGS[simulator]
    except KeyError:
        raise ValueError(f'Unsupported simulator: {simulator}.')

    specify_which_opts = needs_compile_opts and needs_sim_opts

    if stage == 'compile':
        needs_opts = needs_compile_opts
    elif stage == 'sim':
        needs_opts = needs_sim_opts
    else:
        assert 0

    if not needs_opts:
        return ''

    output_type = (f'{simulator}_{stage}_opts'
                   if specify_which_opts else f'{simulator}_opts')

    return run_ibex_config(config_name, output_type)


def get_compile_opts(config_name: str, simulator: str) -> str:
    return get_x_opts(config_name, simulator, 'compile')


def get_sim_opts(config_name: str, simulator: str) -> str:
    return get_x_opts(config_name, simulator, 'sim')
