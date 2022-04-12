#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import os.path
import subprocess
import sys

ibex_config_path = ''
ibex_config_name = ''
ibex_config_filename = ''


class GenError(Exception):
    pass


def run_ibex_config(output_type, extra_args=None):
    ibex_config_cmd = [
        ibex_config_path,
        ibex_config_name,
        '--config_filename', ibex_config_filename,
        output_type
    ]

    if extra_args:
        ibex_config_cmd += extra_args

    result = subprocess.run(ibex_config_cmd,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE)

    if result.returncode != 0:
        raise GenError("Error running {0} got:\n{1}\n{2}".format(
            ibex_config_path, str(result.stdout, 'utf-8'),
            str(result.stderr, 'utf-8')))

    return str(result.stdout, 'utf-8')


def gen_vcs_makefrag():
    vcs_compile_opts = run_ibex_config('vcs_opts', [
        '--ins_hier_path', 'core_ibex_tb_top',
        '--string_define_prefix', 'IBEX_CFG_'
    ])

    return 'COMPILE_OPTS += {0}'.format(vcs_compile_opts)


def gen_riviera_makefrag():
    riviera_compile_opts = run_ibex_config('riviera_compile_opts', [
        '--ins_hier_path', 'core_ibex_tb_top',
        '--string_define_prefix', 'IBEX_CFG_'
    ])

    riviera_sim_opts = run_ibex_config('riviera_sim_opts', [
        '--ins_hier_path', 'core_ibex_tb_top',
        '--string_define_prefix', 'IBEX_CFG_'
    ])

    return ('COMPILE_OPTS += {0}'
            'SIM_OPTS += {1}').format(riviera_compile_opts, riviera_sim_opts)


def gen_questa_makefrag():
    questa_compile_opts = run_ibex_config('questa_compile_opts', [
        '--ins_hier_path', 'core_ibex_tb_top',
        '--string_define_prefix', 'IBEX_CFG_'
    ])

    questa_sim_opts = run_ibex_config('questa_sim_opts', [
        '--ins_hier_path', 'core_ibex_tb_top',
        '--string_define_prefix', 'IBEX_CFG_'
    ])

    return ('COMPILE_OPTS += {0}'
            'SIM_OPTS += {1}').format(questa_compile_opts, questa_sim_opts)


def gen_xlm_makefrag():
    xlm_compile_opts = run_ibex_config('xlm_opts', [
        '--ins_hier_path', 'core_ibex_tb_top',
        '--string_define_prefix', 'IBEX_CFG_'
    ])

    return 'COMPILE_OPTS += {0}'.format(xlm_compile_opts)

def gen_dsim_makefrag():
    dsim_compile_opts = run_ibex_config('dsim_compile_opts', [
        '--ins_hier_path', 'core_ibex_tb_top',
        '--string_define_prefix', 'IBEX_CFG_'
    ])

    return 'COMPILE_OPTS += {0}'.format(gen_dsim_makefrag)


def main():
    argparser = argparse.ArgumentParser(description=(
        'Generates a makefile fragment for use with the Ibex DV makefile that '
        'sets up sim specific variables'))

    sim_fns = {
        'vcs': gen_vcs_makefrag,
        'riviera': gen_riviera_makefrag,
        'xlm': gen_xlm_makefrag,
        'questa': gen_questa_makefrag,
        'dsim': gen_dsim_makefrag
        }

    argparser.add_argument('sim',
                           help='Name of the simulator',
                           choices=sim_fns.keys())

    argparser.add_argument(
        'config', help='Ibex config to generate makefile fragment for')

    argparser.add_argument('ibex_top',
                           help='Path to the top of an ibex repository')

    argparser.add_argument('makefrag_name',
                           help='Filename of the makefile fragment to write')

    args = argparser.parse_args()

    global ibex_config_path
    global ibex_config_name
    global ibex_config_filename

    ibex_config_path = os.path.join(args.ibex_top, 'util/ibex_config.py')
    ibex_config_name = args.config
    ibex_config_filename = os.path.join(args.ibex_top, 'ibex_configs.yaml')

    try:
        with open(args.makefrag_name, 'w') as makefrag:
            makefrag.write(sim_fns[args.sim]())
    except GenError as e:
        print('Failure generating simulation options for', args.sim)
        print(e)
        sys.exit(1)


if __name__ == "__main__":
    main()
