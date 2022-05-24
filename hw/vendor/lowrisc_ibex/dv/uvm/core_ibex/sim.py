#!/usr/bin/env python3

# Copyright 2019 Google LLC
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Regression script for running the Spike UVM testbench"""

import argparse
import logging
import os
import subprocess
import sys

from sim_cmd import get_simulator_cmd

_CORE_IBEX = os.path.normpath(os.path.join(os.path.dirname(__file__)))
_IBEX_ROOT = os.path.normpath(os.path.join(_CORE_IBEX, '../../..'))
_RISCV_DV_ROOT = os.path.join(_IBEX_ROOT, 'vendor/google_riscv-dv')
_XCELIUM_SCRIPTS = os.path.join(_IBEX_ROOT, 'vendor/lowrisc_ip/dv/tools/xcelium')
_OLD_SYS_PATH = sys.path

# Import riscv_trace_csv and lib from _DV_SCRIPTS before putting sys.path back
# as it started.
try:
    sys.path = ([os.path.join(_CORE_IBEX, 'riscv_dv_extension'),
                 os.path.join(_IBEX_ROOT, 'util'),
                 os.path.join(_RISCV_DV_ROOT, 'scripts')] +
                sys.path)

    from lib import run_cmd, setup_logging, RET_SUCCESS, RET_FAIL


finally:
    sys.path = _OLD_SYS_PATH


def subst_vars(string, var_dict):
    '''Apply substitutions in var_dict to string

    If var_dict[K] = V, then <K> will be replaced with V in string.'''
    for key, value in var_dict.items():
        string = string.replace('<{}>'.format(key), value)
    return string


def rtl_compile(compile_cmds, output_dir, lsf_cmd, opts):
    """Compile the testbench RTL

    compile_cmds is a list of commands (each a string), which will have <out>
    and <cmp_opts> substituted. Running them in sequence should compile the
    testbench.

    output_dir is the directory in which to generate the testbench (usually
    something like 'out/rtl_sim'). This will be substituted for <out> in the
    commands.

    If lsf_cmd is not None, it should be a string to prefix onto commands to
    run them through LSF. Here, this is not used for parallelism, but might
    still be needed for licence servers.

    opts is a string giving extra compilation options. This is substituted for
    <cmp_opts> in the commands.

    """
    logging.info("Compiling TB")
    for cmd in compile_cmds:
        cmd = subst_vars(cmd,
                         {
                             'out': output_dir,
                             'cmp_opts': opts
                         })

        if lsf_cmd is not None:
            cmd = lsf_cmd + ' ' + cmd

        logging.debug("Compile command: %s" % cmd)

        # Note that we don't use run_parallel_cmd here: the commands in
        # compile_cmds need to be run serially.
        run_cmd(cmd)


#TODO(udinator) - support DSim, and Riviera
def gen_cov(base_dir, simulator, lsf_cmd):
    """Generate a merged coverage directory.

    Args:
        base_dir:   the base simulation output directory (default: out/)
        simulator:  the chosen RTL simulator
        lsf_cmd:    command to run on LSF

    """
    # Compile a list of all output seed-###/rtl_sim/test.vdb directories
    dir_list = []

    # All generated coverage databases will be named "test.vdb"
    vdb_dir_name = "test.vdb"

    # Copy our existing environment variables to find our unique out folder.
    my_env = os.environ.copy()
    for path, dirs, files in os.walk(my_env['OUT-SEED']):
        for file in files:
            if file.endswith(".ucd") and simulator == 'xlm':
                logging.info("Found coverage database (ucd) at %s" % path)
                dir_list.append(path)
            if vdb_dir_name in dirs and simulator == 'vcs':
                vdb_path = os.path.join(path, vdb_dir_name)
                logging.info("Found coverage database (vdb) at %s" % vdb_path)
                dir_list.append(vdb_path)

    if dir_list == []:
        logging.info(f"No coverage data available for {simulator}, exiting...")
        sys.exit(RET_SUCCESS)

    if simulator == 'vcs':
        cov_cmd = "urg -full64 -format both -dbname test.vdb " \
                  "-report %s/rtl_sim/urgReport -dir" % base_dir
        for cov_dir in dir_list:
            cov_cmd += " %s" % cov_dir
        logging.info("Generating merged coverage directory")
        if lsf_cmd is not None:
            cov_cmd = lsf_cmd + ' ' + cov_cmd
        run_cmd(cov_cmd)
    elif simulator == 'xlm':
        # Get all needed directories for merge and report stages.
        cov_dirs = {
            'cov_merge_dir': my_env['cov_merge_dir'],
            'cov_merge_db_dir': my_env['cov_merge_db_dir'],
            'cov_report_dir': my_env['cov_report_dir'],
        }

        # Create the mentioned directories.
        for d in cov_dirs.values():
            os.makedirs(d, exist_ok=True)

        # The merge TCL code uses a glob to find all available scopes and
        # previous runs. In order to actually get the databases we need to
        # go up once so that the "*" finds the directory we've seen.
        cov_dirs['cov_db_dirs'] = ' '.join([os.path.join(d, '..')
                                            for d in dir_list])
        my_env.update(cov_dirs)

        # First do the merge
        imc_cmd = ["imc", "-64bit", "-licqueue"]
        cov_merge_tcl = os.path.join(_XCELIUM_SCRIPTS, "cov_merge.tcl")
        subprocess.run(imc_cmd + ["-exec", cov_merge_tcl],
                       env=my_env)
        # Then do the reporting
        cov_report_tcl = os.path.join(_XCELIUM_SCRIPTS, "cov_report.tcl")
        subprocess.run(imc_cmd + ["-load", cov_dirs['cov_merge_db_dir'],
                                  "-exec", cov_report_tcl],
                       env=my_env)
    else:
        logging.error("%s is an unsuported simulator! Exiting..." % simulator)
        sys.exit(RET_FAIL)


def main():
    '''Entry point when run as a script'''

    # Parse input arguments
    parser = argparse.ArgumentParser()

    parser.add_argument("--o", type=str, default="out",
                        help="Output directory name")
    parser.add_argument("--simulator", type=str, default="vcs",
                        help="RTL simulator to use (default: vcs)")
    parser.add_argument("--simulator_yaml",
                        help="RTL simulator setting YAML",
                        default=os.path.join(_CORE_IBEX,
                                             'yaml',
                                             'rtl_simulation.yaml'))
    parser.add_argument("-v", "--verbose", dest="verbose", action="store_true",
                        help="Verbose logging")
    parser.add_argument("--cmp_opts", type=str, default="",
                        help="Compile options for the generator")
    parser.add_argument("--en_cov", action='store_true',
                        help="Enable coverage dump")
    parser.add_argument("--en_wave", action='store_true',
                        help="Enable waveform dump")
    parser.add_argument("--en_cosim", action='store_true',
                        help="Enable cosimulation")
    parser.add_argument("--steps", type=str, default="all",
                        help="Run steps: compile,cov")
    parser.add_argument("--lsf_cmd", type=str,
                        help=("LSF command. Run locally if lsf "
                              "command is not specified"))

    args = parser.parse_args()
    setup_logging(args.verbose)

    # If args.lsf_cmd is an empty string return an error message and exit from
    # the script, as doing nothing will result in arbitrary simulation timeouts
    # and errors later on in the run flow.
    if args.lsf_cmd == "":
        logging.error("The LSF command passed in is an empty string.")
        return RET_FAIL

    # Create the output directory
    output_dir = ("%s/rtl_sim" % args.o)
    subprocess.run(["mkdir", "-p", output_dir])

    steps = {
        'compile': args.steps == "all" or 'compile' in args.steps,
        'cov': args.steps == "all" or 'cov' in args.steps
    }

    # Compile TB
    if steps['compile']:
        enables = {
            'cov_opts': args.en_cov,
            'wave_opts': args.en_wave,
            'cosim_opts': args.en_cosim
        }
        compile_cmds, sim_cmd = get_simulator_cmd(args.simulator,
                                                  args.simulator_yaml, enables)

        rtl_compile(compile_cmds, output_dir, args.lsf_cmd, args.cmp_opts)

    # Generate merged coverage directory and load it into appropriate GUI
    if steps['cov']:
        gen_cov(args.o, args.simulator, args.lsf_cmd)

    return RET_SUCCESS


if __name__ == '__main__':
    try:
        sys.exit(main())
    except RuntimeError as err:
        sys.stderr.write('Error: {}\n'.format(err))
        sys.exit(RET_FAIL)
