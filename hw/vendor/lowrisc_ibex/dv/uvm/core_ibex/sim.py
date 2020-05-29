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
import os
import random
import subprocess
import sys

_CORE_IBEX = os.path.normpath(os.path.join(os.path.dirname(__file__)))
_IBEX_ROOT = os.path.normpath(os.path.join(_CORE_IBEX, '../../..'))
_RISCV_DV_ROOT = os.path.join(_IBEX_ROOT, 'vendor/google_riscv-dv')
_OLD_SYS_PATH = sys.path

# Import riscv_trace_csv and lib from _DV_SCRIPTS before putting sys.path back
# as it started.
try:
    sys.path = ([os.path.join(_CORE_IBEX, 'riscv_dv_extension'),
                 os.path.join(_RISCV_DV_ROOT, 'scripts')] +
                sys.path)

    from lib import (process_regression_list,
                     read_yaml, run_cmd, run_parallel_cmd,
                     setup_logging, RET_SUCCESS, RET_FAIL)
    import logging

    from spike_log_to_trace_csv import process_spike_sim_log
    from ovpsim_log_to_trace_csv import process_ovpsim_sim_log
    from instr_trace_compare import compare_trace_csv

    from ibex_log_to_trace_csv import process_ibex_sim_log, check_ibex_uvm_log

finally:
    sys.path = _OLD_SYS_PATH


class SeedGen:
    '''A generator for seed values'''
    def __init__(self, fixed_seed, start_seed):
        self.fixed = False
        self.start_seed = 0

        if fixed_seed is not None:
            if start_seed is not None:
                logging.error("Cannot pass both --seed and --start_seed.")
                sys.exit(RET_FAIL)

            self.start_seed = fixed_seed
            self.fixed = True
            return

        if start_seed is not None:
            self.start_seed = start_seed
            return

        # Neither --seed nor --start_seed passed. Print out the seed so the
        # user can see what's going on.
        self.start_seed = random.getrandbits(32)
        logging.info("Random start seed chosen: {}".format(self.start_seed))

    def gen(self, iteration):
        if iteration != 0:
            assert not self.fixed

        return self.start_seed + iteration


def subst_opt(string, name, enable, replacement):
    '''Substitute the <name> option in string

    If enable is False, <name> is replaced by '' in string. If it is True,
    <name> is replaced by replacement, which should be a string or None. If
    replacement is None and <name> occurs in string, we throw an error.

    '''
    needle = '<{}>'.format(name)
    if not enable:
        return string.replace(needle, '')

    if replacement is None:
        if needle in string:
            raise RuntimeError('No replacement defined for {} '
                               '(used in string: {!r}).'
                               .format(needle, string))
        return string

    return string.replace(needle, replacement)


def subst_env_vars(string, env_vars):
    '''Substitute environment variables in string

    env_vars should be a string with a comma-separated list of environment
    variables to substitute. For each environment variable, V, in the list, any
    occurrence of <V> in string will be replaced by the value of the
    environment variable with that name. If <V> occurs in the string but $V is
    not set in the environment, an error is raised.

    '''
    env_vars = env_vars.strip()
    if not env_vars:
        return string

    for env_var in env_vars.split(','):
        env_var = env_var.strip()
        needle = '<{}>'.format(env_var)
        if needle in string:
            value = os.environ.get(env_var)
            if value is None:
                raise RuntimeError('Cannot substitute {} in command because '
                                   'the environment variable ${} is not set.'
                                   .format(needle, env_var))
            string = string.replace(needle, value)

    return string


def subst_cmd(cmd, enable_dict, opts_dict, env_vars):
    '''Substitute options and environment variables in cmd

    enable_dict should be a dict mapping names to bools. For each key, N, in
    enable_dict, if enable_dict[N] is False, then all occurrences of <N> in cmd
    will be replaced with ''. If enable_dict[N] is True, all occurrences of <N>
    in cmd will be replaced with opts_dict[N].

    If N is not a key in opts_dict, this is no problem unless cmd contains
    <N>, in which case we throw a RuntimeError.

    Finally, the environment variables are substituted as described in
    subst_env_vars and any newlines are stripped out.

    '''
    for name, enable in enable_dict.items():
        cmd = subst_opt(cmd, name, enable, opts_dict.get(name))

    return subst_env_vars(cmd, env_vars).replace('\n', ' ')


def subst_vars(string, var_dict):
    '''Apply substitutions in var_dict to string

    If var_dict[K] = V, then <K> will be replaced with V in string.'''
    for key, value in var_dict.items():
        string = string.replace('<{}>'.format(key), value)
    return string


def get_yaml_for_simulator(simulator, yaml_path):
    '''Read yaml at yaml_path and find entry for simulator'''
    logging.info("Processing simulator setup file : %s" % yaml_path)
    for entry in read_yaml(yaml_path):
        if entry.get('tool') == simulator:
            return entry

    raise RuntimeError("Cannot find RTL simulator {}".format(simulator))


def get_simulator_cmd(simulator, yaml_path, enables):
    '''Get compile and run commands for the testbench

    simulator is the name of the simulator to use. yaml_path is the path to a
    yaml file describing various command line options. enables is a dictionary
    keyed by option names with boolean values: true if the option is enabled.

    Returns (compile_cmds, sim_cmd), which are the simulator commands to
    compile and run the testbench, respectively. compile_cmd is a list of
    strings (multiple commands); sim_cmd is a single string.

    '''
    entry = get_yaml_for_simulator(simulator, yaml_path)
    env_vars = entry.get('env_var', '')

    return ([subst_cmd(arg, enables, entry['compile'], env_vars)
             for arg in entry['compile']['cmd']],
            subst_cmd(entry['sim']['cmd'], enables, entry['sim'], env_vars))


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


def get_test_sim_cmd(base_cmd, test, idx, output_dir, bin_dir, lsf_cmd):
    '''Generate the command that runs a test iteration in the simulator

    base_cmd is the command to use before any test-specific substitutions. test
    is a dictionary describing the test (originally read from the testlist YAML
    file). idx is the test iteration (an integer).

    output_dir is the directory below which the test results will be written.
    bin_dir is the directory containing compiled binaries. lsf_cmd (if not
    None) is a string that runs bsub to submit the task on LSF.

    Returns (desc, cmd, dirname) where desc is a description of the command,
    cmd is the command to run and dirname is the directory in which to run it.

    '''
    sim_cmd = (base_cmd + ' ' + test['sim_opts'].replace('\n', ' ')
               if "sim_opts" in test
               else base_cmd)

    test_name = test['test']

    sim_dir = os.path.join(output_dir, '{}.{}'.format(test_name, idx))
    binary = os.path.join(bin_dir, '{}_{}.bin'.format(test_name, idx))
    desc = '{} with {}'.format(test['rtl_test'], binary)

    # Do final interpolation into the test command for variables that depend on
    # the test name or iteration number.
    sim_cmd = subst_vars(sim_cmd,
                         {
                             'sim_dir': sim_dir,
                             'rtl_test': test['rtl_test'],
                             'binary': binary,
                             'test_name': test_name,
                             'iteration': str(idx)
                         })

    if not os.path.exists(binary):
        raise RuntimeError('When computing simulation command for running '
                           'iteration {} of test {}, cannot find the '
                           'expected binary at {!r}.'
                           .format(idx, test_name, binary))

    if lsf_cmd is not None:
        sim_cmd = lsf_cmd + ' ' + sim_cmd

    return (desc, sim_cmd, sim_dir)


def run_sim_commands(command_list, use_lsf):
    '''Run the given list of commands

    command_list should be a list of tuples (desc, cmd, dirname) where desc is
    a human-readable description of the test, cmd is a command to run and
    dirname is the directory in which to run it (which will be created if
    necessary).

    If use_lsf is true, the commands in command_list begin with something like
    'bsub -Is'. It seems that we always use interactive bsub, so we'll have a
    local process per job, which we track with run_parallel_cmd.

    '''
    # If we're in LSF mode, we submit all the commands 'at once', which means
    # we have to create the output directories in advance.
    if use_lsf:
        cmds = []
        for desc, cmd, dirname in command_list:
            os.makedirs(dirname, exist_ok=True)
            cmds.append(cmd)
        run_parallel_cmd(cmds, 600, check_return_code=True)
        return

    # We're not in LSF mode, so we'll create the output directories as we go.
    # That should make it a bit easier to see how far we got if there was an
    # error.
    for desc, cmd, dirname in command_list:
        os.makedirs(dirname, exist_ok=True)
        logging.info("Running " + desc)
        run_cmd(cmd, 300, check_return_code=True)


def rtl_sim(sim_cmd, test_list, seed_gen, opts,
            output_dir, bin_dir, lsf_cmd):
    """Run the testbench in the simulator

    sim_cmd is the base command (as returned by get_simulator_cmd). This will
    still have placeholders for test-specific arguments. test_list is a list of
    test objects read from the testlist YAML file which gives the tests to run.

    seed the seed generator to use to supply seeds for the simulations
    (controls things like random delays on the bus). opts is a string of
    plusargs to give to the simulator.

    output_dir is the output directory for simulation files (and the directory
    in which the simulator gets run). bin_dir is the directory containing
    binaries to be run.

    If lsf_cmd is not None, it should be prefixed on each command, which will
    be run in parallel.

    """
    logging.info("Running RTL simulation...")

    sim_cmd = subst_vars(sim_cmd,
                         {
                             'out': output_dir,
                             'sim_opts': opts,
                             'cwd': _CORE_IBEX,
                         })

    # Compute a list of pairs (cmd, dirname) where cmd is the command to run
    # and dirname is the directory in which the command should be run.
    cmd_list = []
    for test in test_list:
        for i in range(test['iterations']):
            it_cmd = subst_vars(sim_cmd, {'seed': str(seed_gen.gen(i))})
            cmd_list.append(get_test_sim_cmd(it_cmd, test, i,
                                             output_dir, bin_dir, lsf_cmd))

    run_sim_commands(cmd_list, lsf_cmd is not None)


def compare_test_run(test, idx, iss, output_dir, report):
    '''Compare results for a single run of a single test

    Here, test is a dictionary describing the test (read from the testlist YAML
    file). idx is the iteration index. iss is the chosen instruction set
    simulator (currently supported: spike and ovpsim). output_dir is the base
    output directory (which should contain logs from both the ISS and the test
    run itself). report is the path to the regression report file we're
    writing.

    Returns True if the test run passed and False otherwise.

    '''
    test_name = test['test']
    elf = os.path.join(output_dir,
                       'instr_gen/asm_tests/{}.{}.o'.format(test_name, idx))

    logging.info("Comparing %s/DUT sim result : %s" % (iss, elf))

    with open(report, 'a') as report_fd:
        report_fd.write('Test binary: {}\n'.format(elf))

    rtl_dir = os.path.join(output_dir, 'rtl_sim',
                           '{}.{}'.format(test_name, idx))

    rtl_log = os.path.join(rtl_dir, 'trace_core_00000000.log')
    rtl_csv = os.path.join(rtl_dir, 'trace_core_00000000.csv')
    uvm_log = os.path.join(rtl_dir, 'sim.log')

    try:
        # Convert the RTL log file to a trace CSV.
        process_ibex_sim_log(rtl_log, rtl_csv, 1)
    except RuntimeError as e:
        with open(report, 'a') as report_fd:
            report_fd.write('Log processing failed: {}\n'.format(e))

        return False

    # Have a look at the UVM log. We should write out a message on failure or
    # if we are stopping at this point.
    no_post_compare = test.get('no_post_compare')
    if not check_ibex_uvm_log(uvm_log, "ibex", test_name, report,
                              write=(True if no_post_compare else 'onfail')):
        return False

    if no_post_compare:
        return True

    # There were no UVM errors. Process the log file from the ISS.
    iss_dir = os.path.join(output_dir, 'instr_gen', '{}_sim'.format(iss))

    iss_log = os.path.join(iss_dir, '{}.{}.log'.format(test_name, idx))
    iss_csv = os.path.join(iss_dir, '{}.{}.csv'.format(test_name, idx))

    if iss == "spike":
        process_spike_sim_log(iss_log, iss_csv)
    else:
        assert iss == 'ovpsim'  # (should be checked by argparse)
        process_ovpsim_sim_log(iss_log, iss_csv)

    compare_result = \
        compare_trace_csv(rtl_csv, iss_csv, "ibex", iss, report,
                          **test.get('compare_opts', {}))

    # Rather oddly, compare_result is a string. The comparison passed if it
    # starts with '[PASSED]'.
    return compare_result.startswith('[PASSED]')


def compare(test_list, iss, output_dir):
    """Compare RTL & ISS simulation reult

    Here, test_list is a list of tests read from the testlist YAML file. iss is
    the instruction set simulator that was used (must be 'spike' or 'ovpsim')
    and output_dir is the output directory which contains the results and where
    we'll write the regression log.

    """
    report = os.path.join(output_dir, 'regr.log')
    passes = 0
    fails = 0
    for test in test_list:
        for idx in range(test['iterations']):
            if compare_test_run(test, idx, iss, output_dir, report):
                passes += 1
            else:
                fails += 1

    summary = "{} PASSED, {} FAILED".format(passes, fails)
    with open(report, 'a') as report_fd:
        report_fd.write(summary + '\n')

    logging.info(summary)
    logging.info("RTL & ISS regression report at {}".format(report))

    return fails == 0


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
    for entry in os.scandir(base_dir):
        vdb_path = "%s/%s/rtl_sim/test.vdb" % (base_dir, entry.name)
        if 'seed' in entry.name:
            logging.info("Searching %s/%s for coverage database" %
                         (base_dir, entry.name))
            if os.path.exists(vdb_path):
                dir_list.append(vdb_path)
    if dir_list == []:
        logging.info("No coverage data available, exiting...")
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
    else:
        logging.error("%s is an unsuported simulator! Exiting..." % simulator)
        sys.exit(RET_FAIL)


def read_seed(arg):
    '''Read an argument to the --seed command line value'''
    try:
        seed = int(arg)
        if seed < 0:
            raise ValueError('bad seed')
        return seed

    except ValueError:
        raise argparse.ArgumentTypeError('Bad argument for --seed ({}): '
                                         'must be a non-negative integer.'
                                         .format(arg))


def main():
    '''Entry point when run as a script'''

    # Parse input arguments
    parser = argparse.ArgumentParser()

    parser.add_argument("--o", type=str, default="out",
                        help="Output directory name")
    parser.add_argument("--testlist", help="Regression testlist",
                        default=os.path.join(_CORE_IBEX,
                                             'riscv_dv_extension',
                                             'testlist.yaml'))
    parser.add_argument("--test", type=str, default="all",
                        help="Test name, 'all' means all tests in the list")
    parser.add_argument("--simulator", type=str, default="vcs",
                        help="RTL simulator to use (default: vcs)")
    parser.add_argument("--simulator_yaml",
                        help="RTL simulator setting YAML",
                        default=os.path.join(_CORE_IBEX,
                                             'yaml',
                                             'rtl_simulation.yaml'))
    parser.add_argument("--iss", default="spike",
                        choices=['spike', 'ovpsim'],
                        help="Instruction set simulator")
    parser.add_argument("-v", "--verbose", dest="verbose", action="store_true",
                        help="Verbose logging")
    parser.add_argument("--cmp_opts", type=str, default="",
                        help="Compile options for the generator")
    parser.add_argument("--sim_opts", type=str, default="",
                        help="Simulation options for the generator")
    parser.add_argument("--en_cov", action='store_true',
                        help="Enable coverage dump")
    parser.add_argument("--en_wave", action='store_true',
                        help="Enable waveform dump")
    parser.add_argument("--steps", type=str, default="all",
                        help="Run steps: compile,sim,compare,cov")
    parser.add_argument("--lsf_cmd", type=str,
                        help=("LSF command. Run locally if lsf "
                              "command is not specified"))

    sg = (parser.
          add_argument_group('Seeds and iterations',
                             'If none of the arguments in this section are '
                             'used, a random starting seed will be picked and '
                             'passed as --start_seed. The number of '
                             'iterations for each test will be read from the '
                             'configuration.'))

    sg.add_argument("--seed", type=read_seed, metavar='S',
                    help=("Randomization seed for the only iteration of each "
                          "test. Implies --iterations=1. Equivalently, pass "
                          "--start_seed and set iterations to 1."))
    sg.add_argument("--start_seed", type=read_seed, metavar='S',
                    help=("Randomization seed for the first iteration of each "
                          "test. Following iterations will use seeds S+1, "
                          "S+2, and so on."))
    sg.add_argument("--iterations", type=int,
                    help="Override the iteration count in the test list")

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
    bin_dir = ("%s/instr_gen/asm_tests" % args.o)
    subprocess.run(["mkdir", "-p", output_dir])

    steps = {
        'compile': args.steps == "all" or 'compile' in args.steps,
        'sim': args.steps == "all" or 'sim' in args.steps,
        'compare': args.steps == "all" or 'compare' in args.steps,
        'cov': args.steps == "all" or 'cov' in args.steps
    }

    compile_cmds = []
    sim_cmd = ""
    matched_list = []
    seed_gen = None

    if steps['compile'] or steps['sim']:
        enables = {
            'cov_opts': args.en_cov,
            'wave_opts': args.en_wave
        }
        compile_cmds, sim_cmd = get_simulator_cmd(args.simulator,
                                                  args.simulator_yaml, enables)

    if steps['sim'] or steps['compare']:
        seed_gen = SeedGen(args.seed, args.start_seed)
        if seed_gen.fixed:
            if not args.iterations:
                args.iterations = 1
            if args.iterations != 1:
                logging.error('Cannot set multiple --iterations with a '
                              'fixed seed.')
                return RET_FAIL

        process_regression_list(args.testlist, args.test, args.iterations or 0,
                                matched_list, _RISCV_DV_ROOT)
        if not matched_list:
            raise RuntimeError("Cannot find %s in %s" %
                               (args.test, args.testlist))

    # Compile TB
    if steps['compile']:
        rtl_compile(compile_cmds, output_dir, args.lsf_cmd, args.cmp_opts)

    # Run RTL simulation
    if steps['sim']:
        rtl_sim(sim_cmd, matched_list, seed_gen,
                args.sim_opts, output_dir, bin_dir, args.lsf_cmd)

    # Compare RTL & ISS simulation result.
    if steps['compare']:
        compare(matched_list, args.iss, args.o)

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
