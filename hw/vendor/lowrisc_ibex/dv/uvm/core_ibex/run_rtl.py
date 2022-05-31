#!/usr/bin/env python3

import argparse
import os
import re
import subprocess
import sys
from typing import Tuple

from sim_cmd import get_simulator_cmd
from test_entry import get_test_entry

_CORE_IBEX = os.path.normpath(os.path.join(os.path.dirname(__file__)))

_TestAndSeed = Tuple[str, int]


def read_test_dot_seed(arg: str) -> _TestAndSeed:
    '''Read a value for --test-dot-seed'''

    match = re.match(r'([^.]+)\.([0-9]+)$', arg)
    if match is None:
        raise argparse.ArgumentTypeError('Bad --test-dot-seed ({}): '
                                         'should be of the form TEST.SEED.'
                                         .format(arg))

    return (match.group(1), int(match.group(2), 10))


def subst_vars(string, var_dict):
    '''Apply substitutions in var_dict to string

    If var_dict[K] = V, then <K> will be replaced with V in string.'''
    for key, value in var_dict.items():
        string = string.replace('<{}>'.format(key), value)
    return string


def get_test_sim_cmd(base_cmd, test, idx, seed, sim_dir, bin_dir, lsf_cmd):
    '''Generate the command that runs a test iteration in the simulator

    base_cmd is the command to use before any test-specific substitutions. test
    is a dictionary describing the test (originally read from the testlist YAML
    file). idx is the test iteration (an integer) and seed is the corresponding
    seed.

    sim_dir is the directory to which the test results will be written. bin_dir
    is the directory containing compiled binaries. lsf_cmd (if not None) is a
    string that runs bsub to submit the task on LSF.

    Returns the command to run.

    '''
    it_cmd = subst_vars(base_cmd, {'seed': str(seed)})
    sim_cmd = (it_cmd + ' ' + test['sim_opts'].replace('\n', ' ')
               if "sim_opts" in test
               else it_cmd)

    test_name = test['test']

    binary = os.path.join(bin_dir, '{}_{}.bin'.format(test_name, idx))

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

    return sim_cmd


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--simulator', required=True)
    parser.add_argument("--simulator_yaml", required=True)
    parser.add_argument("--en_cov", action='store_true')
    parser.add_argument("--en_wave", action='store_true')
    parser.add_argument('--start-seed', type=int, required=True)
    parser.add_argument('--test-dot-seed',
                        type=read_test_dot_seed,
                        required=True)
    parser.add_argument('--lsf-cmd')
    parser.add_argument('--bin-dir', required=True)
    parser.add_argument('--rtl-sim-dir', required=True)
    parser.add_argument('--sim-opts', default='')

    args = parser.parse_args()

    if args.start_seed < 0:
        raise RuntimeError('Invalid start seed: {}'.format(args.start_seed))
    testname, seed = args.test_dot_seed
    if seed < args.start_seed:
        raise RuntimeError('Start seed is greater than test seed '
                           f'({args.start_seed} > {seed}).')

    iteration = seed - args.start_seed

    entry = get_test_entry(testname)

    # Look up how to run the simulator in general
    enables = {
        'cov_opts': args.en_cov,
        'wave_opts': args.en_wave
    }
    _, base_cmd = get_simulator_cmd(args.simulator,
                                    args.simulator_yaml, enables)

    # Specialize base_cmd with the right directories and simulator options
    sim_cmd = subst_vars(base_cmd,
                         {
                             'out': args.rtl_sim_dir,
                             'sim_opts': args.sim_opts,
                             'cwd': _CORE_IBEX,
                         })

    # Specialize base_cmd for this specific test
    test_sim_dir = os.path.join(args.rtl_sim_dir,
                                '{}.{}'.format(testname, seed))
    test_cmd = get_test_sim_cmd(sim_cmd, entry, iteration, seed,
                                test_sim_dir, args.bin_dir, args.lsf_cmd)

    # Run test_cmd (it's a string, so we have to call out to the shell to do
    # so). Note that we don't capture the success or failure of the subprocess:
    # if something goes horribly wrong, we assume we won't have a matching
    # trace.
    sim_log = os.path.join(test_sim_dir, 'sim.log')
    with open(sim_log, 'wb') as sim_fd:
        subprocess.run(test_cmd, shell=True, stdout=sim_fd, stderr=sim_fd)

    # Always return 0 (success), even if the test failed. We've successfully
    # generated a log either way.
    return 0


if __name__ == '__main__':
    sys.exit(main())
