#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""dvsim is a command line tool to deploy ASIC tool flows such as regressions
for design verification (DV), formal property verification (FPV), linting and
synthesis.

It uses hjson as the format for specifying what to build and run. It is an
end-to-end regression manager that can deploy multiple builds (where some tests
might need different set of compile time options requiring a uniquely build sim
executable) in parallel followed by tests in parallel using the load balancer
of your choice.

dvsim is built to be tool-agnostic so that you can easily switch between the
tools at your disposal. dvsim uses fusesoc as the starting step to resolve all
inter-package dependencies and provide us with a filelist that will be consumed
by the sim tool.

"""

import argparse
import datetime
import logging as log
import os
import shlex
import subprocess
import sys
import textwrap
from pathlib import Path

import Launcher
import LauncherFactory
import LocalLauncher
from CfgFactory import make_cfg
from Deploy import RunTest
from Timer import Timer
from utils import (TS_FORMAT, TS_FORMAT_LONG, VERBOSE, rm_path,
                   run_cmd_with_timeout)

# TODO: add dvsim_cfg.hjson to retrieve this info
version = 0.1

# The different categories that can be passed to the --list argument.
_LIST_CATEGORIES = ["build_modes", "run_modes", "tests", "regressions"]


# Function to resolve the scratch root directory among the available options:
# If set on the command line, then use that as a preference.
# Else, check if $SCRATCH_ROOT env variable exists and is a directory.
# Else use the default (<proj_root>/scratch)
# Try to create the directory if it does not already exist.
def resolve_scratch_root(arg_scratch_root, proj_root):
    default_scratch_root = proj_root + "/scratch"
    scratch_root = os.environ.get('SCRATCH_ROOT')
    if not arg_scratch_root:
        if scratch_root is None:
            arg_scratch_root = default_scratch_root
        else:
            # Scratch space could be mounted in a filesystem (such as NFS) on a network drive.
            # If the network is down, it could cause the access access check to hang. So run a
            # simple ls command with a timeout to prevent the hang.
            (out, status) = run_cmd_with_timeout(cmd="ls -d " + scratch_root,
                                                 timeout=1,
                                                 exit_on_failure=0)
            if status == 0 and out != "":
                arg_scratch_root = scratch_root
            else:
                arg_scratch_root = default_scratch_root
                log.warning(
                    "Env variable $SCRATCH_ROOT=\"{}\" is not accessible.\n"
                    "Using \"{}\" instead.".format(scratch_root,
                                                   arg_scratch_root))
    else:
        arg_scratch_root = os.path.realpath(arg_scratch_root)

    try:
        os.makedirs(arg_scratch_root, exist_ok=True)
    except PermissionError as e:
        log.fatal("Failed to create scratch root {}:\n{}.".format(
            arg_scratch_root, e))
        sys.exit(1)

    if not os.access(arg_scratch_root, os.W_OK):
        log.fatal("Scratch root {} is not writable!".format(arg_scratch_root))
        sys.exit(1)

    return arg_scratch_root


def read_max_parallel(arg):
    '''Take value for --max-parallel as an integer'''
    try:
        int_val = int(arg)
        if int_val <= 0:
            raise ValueError('bad value')
        return int_val

    except ValueError:
        raise argparse.ArgumentTypeError(
            'Bad argument for --max-parallel '
            '({!r}): must be a positive integer.'.format(arg))


def resolve_max_parallel(arg):
    '''Pick a value of max_parallel, defaulting to 16 or $DVSIM_MAX_PARALLEL'''
    if arg is not None:
        assert arg > 0
        return arg

    from_env = os.environ.get('DVSIM_MAX_PARALLEL')
    if from_env is not None:
        try:
            return read_max_parallel(from_env)
        except argparse.ArgumentTypeError:
            log.warning('DVSIM_MAX_PARALLEL environment variable has value '
                        '{!r}, which is not a positive integer. Using default '
                        'value (16).'.format(from_env))

    return 16


def resolve_branch(branch):
    '''Choose a branch name for output files

    If the --branch argument was passed on the command line, the branch
    argument is the branch name to use. Otherwise it is None and we use git to
    find the name of the current branch in the working directory.

    '''

    if branch is not None:
        return branch

    result = subprocess.run(["git", "rev-parse", "--abbrev-ref", "HEAD"],
                            stdout=subprocess.PIPE)
    branch = result.stdout.decode("utf-8").strip()
    if not branch:
        log.warning("Failed to find current git branch. "
                    "Setting it to \"default\"")
        branch = "default"

    return branch


# Get the project root directory path - this is used to construct the full paths
def get_proj_root():
    cmd = ["git", "rev-parse", "--show-toplevel"]
    result = subprocess.run(cmd,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE)
    proj_root = result.stdout.decode("utf-8").strip()
    if not proj_root:
        log.error(
            "Attempted to find the root of this GitHub repository by running:\n"
            "{}\n"
            "But this command has failed:\n"
            "{}".format(' '.join(cmd), result.stderr.decode("utf-8")))
        sys.exit(1)
    return (proj_root)


def resolve_proj_root(args):
    '''Update proj_root based on how DVSim is invoked.

    If --remote switch is set, a location in the scratch area is chosen as the
    new proj_root. The entire repo is copied over to this location. Else, the
    proj_root is discovered using get_proj_root() method, unless the user
    overrides it on the command line.

    This function returns the updated proj_root src and destination path. If
    --remote switch is not set, the destination path is identical to the src
    path. Likewise, if --dry-run is set.
    '''
    proj_root_src = args.proj_root or get_proj_root()

    # Check if jobs are dispatched to external compute machines. If yes,
    # then the repo needs to be copied over to the scratch area
    # accessible to those machines.
    # If --purge arg is set, then purge the repo_top that was copied before.
    if args.remote and not args.dry_run:
        proj_root_dest = os.path.join(args.scratch_root, args.branch,
                                      "repo_top")
        if args.purge:
            rm_path(proj_root_dest)
        copy_repo(proj_root_src, proj_root_dest)
    else:
        proj_root_dest = proj_root_src

    return proj_root_src, proj_root_dest


def copy_repo(src, dest):
    '''Copy over the repo to a new location.

    The repo is copied over from src to dest area. It tentatively uses the
    rsync utility which provides the ability to specify a file containing some
    exclude patterns to skip certain things from being copied over. With GitHub
    repos, an existing `.gitignore` serves this purpose pretty well.
    '''
    rsync_cmd = [
        "rsync", "--recursive", "--links", "--checksum", "--update",
        "--inplace", "--no-group"
    ]

    # Supply `.gitignore` from the src area to skip temp files.
    ignore_patterns_file = os.path.join(src, ".gitignore")
    if os.path.exists(ignore_patterns_file):
        # TODO: hack - include hw/foundry since it is excluded in .gitignore.
        rsync_cmd += [
            "--include=hw/foundry",
            "--exclude-from={}".format(ignore_patterns_file), "--exclude=.*"
        ]

    rsync_cmd += [src + "/.", dest]
    rsync_str = ' '.join([shlex.quote(w) for w in rsync_cmd])

    cmd = ["flock", "--timeout", "600", dest, "--command", rsync_str]

    log.info("[copy_repo] [dest]: %s", dest)
    log.log(VERBOSE, "[copy_repo] [cmd]: \n%s", ' '.join(cmd))

    # Make sure the dest exists first.
    os.makedirs(dest, exist_ok=True)
    try:
        subprocess.run(cmd,
                       check=True,
                       stdout=subprocess.PIPE,
                       stderr=subprocess.PIPE)
    except subprocess.CalledProcessError as e:
        log.error("Failed to copy over %s to %s: %s", src, dest,
                  e.stderr.decode("utf-8").strip())
    log.info("Done.")


def wrapped_docstring():
    '''Return a text-wrapped version of the module docstring'''
    paras = []
    para = []
    for line in __doc__.strip().split('\n'):
        line = line.strip()
        if not line:
            if para:
                paras.append('\n'.join(para))
                para = []
        else:
            para.append(line)
    if para:
        paras.append('\n'.join(para))

    return '\n\n'.join(textwrap.fill(p) for p in paras)


def parse_args():
    parser = argparse.ArgumentParser(
        description=wrapped_docstring(),
        formatter_class=argparse.RawDescriptionHelpFormatter)

    parser.add_argument("cfg",
                        metavar="<cfg-hjson-file>",
                        help="""Configuration hjson file.""")

    parser.add_argument("--version",
                        action='store_true',
                        help="Print version and exit")

    parser.add_argument(
        "--tool",
        "-t",
        help=("Explicitly set the tool to use. This is "
              "optional for running simulations (where it can "
              "be set in an .hjson file), but is required for "
              "other flows. Possible tools include: vcs, "
              "xcelium, ascentlint, veriblelint, verilator, dc."))

    parser.add_argument("--list",
                        "-l",
                        nargs="*",
                        metavar='CAT',
                        choices=_LIST_CATEGORIES,
                        help=('Parse the the given .hjson config file, list '
                              'the things that can be run, then exit. The '
                              'list can be filtered with a space-separated '
                              'of categories from: {}.'.format(
                                  ', '.join(_LIST_CATEGORIES))))

    whatg = parser.add_argument_group('Choosing what to run')

    whatg.add_argument("-i",
                       "--items",
                       nargs="*",
                       default=["smoke"],
                       help=('Specify the regressions or tests to run. '
                             'Defaults to "smoke", but can be a '
                             'space separated list of test or regression '
                             'names.'))

    whatg.add_argument("--select-cfgs",
                       nargs="*",
                       metavar="CFG",
                       help=('The .hjson file is a primary config. Only run '
                             'the given configs from it. If this argument is '
                             'not used, dvsim will process all configs listed '
                             'in a primary config.'))

    disg = parser.add_argument_group('Dispatch options')

    disg.add_argument("--job-prefix",
                      default="",
                      metavar="PFX",
                      help=('Prepend this string when running each tool '
                            'command.'))

    disg.add_argument("--local",
                      action='store_true',
                      help=('Force jobs to be dispatched locally onto user\'s '
                            'machine.'))

    disg.add_argument("--remote",
                      action='store_true',
                      help=('Trigger copying of the repo to scratch area.'))

    disg.add_argument("--max-parallel",
                      "-mp",
                      type=read_max_parallel,
                      metavar="N",
                      help=('Run only up to N builds/tests at a time. '
                            'Default value 16, unless the DVSIM_MAX_PARALLEL '
                            'environment variable is set, in which case that '
                            'is used. Only applicable when launching jobs '
                            'locally.'))

    pathg = parser.add_argument_group('File management')

    pathg.add_argument("--scratch-root",
                       "-sr",
                       metavar="PATH",
                       help=('Destination for build / run directories. If not '
                             'specified, uses the path in the SCRATCH_ROOT '
                             'environment variable, if set, or ./scratch '
                             'otherwise.'))

    pathg.add_argument("--proj-root",
                       "-pr",
                       metavar="PATH",
                       help=('The root directory of the project. If not '
                             'specified, dvsim will search for a git '
                             'repository containing the current directory.'))

    pathg.add_argument("--branch",
                       "-br",
                       metavar='B',
                       help=('By default, dvsim creates files below '
                             '{scratch-root}/{dut}.{flow}.{tool}/{branch}. '
                             'If --branch is not specified, dvsim assumes the '
                             'current directory is a git repository and uses '
                             'the name of the current branch.'))

    pathg.add_argument("--max-odirs",
                       "-mo",
                       type=int,
                       default=5,
                       metavar="N",
                       help=('When tests are run, older runs are backed '
                             'up. Discard all but the N most recent (defaults '
                             'to 5).'))

    pathg.add_argument("--purge",
                       action='store_true',
                       help="Clean the scratch directory before running.")

    buildg = parser.add_argument_group('Options for building')

    buildg.add_argument("--build-only",
                        "-bu",
                        action='store_true',
                        help=('Stop after building executables for the given '
                              'items.'))

    buildg.add_argument("--build-unique",
                        action='store_true',
                        help=('Append a timestamp to the directory in which '
                              'files are built. This is suitable for the case '
                              'when another test is already running and you '
                              'want to run something else from a different '
                              'terminal without affecting it.'))

    buildg.add_argument("--build-opts",
                        "-bo",
                        nargs="+",
                        default=[],
                        metavar="OPT",
                        help=('Additional options passed on the command line '
                              'each time a build tool is run.'))

    buildg.add_argument("--build-modes",
                        "-bm",
                        nargs="+",
                        default=[],
                        metavar="MODE",
                        help=('The options for each build_mode in this list '
                              'are applied to all build and run targets.'))

    disg.add_argument("--gui",
                      action='store_true',
                      help=('Run the flow in interactive mode instead of the '
                            'batch mode.'))

    rung = parser.add_argument_group('Options for running')

    rung.add_argument("--run-only",
                      "-ru",
                      action='store_true',
                      help=('Skip the build step (assume that simulation '
                            'executables have already been built).'))

    rung.add_argument("--run-opts",
                      "-ro",
                      nargs="+",
                      default=[],
                      metavar="OPT",
                      help=('Additional options passed on the command line '
                            'each time a test is run.'))

    rung.add_argument("--run-modes",
                      "-rm",
                      nargs="+",
                      default=[],
                      metavar="MODE",
                      help=('The options for each run_mode in this list are '
                            'applied to each simulation run.'))

    rung.add_argument("--profile",
                      "-p",
                      nargs="?",
                      choices=['time', 'mem'],
                      const="time",
                      metavar="P",
                      help=('Turn on simulation profiling (where P is time '
                            'or mem).'))

    rung.add_argument("--xprop-off",
                      action='store_true',
                      help="Turn off X-propagation in simulation.")

    rung.add_argument("--no-rerun",
                      action='store_true',
                      help=("Disable the default behaviour, where failing "
                            "tests are automatically rerun with waves "
                            "enabled."))

    rung.add_argument("--verbosity",
                      "-v",
                      choices=['n', 'l', 'm', 'h', 'f', 'd'],
                      metavar='V',
                      help=('Set tool/simulation verbosity to none (n), low '
                            '(l), medium (m), high (h), full (f) or debug (d).'
                            ' The default value is set in config files.'))

    seedg = parser.add_argument_group('Test seeds')

    seedg.add_argument("--seeds",
                       "-s",
                       nargs="+",
                       default=[],
                       metavar="S",
                       help=('A list of seeds for tests. Note that these '
                             'specific seeds are applied to items being run '
                             'in the order they are passed.'))

    seedg.add_argument("--fixed-seed",
                       type=int,
                       metavar='S',
                       help=('Run all items with the seed S. This implies '
                             '--reseed 1.'))

    seedg.add_argument("--reseed",
                       "-r",
                       type=int,
                       metavar="N",
                       help=('Override any reseed value in the test '
                             'configuration and run each test N times, with '
                             'a new seed each time.'))

    seedg.add_argument("--reseed-multiplier",
                       "-rx",
                       type=int,
                       default=1,
                       metavar="N",
                       help=('Scale each reseed value in the test '
                             'configuration by N. This allows e.g. running '
                             'the tests 10 times as much as normal while '
                             'maintaining the ratio of numbers of runs '
                             'between different tests.'))

    waveg = parser.add_argument_group('Dumping waves')

    waveg.add_argument(
        "--waves",
        "-w",
        nargs="?",
        choices=["default", "fsdb", "shm", "vpd", "vcd", "evcd", "fst"],
        const="default",
        help=("Enable dumping of waves. It takes an optional "
              "argument to pick the desired wave format. If "
              "the optional argument is not supplied, it picks "
              "whatever is the default for the chosen tool. "
              "By default, dumping waves is not enabled."))

    waveg.add_argument("--max-waves",
                       "-mw",
                       type=int,
                       default=5,
                       metavar="N",
                       help=('Only dump waves for the first N tests run. This '
                             'includes both tests scheduled for run and those '
                             'that are automatically rerun.'))

    covg = parser.add_argument_group('Generating simulation coverage')

    covg.add_argument("--cov",
                      "-c",
                      action='store_true',
                      help="Enable collection of coverage data.")

    covg.add_argument("--cov-merge-previous",
                      action='store_true',
                      help=('Only applicable with --cov. Merge any previous '
                            'coverage database directory with the new '
                            'coverage database.'))

    covg.add_argument("--cov-unr",
                      action='store_true',
                      help=('Run coverage UNR analysis and generate report. '
                            'This only supports VCS now.'))

    covg.add_argument("--cov-analyze",
                      action='store_true',
                      help=('Rather than building or running any tests, '
                            'analyze the coverage from the last run.'))

    pubg = parser.add_argument_group('Generating and publishing results')

    pubg.add_argument("--map-full-testplan",
                      action='store_true',
                      help=("Show complete testplan annotated results "
                            "at the end."))

    pubg.add_argument("--publish",
                      action='store_true',
                      help="Publish results to reports.opentitan.org.")

    dvg = parser.add_argument_group('Controlling DVSim itself')

    dvg.add_argument("--print-interval",
                     "-pi",
                     type=int,
                     default=10,
                     metavar="N",
                     help="Print status every N seconds.")

    dvg.add_argument("--verbose",
                     nargs="?",
                     choices=['default', 'debug'],
                     const="default",
                     metavar="D",
                     help=('With no argument, print verbose dvsim tool '
                           'messages. With --verbose=debug, the volume of '
                           'messages is even higher.'))

    dvg.add_argument("--dry-run",
                     "-n",
                     action='store_true',
                     help=("Print dvsim tool messages but don't actually "
                           "run any command"))

    args = parser.parse_args()

    if args.version:
        print(version)
        sys.exit()

    # We want the --list argument to default to "all categories", but allow
    # filtering. If args.list is None, then --list wasn't supplied. If it is
    # [], then --list was supplied with no further arguments and we want to
    # list all categories.
    if args.list == []:
        args.list = _LIST_CATEGORIES

    # Get max_parallel from environment if it wasn't specified on the command
    # line.
    args.max_parallel = resolve_max_parallel(args.max_parallel)
    assert args.max_parallel > 0

    return args


def main():
    args = parse_args()

    # Add log level 'VERBOSE' between INFO and DEBUG
    log.addLevelName(VERBOSE, 'VERBOSE')

    log_format = '%(levelname)s: [%(module)s] %(message)s'
    log_level = log.INFO
    if args.verbose == "default":
        log_level = VERBOSE
    elif args.verbose == "debug":
        log_level = log.DEBUG
    log.basicConfig(format=log_format, level=log_level)

    if not os.path.exists(args.cfg):
        log.fatal("Path to config file %s appears to be invalid.", args.cfg)
        sys.exit(1)

    # If publishing results, then force full testplan mapping of results.
    if args.publish:
        args.map_full_testplan = True

    args.branch = resolve_branch(args.branch)
    proj_root_src, proj_root = resolve_proj_root(args)
    args.scratch_root = resolve_scratch_root(args.scratch_root, proj_root)
    log.info("[proj_root]: %s", proj_root)

    # Create an empty FUSESOC_IGNORE file in scratch_root. This ensures that
    # any fusesoc invocation from a job won't search within scratch_root for
    # core files.
    (Path(args.scratch_root) / 'FUSESOC_IGNORE').touch()

    args.cfg = os.path.abspath(args.cfg)
    if args.remote:
        cfg_path = args.cfg.replace(proj_root_src + "/", "")
        args.cfg = os.path.join(proj_root, cfg_path)

    # Add timestamp to args that all downstream objects can use.
    curr_ts = datetime.datetime.utcnow()
    setattr(args, "timestamp_long", curr_ts.strftime(TS_FORMAT_LONG))
    setattr(args, "timestamp", curr_ts.strftime(TS_FORMAT))

    # Register the seeds from command line with RunTest class.
    RunTest.seeds = args.seeds
    # If we are fixing a seed value, no point in tests having multiple reseeds.
    if args.fixed_seed:
        args.reseed = 1
    RunTest.fixed_seed = args.fixed_seed

    # Register the common deploy settings.
    Timer.print_interval = args.print_interval
    LocalLauncher.LocalLauncher.max_parallel = args.max_parallel
    Launcher.Launcher.max_odirs = args.max_odirs
    LauncherFactory.set_launcher_type(args.local)

    # Build infrastructure from hjson file and create the list of items to
    # be deployed.
    global cfg
    cfg = make_cfg(args.cfg, args, proj_root)

    # List items available for run if --list switch is passed, and exit.
    if args.list is not None:
        cfg.print_list()
        sys.exit(0)

    # Purge the scratch path if --purge option is set.
    if args.purge:
        cfg.purge()

    # If --cov-unr is passed, run UNR to generate report for unreachable
    # exclusion file.
    if args.cov_unr:
        cfg.cov_unr()
        cfg.deploy_objects()
        sys.exit(0)

    # In simulation mode: if --cov-analyze switch is passed, then run the GUI
    # tool.
    if args.cov_analyze:
        cfg.cov_analyze()
        cfg.deploy_objects()
        sys.exit(0)

    # Deploy the builds and runs
    if args.items != []:
        # Create deploy objects.
        cfg.create_deploy_objects()
        results = cfg.deploy_objects()

        # Generate results.
        cfg.gen_results(results)

        # Publish results
        if args.publish:
            cfg.publish_results()

    else:
        log.info("No items specified to be run.")

    # Exit with non-zero status if there were errors or failures.
    if cfg.has_errors():
        log.error("Errors were encountered in this run.")
        sys.exit(1)


if __name__ == '__main__':
    main()
