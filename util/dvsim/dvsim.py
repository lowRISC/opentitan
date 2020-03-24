#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
dvsim is a command line tool to deploy regressions for design verification. It uses hjson as the
format for specifying what to build and run. It is an end-to-end regression manager that can deploy
multiple builds (where some tests might need different set of compile time options requiring a
uniquely build sim executable) in parallel followed by tests in parallel using the load balancer
of your choice. dvsim is built to be tool-agnostic so that you can easily switch between tools
available at your disposal. dvsim uses fusesoc as the starting step to resolve all inter-package
dependencies and provide us with a filelist that will be consumed by the sim tool.
"""

import argparse
import datetime
import logging as log
import os
import subprocess
import sys
from pathlib import Path

import Deploy
import LintCfg
import SimCfg
import utils

# TODO: add dvsim_cfg.hjson to retrieve this info
version = 0.1


# Function to resolve the scratch root directory among the available options:
# If set on the command line, then use that as a preference.
# Else, check if $SCRATCH_ROOT env variable exists and is a directory.
# Else use the default (<cwd>/scratch)
# Try to create the directory if it does not already exist.
def resolve_scratch_root(arg_scratch_root):
    scratch_root = os.environ.get('SCRATCH_ROOT')
    if arg_scratch_root == None or arg_scratch_root == "":
        if scratch_root == None:
            arg_scratch_root = os.getcwd() + "/scratch"
        else:
            # Scratch space could be mounted in a filesystem (such as NFS) on a network drive.
            # If the network is down, it could cause the access access check to hang. So run a
            # simple ls command with a timeout to prevent the hang.
            (out,
             status) = utils.run_cmd_with_timeout(cmd="ls -d " + scratch_root,
                                                  timeout=1,
                                                  exit_on_failure=0)
            if status == 0 and out != "":
                arg_scratch_root = scratch_root
            else:
                arg_scratch_root = os.getcwd() + "/scratch"
                log.warning(
                    "Env variable $SCRATCH_ROOT=\"%s\" is not accessible.\n" +
                    "Using \"%s\" instead.", scratch_root, arg_scratch_root)
    else:
        arg_scratch_root = os.path.realpath(arg_scratch_root)

    try:
        os.system("mkdir -p " + arg_scratch_root)
    except:
        log.fatal(
            "Invalid --scratch-root=\"%s\" switch - failed to create directory!",
            arg_scratch_root)
        sys.exit(1)
    return (arg_scratch_root)


# Set and return the current GitHub branch name, unless set on the command line.
# It runs "git branch --show-current". If the command fails, it throws a warning
# and sets the branch name to "default"
def resolve_branch(arg_branch):
    if arg_branch is None or arg_branch == "":
        result = subprocess.run(["git", "rev-parse", "--abbrev-ref", "HEAD"],
                                stdout=subprocess.PIPE)
        arg_branch = result.stdout.decode("utf-8").strip()
        if arg_branch == "":
            log.warning(
                "Failed to find current git branch. Setting it to \"default\"")
            arg_branch = "default"
    return (arg_branch)


# Get the project root directory path - this is used to construct the full paths
def get_proj_root():
    result = subprocess.run(["git", "rev-parse", "--show-toplevel"],
                            stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE)
    proj_root = result.stdout.decode("utf-8").strip()
    if proj_root == "":
        log.error(
            "Attempted to find the root of this GitHub repository by running:" \
            "\n..\nBut this command has failed:\n%s" %
                result.stderr.decode("utf-8"))
        sys.exit(1)
    return (proj_root)


def main():
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)

    parser.add_argument("cfg",
                        metavar="<cfg-hjson-file>",
                        help="""Configuration hjson file.""")

    parser.add_argument("-i",
                        "--items",
                        nargs="*",
                        default=["sanity"],
                        metavar="regr1, regr2, regr3|test1, test2, test3, ...",
                        help="""Indicate which regressions or tests to run.""")

    parser.add_argument(
        "-l",
        "--list",
        nargs="+",
        default=[],
        metavar="build_modes|run_modes|tests|regressions",
        help=
        """List the available build_modes / run_modes / tests / regressions for use."""
    )

    parser.add_argument("-t",
                        "--tool",
                        default="",
                        metavar="vcs|xcelium|ascentlint|...",
                        help="Override the tool that is set in hjson file")

    parser.add_argument(
        "-sr",
        "--scratch-root",
        metavar="path",
        help="""root scratch directory path where all build / run drectories go;
                      by default, the tool will create the {scratch_path} = {scratch_root}/{dut}
                      directory if it doesn't already exist; under {scratch_path}, there will be
                      {compile_set} set of directories where all the build outputs go and
                      {test_name} set of directories where the test outputs go"""
    )

    parser.add_argument("-pr",
                        "--proj-root",
                        metavar="path",
                        help="""Specify the root directory of the project.
                If this option is not passed, the tool will assume that this is
                a local GitHub repository and will attempt to automatically find
                the root directory.""")

    parser.add_argument(
        "-br",
        "--branch",
        default="",
        metavar="<branch-name>",
        help=
        """This variable is used to construct the scratch path directory name. If not
                specified, it defaults to the GitHub branch name. The idea is to uniquefy the
                scratch paths between different branches.""")

    parser.add_argument(
        "-bo",
        "--build-opts",
        nargs="+",
        default=[],
        metavar="",
        help="""pass additional build options over the command line;
                              note that if there are multiple compile sets identified to be built,
                              these options will be passed on to all of them"""
    )

    parser.add_argument(
        "-bm",
        "--build-modes",
        nargs="+",
        default=[],
        metavar="",
        help="""Set build modes on the command line for all tests run as a part
                              of the regression.""")

    parser.add_argument(
        "-ro",
        "--run-opts",
        nargs="+",
        default=[],
        metavar="",
        help="""pass additional run time options over the command line;
                              these options will be passed on to all tests scheduled to be run"""
    )

    parser.add_argument(
        "-rm",
        "--run-modes",
        nargs="+",
        default=[],
        metavar="",
        help="""Set run modes on the command line for all tests run as a part
                              of the regression.""")

    parser.add_argument(
        "-bu",
        "--build-unique",
        default=False,
        action='store_true',
        help=
        """By default, under the {scratch} directory, there is a {compile_set}
                              directory created where the build output goes; this can be
                              uniquified by appending the current timestamp. This is suitable
                              for the case when a test / regression already running and you want
                              to run something else from a different terminal without affecting
                              the previous one""")

    parser.add_argument(
        "--build-only",
        default=False,
        action='store_true',
        help="Only build the simulation executables for the givem items.")

    parser.add_argument(
        "--run-only",
        default=False,
        action='store_true',
        help="Assume sim exec is available and proceed to run step")

    parser.add_argument(
        "-s",
        "--seeds",
        nargs="+",
        default=[],
        metavar="seed0 seed1 ...",
        help=
        """Run tests with a specific seeds. Note that these specific seeds are applied to
           items being run in the order they are passed.""")

    parser.add_argument(
        "--fixed-seed",
        type=int,
        default=None,
        help="""Run all items with a fixed seed value. This option enforces
           --reseed 1.""")

    parser.add_argument(
        "-r",
        "--reseed",
        type=int,
        default=-1,
        metavar="N",
        help="""Repeat tests with N iterations with different seeds""")

    parser.add_argument("-rx",
                        "--reseed-multiplier",
                        type=int,
                        default=1,
                        metavar="N",
                        help="""Multiplier for existing reseed values.""")

    parser.add_argument("-w",
                        "--waves",
                        default=False,
                        action='store_true',
                        help="Enable dumping of waves")

    parser.add_argument("-d",
                        "--dump",
                        default="fsdb",
                        metavar="fsdb|shm",
                        help="Dump waves in fsdb or shm.")

    parser.add_argument("-mw",
                        "--max-waves",
                        type=int,
                        default=5,
                        metavar="N",
                        help="""enable dumpling of waves for at most N tests;
                              this includes tests scheduled for run AND automatic rerun"""
                        )

    parser.add_argument("-c",
                        "--cov",
                        default=False,
                        action='store_true',
                        help="turn on coverage collection")

    parser.add_argument(
        "--cov-merge-previous",
        default=False,
        action='store_true',
        help="""Applicable when --cov switch is enabled. If a previous cov
                        database directory exists, this switch will cause it to be merged with
                        the current cov database.""")

    parser.add_argument(
        "--cov-analyze",
        default=False,
        action='store_true',
        help="Analyze the coverage from the last regression result.")

    parser.add_argument("-p",
                        "--profile",
                        default="none",
                        metavar="time|mem",
                        help="Turn on simulation profiling")

    parser.add_argument("--xprop-off",
                        default=False,
                        action='store_true',
                        help="Turn off Xpropagation")

    parser.add_argument("--job-prefix",
                        default="",
                        metavar="job-prefix",
                        help="Job prefix before deploying the tool commands.")

    parser.add_argument("--purge",
                        default=False,
                        action='store_true',
                        help="Clean the scratch directory before running.")

    parser.add_argument(
        "-mo",
        "--max-odirs",
        type=int,
        default=5,
        metavar="N",
        help="""When tests are run, the older runs are backed up. This switch
                              limits the number of backup directories being maintained."""
    )

    parser.add_argument(
        "--no-rerun",
        default=False,
        action='store_true',
        help=
        """by default, failing tests will be automatically be rerun with waves;
                              this option will prevent the rerun from being triggered"""
    )

    parser.add_argument("--skip-ral",
                        default=False,
                        action='store_true',
                        help="""Skip the ral generation step.""")

    parser.add_argument("-v",
                        "--verbosity",
                        default="l",
                        metavar="n|l|m|h|d",
                        help="""set verbosity to none/low/medium/high/debug;
                              This will override any setting added to any of the hjson files
                              used for config""")

    parser.add_argument("--email",
                        nargs="+",
                        default=[],
                        metavar="",
                        help="""email the report to specified addresses""")

    parser.add_argument(
        "--verbose",
        nargs="?",
        default=None,
        const="default",
        metavar="debug",
        help="""Print verbose dvsim tool messages. If 'debug' is passed, then the
                              volume of messages is ven higher.""")

    parser.add_argument("--version",
                        default=False,
                        action='store_true',
                        help="Print version and exit")

    parser.add_argument(
        "-n",
        "--dry-run",
        default=False,
        action='store_true',
        help=
        "Print dvsim tool messages only, without actually running any command")

    parser.add_argument(
        "--map-full-testplan",
        default=False,
        action='store_true',
        help="Force complete testplan annotated results to be shown at the end."
    )

    parser.add_argument(
        "--publish",
        default=False,
        action='store_true',
        help="Publish results to the reports.opentitan.org web server.")

    parser.add_argument(
        "-pi",
        "--print-interval",
        type=int,
        default=10,
        metavar="N",
        help="""Interval in seconds. Print status every N seconds.""")

    parser.add_argument(
        "-mp",
        "--max-parallel",
        type=int,
        default=16,
        metavar="N",
        help="""Run only upto a fixed number of builds/tests at a time.""")

    parser.add_argument(
        "--local",
        default=False,
        action='store_true',
        help=
        """Deploy builds and runs on the local workstation instead of the compute farm.
        Support for this has not been added yet.""")

    args = parser.parse_args()

    if args.version:
        print(version)
        sys.exit()

    # Add log level 'VERBOSE' between INFO and DEBUG
    log.addLevelName(utils.VERBOSE, 'VERBOSE')

    log_format = '%(levelname)s: [%(module)s] %(message)s'
    log_level = log.INFO
    if args.verbose == "default": log_level = utils.VERBOSE
    elif args.verbose == "debug": log_level = log.DEBUG
    log.basicConfig(format=log_format, level=log_level)

    if not os.path.exists(args.cfg):
        log.fatal("Path to config file %s appears to be invalid.", args.cfg)
        sys.exit(1)

    # If publishing results, then force full testplan mapping of results.
    if args.publish: args.map_full_testplan = True

    args.scratch_root = resolve_scratch_root(args.scratch_root)
    args.branch = resolve_branch(args.branch)
    args.cfg = os.path.abspath(args.cfg)

    # Add timestamp to args that all downstream objects can use.
    # Static variables - indicate timestamp.
    ts_format_long = "%A %B %d %Y %I:%M:%S%p %Z"
    ts_format = "%a.%m.%d.%y__%I.%M.%S%p"
    curr_ts = datetime.datetime.now()
    timestamp_long = curr_ts.strftime(ts_format_long)
    timestamp = curr_ts.strftime(ts_format)
    setattr(args, "ts_format_long", ts_format_long)
    setattr(args, "ts_format", ts_format)
    setattr(args, "timestamp_long", timestamp_long)
    setattr(args, "timestamp", timestamp)

    # Register the seeds from command line with RunTest class.
    Deploy.RunTest.seeds = args.seeds
    # If we are fixing a seed value, no point in tests having multiple reseeds.
    if args.fixed_seed: args.reseed = 1
    Deploy.RunTest.fixed_seed = args.fixed_seed

    # Register the common deploy settings.
    Deploy.Deploy.print_interval = args.print_interval
    Deploy.Deploy.max_parallel = args.max_parallel
    Deploy.Deploy.max_odirs = args.max_odirs

    # Build infrastructure from hjson file and create the list of items to
    # be deployed.

    # Sets the project root directory: either specified from the command line
    # or set by automatically assuming we are in a GitHub repository and
    # automatically finding the root of this repository.
    if args.proj_root:
        proj_root = args.proj_root
    else:
        proj_root = get_proj_root()

    # TODO: SimCfg item below implies DV - need to solve this once we add FPV
    # and other ASIC flow targets.
    if args.tool == 'ascentlint':
        cfg = LintCfg.LintCfg(args.cfg, proj_root, args)
    else:
        cfg = SimCfg.SimCfg(args.cfg, proj_root, args)

    # List items available for run if --list switch is passed, and exit.
    if args.list != []:
        cfg.print_list()
        sys.exit(0)

    # In simulation mode: if --cov-analyze switch is passed, then run the GUI
    # tool.
    if args.cov_analyze:
        cfg.cov_analyze()
        sys.exit(0)

    # Purge the scratch path if --purge option is set.
    if args.purge:
        cfg.purge()

    # Deploy the builds and runs
    if args.items != []:
        # Create deploy objects.
        cfg.create_deploy_objects()
        cfg.deploy_objects()

        # Generate results.
        cfg.gen_results()

        # Publish results
        if args.publish: cfg.publish_results()

    else:
        log.info("No items specified to be run.")

    # Exit with non-zero status if there were errors or failures.
    if cfg.has_errors():
        log.error("Errors were encountered in this run.")
        sys.exit(1)


if __name__ == '__main__':
    main()
