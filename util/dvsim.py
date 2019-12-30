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
import glob
import logging as log
import os
import subprocess
import sys
from pathlib import Path

import hjson

from dvsim import SimCfg, utils

# TODO: add dvsim_cfg.hjson to retrieve this info
version = 0.1


# Function to resolve the scratch root directory among the available options:
# If set on the command line, then use that as a preference.
# Else, check if $SCRATCH_ROOT env variable exists and is a directory.
# Else use the default (<cwd>/scratch)
# Try to create the directory if it does not already exist.
def resolve_scratch_root(arg_scratch_root):
    scratch_root = os.environ.get('SCRATCH_ROOT')
    if arg_scratch_root == "scratch":
        if scratch_root == None:
            arg_scratch_root = os.getcwd() + '/' + arg_scratch_root
        else:
            # Scratch space could be mounted in a filesystem (such as NFS) on a network drive.
            # If the network is down, it could cause the access access check to hang. So run a
            # simple ls command with a timeout to prevent the hang.
            (out,
             status) = utils.run_cmd_with_timeout(cmd="ls -d " + scratch_root,
                                                  timeout=5,
                                                  exit_on_failure=0)
            if status == 0 and out != "":
                arg_scratch_root = scratch_root
            else:
                arg_scratch_root = os.getcwd() + '/' + arg_scratch_root
                log.warning(
                    "Env variable $SCRATCH_ROOT=\"%s\" is not accessible.\n" +
                    "Using \"%s\" instead.", scratch_root, arg_scratch_root)
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
        result = subprocess.run(["git", "branch", "--show-current"],
                                stdout=subprocess.PIPE)
        arg_branch = result.stdout.decode("utf-8").strip()
        if arg_branch == "":
            log.warning(
                "Failed to find current git branch. Setting it to \"master\"")
            arg_branch = "default"
    return (arg_branch)


# Get the project root directory path - this is used to construct the full paths
def get_proj_root():
    return os.path.abspath(os.path.dirname(os.path.realpath(__file__)) + "/..")


def main():
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)

    parser.add_argument(
        "-f",
        "--flow",
        default="sim",
        metavar="lint|elab|synth|formal|sim",
        help="which simulation flow' currently only dv flow supported")

    parser.add_argument(
        "--cfg",
        default="cfg.hjson",
        metavar="<file>",
        help="""simulation configuration file; if this is not supplied, it will
                              attempt to look for \"<flow>_cfg.hjson\" file in PWD"""
    )

    parser.add_argument(
        "items",
        nargs="*",
        default=["sanity"],
        metavar="""regr1, regr2, regr3|test1, test2, test3, ...""",
        help="""Indicate which regression or tests to run""")

    parser.add_argument(
        "--list",
        nargs="+",
        default=[],
        metavar="build_modes|run_modes|tests|regressions",
        help=
        """Provides a list of modes / tests / regressions available for use."""
    )

    parser.add_argument("-s",
                        "--simulator",
                        default="vcs",
                        metavar="vcs|xcelium",
                        help="simulator to use; the default is vcs")

    parser.add_argument(
        "-sr",
        "--scratch-root",
        default="scratch",
        metavar="path",
        help="""root scratch directory path where all build / run drectories go;
                      by default, the tool will create the {scratch_path} = {scratch_root}/{dut}
                      directory if it doesn't already exist; under {scratch_path}, there will be
                      {compile_set} set of directories where all the build outputs go and
                      {test_name} set of directories where the test outputs go"""
    )

    parser.add_argument(
        "-br",
        "--branch",
        metavar="<github-branch>",
        help="""GitHub branch name. This is used to construct the build and run
                              directories""")

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
                              these options will be passed on to all tests schedueld to be run"""
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
        "--seeds",
        nargs="+",
        default=[],
        metavar="seed0 seed1 ...",
        help=
        """Run tests with a specific seeds; if not specified, tool will use a
                              randomly generated seed""")

    parser.add_argument(
        "--reseed",
        type=int,
        default=-1,
        metavar="N",
        help="""repeat tests with N iterations with different seeds""")

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

    parser.add_argument("-p",
                        "--profile",
                        default="none",
                        metavar="time|mem",
                        help="turn on simulation profiling")

    parser.add_argument(
        "--job-prefix",
        default="",
        metavar="job-prefix",
        help="Job prefix before deploying the simulator commands.")

    parser.add_argument("--purge",
                        default=False,
                        action='store_true',
                        help="Clean the scratch directory.")

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
        default=32,
        metavar="N",
        help="""Run only upto a fixed number of builds/tests at a time.""")

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

    if args.cfg == "cfg.hjson": args.cfg = args.flow + "_" + args.cfg
    if not os.path.exists(args.cfg):
        log.fatal("Simulation config file %s appears to be invalid.", args.cfg)
        sys.exit(1)

    args.scratch_root = resolve_scratch_root(args.scratch_root)
    args.branch = resolve_branch(args.branch)
    args.cfg = os.path.abspath(args.cfg)

    cfg = SimCfg.SimCfg(proj_root=get_proj_root(), args=args)

    # sim_cfg_list = dvsim_parser.run(args)
    # dvsim_scheduler.dispatch(sim_cfg_list)


if __name__ == '__main__':
    main()
