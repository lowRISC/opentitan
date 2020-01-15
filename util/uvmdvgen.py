#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Command-line tool to autogenerate boilerplate DV testbench code extended from dv_lib / cip_lib
"""
import argparse
import os
import sys

from uvmdvgen import gen_agent, gen_env


def main():
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument(
        "name",
        metavar="[ip/block name]",
        help="Name of the ip/block for which the UVM TB is being auto-generated"
    )

    parser.add_argument(
        "-a",
        "--gen_agent",
        action='store_true',
        help="Generate UVM agent code extended from DV library")

    parser.add_argument(
        "-s",
        "--has_separate_host_device_driver",
        action='store_true',
        help=
        """IP / block agent creates a separate driver for host and device modes.
                              (ignored if -a switch is not passed)""")

    parser.add_argument("-e",
                        "--gen_env",
                        action='store_true',
                        help="Generate testbench UVM env code")

    parser.add_argument(
        "-c",
        "--is_cip",
        action='store_true',
        help=
        """Is comportable IP - this will result in code being extended from CIP
                              library. If switch is not passed, then the code will be extended from
                              DV library instead. (ignored if -e switch is not passed)"""
    )

    parser.add_argument(
        "-hi",
        "--has_interrupts",
        default=False,
        action='store_true',
        help="""CIP has interrupts. Create interrupts interface in tb""")

    parser.add_argument(
        "-ha",
        "--has_alerts",
        default=False,
        action='store_true',
        help="""CIP has alerts. Create alerts interface in tb""")

    parser.add_argument(
        "-ea",
        "--env_agents",
        nargs="+",
        metavar="agt1 agt2",
        help="""Env creates an interface agent specified here. They are
                              assumed to already exist. Note that the list is space-separated,
                              and not comma-separated. (ignored if -e switch is not passed)"""
    )

    parser.add_argument(
        "-ao",
        "--agent_outdir",
        default="name",
        metavar="[hw/dv/sv]",
        help="""Path to place the agent code. A directory called <name>_agent is
                              created at this location. (default set to './<name>')"""
    )

    parser.add_argument(
        "-eo",
        "--env_outdir",
        default="name",
        metavar="[hw/ip/<ip>]",
        help=
        """Path to place the full tetsbench code. It creates 3 directories - dv, data and doc.
                The DV plan and the testplan Hjson files are placed in the doc and data directories
                respectively. These are to be merged into the IP's root directory (with the existing
                data and doc directories). Under dv, it creates 3 sub-directories - env,
                tb and tests to place all of the testbench sources. (default set to './<name>')"""
    )

    parser.add_argument(
        "-m",
        "--add-makefile",
        default=False,
        action='store_true',
        help=
        """Tests are now run with dvsim.py tool that requires a hjson based sim cfg.
             Setting this option will also result in the Makefile to be auto-generated (which is
             the older way of building and running sims going through deprecation).""")

    args = parser.parse_args()
    if args.agent_outdir == "name": args.agent_outdir = args.name
    if args.env_outdir == "name": args.env_outdir = args.name

    if args.gen_agent:
        gen_agent.gen_agent(args.name, \
                            args.has_separate_host_device_driver, \
                            args.agent_outdir)

    if args.gen_env:
        if not args.env_agents: args.env_agents = []
        gen_env.gen_env(args.name, \
                        args.is_cip, \
                        args.has_interrupts, \
                        args.has_alerts, \
                        args.env_agents, \
                        args.env_outdir, \
                        args.add_makefile)


if __name__ == '__main__':
    main()
