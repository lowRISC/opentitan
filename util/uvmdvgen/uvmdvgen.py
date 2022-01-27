#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Command-line tool to generate boilerplate DV testbench.

The generated objects are extended from dv_lib / cip_lib.
"""
import argparse
import logging as log
import re
import sys

import gen_agent
import gen_env

VENDOR_DEFAULT = "lowrisc"


def main():
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument(
        "name",
        metavar="[ip/block name]",
        help="""Name of the ip/block for which the UVM TB is being generated.
                This should just name the block, not the path to it.""")

    parser.add_argument(
        "-a",
        "--gen-agent",
        action='store_true',
        help="Generate UVM agent code extended from DV library")

    parser.add_argument(
        "-s",
        "--has-separate-host-device-driver",
        action='store_true',
        help=
        """IP / block agent creates a separate driver for host and device modes.
        (Ignored if -a switch is not passed.)""")

    parser.add_argument("-e",
                        "--gen-env",
                        action='store_true',
                        help="Generate testbench UVM env code")

    parser.add_argument(
        "-c",
        "--is-cip",
        action='store_true',
        help=
        """Is comportable IP - this will result in code being extended from CIP
        library. If switch is not passed, the code will be extended from DV
        library instead. (Ignored if -e switch is not passed.)""")

    parser.add_argument(
        "-hr",
        "--has-ral",
        default=False,
        action='store_true',
        help="""Specify whether the DUT has CSRs and thus needs a UVM RAL model.
                This option is required if either --is_cip or --has_interrupts
                are enabled.""")

    parser.add_argument(
        "-hi",
        "--has-interrupts",
        default=False,
        action='store_true',
        help="""CIP has interrupts. Create interrupts interface in tb""")

    parser.add_argument(
        "-ha",
        "--has-alerts",
        default=False,
        action='store_true',
        help="""CIP has alerts. Create alerts interface in tb""")

    parser.add_argument(
        "-ne",
        "--num-edn",
        default=0,
        type=int,
        help="""CIP has EDN connection. Create edn pull interface in tb""")

    parser.add_argument(
        "-ea",
        "--env-agents",
        nargs="+",
        metavar="agt1 agt2",
        help="""Env creates an interface agent specified here. They are
                assumed to already exist. Note that the list is space-separated,
                and not comma-separated. (ignored if -e switch is not passed)"""
    )

    parser.add_argument(
        "-ao",
        "--agent-outdir",
        metavar="[hw/dv/sv]",
        help="""Path to place the agent code. A directory called <name>_agent is
                created at this location. (default set to './<name>')""")

    parser.add_argument(
        "-eo",
        "--env-outdir",
        metavar="[hw/ip/<ip>]",
        help="""Path to place the full testbench code. It creates 3 directories
        - dv, data, and doc. The DV doc and the testplan Hjson files are placed
        in the doc and data directories respectively. These are to be merged
        into the IP's root directory (with the existing data and doc
        directories). Under dv, it creates 3 sub-directories - env, tb, and
        tests - to place all of the testbench sources. (default set to
        './<name>'.)""")

    parser.add_argument(
        "-v",
        "--vendor",
        default=VENDOR_DEFAULT,
        help=
        """Name of the vendor / entity developing the testbench. This is used
        to set the VLNV of the FuseSoC core files.""")

    args = parser.parse_args()

    # The name should be alphanumeric.
    if re.search(r"\W", args.name):
        log.error("The block name '%s' contains non-alphanumeric characters.",
                  args.name)
        sys.exit(1)

    if not args.agent_outdir:
        args.agent_outdir = args.name
    if not args.env_outdir:
        args.env_outdir = args.name

    # The has_ral option must be set if either is_cip or has_interrupts is set,
    # as both require use of a RAL model. As such, it is disallowed to not have
    # has_ral set if one of these options is set.
    if not args.has_ral and (args.is_cip or args.has_interrupts):
        args.has_ral = True
        print("NOTE: --has_ral switch is enabled since either "
              "--is_cip or --has_interrupts is set.")

    if args.gen_agent:
        gen_agent.gen_agent(args.name, args.has_separate_host_device_driver,
                            args.agent_outdir, args.vendor)

    if args.gen_env:
        if not args.env_agents:
            args.env_agents = []
        gen_env.gen_env(args.name, args.is_cip, args.has_ral,
                        args.has_interrupts, args.has_alerts, args.num_edn,
                        args.env_agents, args.env_outdir, args.vendor)


if __name__ == '__main__':
    main()
