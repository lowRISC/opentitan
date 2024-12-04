#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""autogen_tests.py is a script for auto-generating a portion of the
`tests` from Mako templates.
"""

import argparse
import logging
from pathlib import Path

import topgen.lib as topgen_lib
from topgen.topcfg import CompleteTopCfg
from autogen_tests.gen import gen_tests
from reggen.ip_block import IpBlock

# This file is $REPO_TOP/util/autogen_testutils.py, so it takes two parent()
# calls to get back to the top.
REPO_TOP = Path(__file__).resolve().parent.parent


def main():
    # Parse command line args.
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--topcfg_path",
        "-t",
        type=Path,
        required=True,
        help="path of the top hjson file.",
    )
    parser.add_argument(
        "--ipcfg",
        "-i",
        type=Path,
        action="append",
        default=[],
        help="path of an IP hjson file (if not specified, will be guessed by the tool).",
    )
    parser.add_argument(
        "--outdir",
        "-o",
        type=Path,
        required=True,
        help="Output directory"
    )
    args = parser.parse_args()

    logging.getLogger().setLevel(logging.INFO)
    # Parse toplevel Hjson to get IPs that are generated with IPgen.
    topcfg = CompleteTopCfg.from_path(args.topcfg_path)
    ipgen_modules = topgen_lib.get_ipgen_modules(topcfg)
    reggen_top_modules = topgen_lib.get_top_reggen_modules(topcfg)

    # Define autogen DIF directory.
    outdir = args.outdir

    # First load provided IPs.
    ip_hjson = {}
    for ipcfg in args.ipcfg:
        # Assume that the file name is "<ip>.hjson"
        ipname = ipcfg.stem
        ip_hjson[ipname] = ipcfg

    # Create list of IPs to generate shared testutils code for. This is all IPs
    # that have a DIF library, that the testutils functions can use. Note, the
    # templates will take care of only generating ISR testutil functions for IPs
    # that can actually generate interrupts.
    name_to_block = {}
    for ipname in list({m['type'] for m in topcfg['module']}):
        # If the IP's hjson path was not provided on the command line, guess
        # its location based on the type and top name.
        if ipname in ip_hjson:
            hjson_file = ip_hjson[ipname]
        else:
            # Load HJSON data.
            if ipname in ipgen_modules:
                data_dir = REPO_TOP / "hw/top_{}/ip_autogen/{}/data".format(
                    topcfg["name"], ipname)
            elif ipname in reggen_top_modules:
                data_dir = REPO_TOP / "hw/top_{}/ip/{}/data/".format(
                    topcfg["name"], ipname)
            else:
                data_dir = REPO_TOP / "hw/ip/{}/data".format(ipname)
            hjson_file = data_dir / "{}.hjson".format(ipname)
            logging.info("IP hjson path for {} was not provided, ".format(ipname) +
                         "guessing its location to be {}".format(hjson_file.relative_to(REPO_TOP)))

        # NOTE: ip.name_long_* not needed for auto-generated files which
        # are the only files (re-)generated in batch mode.
        name_to_block[ipname] = IpBlock.from_path(hjson_file, [])

    # Auto-generate testutils files.
    gen_tests(outdir, topcfg, name_to_block)


if __name__ == "__main__":
    main()
