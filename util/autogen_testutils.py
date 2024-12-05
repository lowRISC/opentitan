#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""autogen_testutils.py is a script for auto-generating a portion of the
`testutils` libraries from Mako templates.

`testutils` libraries are testing libraries that sit a layer above the DIFs
that aid in writing chip-level tests by enabling test developers to re-use
code that calls a specific collection of DIFs.

To render all testutil templates, run the script with:
$ util/autogen_testutils.py
"""

import argparse
import logging
import sys
from pathlib import Path

import hjson

import topgen.lib as topgen_lib
from autogen_testutils.gen import gen_testutils
from make_new_dif.ip import Ip

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
        "--exclude",
        "-e",
        type=str,
        action="append",
        default=[],
        help="ignore IP when generating the testutils",
    ),
    parser.add_argument(
        "--outdir",
        "-o",
        type=Path,
        help="Output directory"
    )
    args = parser.parse_args()

    logging.getLogger().setLevel(logging.INFO)
    # Parse toplevel Hjson to get IPs that are generated with IPgen.
    try:
        topcfg_text = args.topcfg_path.read_text()
    except FileNotFoundError:
        logging.error(f"hjson {args.topcfg_path} could not be found.")
        sys.exit(1)
    topcfg = hjson.loads(topcfg_text, use_decimal=True)
    ipgen_modules = topgen_lib.get_ipgen_modules(topcfg)
    reggen_top_modules = topgen_lib.get_top_reggen_modules(topcfg)

    # Define autogen DIF directory.
    outdir = args.outdir if args.outdir else REPO_TOP / "sw/device/lib/testing/autogen"

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
    ips = []
    for ipname in list({m['type'] for m in topcfg['module']}):
        if ipname in args.exclude:
            continue
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
        ips.append(Ip(ipname, "AUTOGEN", hjson_file))

    # Auto-generate testutils files.
    gen_testutils(outdir, topcfg, ips)


if __name__ == "__main__":
    main()
