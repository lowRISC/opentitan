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
        default=(REPO_TOP / "hw/top_earlgrey/data/top_earlgrey.hjson"),
        help="path of the top hjson file.",
    )
    args = parser.parse_args()

    # Parse toplevel Hjson to get IPs that are generated with IPgen.
    try:
        topcfg_text = args.topcfg_path.read_text()
    except FileNotFoundError:
        logging.error(f"hjson {args.topcfg_path} could not be found.")
        sys.exit(1)
    topcfg = hjson.loads(topcfg_text, use_decimal=True)

    # Define autogen DIF directory.
    autogen_dif_directory = REPO_TOP / "sw/device/lib/dif"

    # Create list of IPs to generate shared testutils code for. This is all IPs
    # that have a DIF library, that the testutils functions can use. Note, the
    # templates will take care of only generating ISR testutil functions for IPs
    # that can actually generate interrupts.
    ips_with_difs = []

    for ip_name_snake in sorted({m["type"] for m in topcfg["module"]}):
        if not (autogen_dif_directory / f"dif_{ip_name_snake}.h").exists():
            continue

        hjson_file = topgen_lib.get_ip_hjson_path(ip_name_snake, topcfg, REPO_TOP)

        # NOTE: ip.name_long_* not needed for auto-generated files which
        # are the only files (re-)generated in batch mode.
        ips_with_difs.append(
            Ip(ip_name_snake, "AUTOGEN", hjson_file))

    # Auto-generate testutils files.
    gen_testutils(ips_with_difs)


if __name__ == "__main__":
    main()
