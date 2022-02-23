#!/usr/bin/env python3
# Copyright lowRISC contributors.
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
import glob
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

    # Parse toplevel Hjson to get IPs that are templated / generated with IPgen.
    try:
        topcfg_text = args.topcfg_path.read_text()
    except FileNotFoundError:
        logging.error(f"hjson {args.topcfg_path} could not be found.")
        sys.exit(1)
    topcfg = hjson.loads(topcfg_text, use_decimal=True)
    templated_modules = topgen_lib.get_templated_modules(topcfg)
    ipgen_modules = topgen_lib.get_ipgen_modules(topcfg)

    # Define autogen DIF directory.
    autogen_dif_directory = REPO_TOP / "sw/device/lib/dif/autogen"

    # Create list of IPs to generate shared testutils code for. This is all IPs
    # that have a DIF library, that the testutils functions can use. Note, the
    # templates will take care of only generating ISR testutil functions for IPs
    # that can actually generate interrupts.
    ips_with_difs = []
    for autogen_dif_filename in glob.iglob(str(autogen_dif_directory / "*.h")):
        # NOTE: the line below takes as input a file path
        # (/path/to/dif_uart_autogen.c) and returns the IP name in lower
        # case snake mode (i.e., uart).
        ip_name_snake = Path(autogen_dif_filename).stem[4:-8]
        # NOTE: ip.name_long_* not needed for auto-generated files which
        # are the only files (re-)generated in batch mode.
        ips_with_difs.append(
            Ip(ip_name_snake, "AUTOGEN", templated_modules, ipgen_modules))

    # Auto-generate testutils files.
    gen_testutils(ips_with_difs)


if __name__ == "__main__":
    main()
