#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r""" TileLink-Uncached Lightweight Xbar generator
"""

import argparse
import logging as log
import sys
from pathlib import Path, PurePath

import hjson
import mako
import pkg_resources

import tlgen


def main():
    parser = argparse.ArgumentParser(prog="tlgen")
    parser.add_argument('--topcfg',
                        '-t',
                        metavar='file',
                        type=argparse.FileType('r'),
                        help="`top_cfg.hjson` file.")
    parser.add_argument('--doc',
                        '-d',
                        action='store_true',
                        help='Generate self HTML document in stdout')
    parser.add_argument(
        '--outdir',
        '-o',
        help=
        "Target directory. tlgen needs 'rtl/' and 'dv/' directory under the target dir"
    )
    parser.add_argument('--verbose', '-v', action='store_true', help='Verbose')

    args = parser.parse_args()

    if args.verbose:
        log.basicConfig(format="%(levelname)s: %(message)s", level=log.DEBUG)
    else:
        log.basicConfig(format="%(levelname)s: %(message)s")

    if args.doc:
        # Generate Doc and return
        sys.stdout.write(tlgen.selfdoc(heading=3, cmd='tlgen.py --doc'))
        return

    # Check if topcfg defined
    if not args.topcfg or not args.outdir:
        log.error("--topcfg option is mandatory to generate codes.")

    # Check if outdir exists. If not, show error and exit
    if not Path(args.outdir).is_dir():
        log.error("'--outdir' should point to writable directory")

    # Load contents of top_cfg
    # Skip this part and use internal structure at this time
    try:
        obj = hjson.load(args.topcfg, use_decimal=True)
    except ValueError:
        raise SystemExit(sys.exc_info()[1])

    log.info(obj)

    xbar = tlgen.validate(obj)

    if not tlgen.elaborate(xbar):
        log.error("Elaboration failed." + repr(xbar))

    # Generate
    out_rtl, out_pkg, out_core = tlgen.generate(xbar)

    rtl_path = Path(args.outdir) / 'rtl/autogen'
    rtl_path.mkdir(parents=True, exist_ok=True)
    dv_path = Path(args.outdir) / 'dv/autogen'
    dv_path.mkdir(parents=True, exist_ok=True)

    rtl_filename = "xbar_%s.sv" % (xbar.name)
    rtl_filepath = rtl_path / rtl_filename
    with rtl_filepath.open(mode='w', encoding='UTF-8') as fout:
        fout.write(out_rtl)

    pkg_filename = "tl_%s_pkg.sv" % (xbar.name)
    pkg_filepath = rtl_path / pkg_filename
    with pkg_filepath.open(mode='w', encoding='UTF-8') as fout:
        fout.write(out_pkg)

    core_filename = "xbar_%s.core" % (xbar.name)
    core_filepath = rtl_path / core_filename
    with core_filepath.open(mode='w', encoding='UTF-8') as fout:
        fout.write(out_core)

    # generate TB
    tlgen.generate_tb(xbar, dv_path)


if __name__ == "__main__":
    main()
