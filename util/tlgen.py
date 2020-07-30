#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r""" TileLink-Uncached Lightweight Xbar generator
"""

import argparse
import logging as log
import sys
from pathlib import Path

import hjson

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
    parser.add_argument('--ip-path',
                        default="",
                        help='''
        Additional path to generated rtl/ or dv/ folders: outdir/ip_path/rtl
        Only needed when there are multiple xbar in outdir''')
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
    xbar.ip_path = args.ip_path

    if not tlgen.elaborate(xbar):
        log.error("Elaboration failed." + repr(xbar))

    # Generate
    results = tlgen.generate(xbar)

    dv_path = Path(args.outdir) / args.ip_path / 'dv/autogen'
    dv_path.mkdir(parents=True, exist_ok=True)

    for filename, filecontent in results:
        filepath = Path(args.outdir) / args.ip_path / filename
        filepath.parent.mkdir(parents=True, exist_ok=True)
        with filepath.open(mode='w', encoding='UTF-8') as fout:
            fout.write(filecontent)

    # generate TB
    tlgen.generate_tb(xbar, dv_path)


if __name__ == "__main__":
    main()
