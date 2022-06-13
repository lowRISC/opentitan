#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Generates chip_info.h for ROM build
"""

import argparse
import logging as log
import sys
from datetime import datetime
from pathlib import Path

header_template = r"""
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// --------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! ---------//

#ifndef _F_CHIPINFO_H__
#define _F_CHIPINFO_H__

static const char chip_info[128] __attribute__((section(".chip_info"))) =
  "Version: {%version%}, Build Date: {%build_date%}";

#endif  // _F_CHIPINFO_H__

"""


def main():
    parser = argparse.ArgumentParser(prog="rom_chip_info")
    parser.add_argument('--outdir',
                        '-o',
                        required=True,
                        help='Output Directory')
    parser.add_argument('--ot_version',
                        required=False,
                        help='OpenTitan Version')
    parser.add_argument('--ot_version_file',
                        required=False,
                        help='Path to a file with the OpenTitan Version')

    log.basicConfig(format="%(levelname)s: %(message)s")
    args = parser.parse_args()

    if not args.outdir:
        log.error("Missing --outdir.")
        raise SystemExit(sys.exc_info()[1])

    if args.ot_version:
        version = args.ot_version
    elif args.ot_version_file:
        version = open(args.ot_version_file, "rt").read().strip()
    else:
        log.error(
            "Missing ot_version, provide --ot_version or --ot_version_file.")
        raise SystemExit(sys.exc_info()[1])

    outdir = Path(args.outdir)

    outdir.mkdir(parents=True, exist_ok=True)
    out_path = outdir / "chip_info.h"

    now = datetime.now()
    wall_time = now.strftime("%Y-%m-%d %H:%M:%S")

    log.info("Version: %s" % (version, ))
    log.info("Build Date: %s" % (wall_time, ))

    output = header_template
    output = output.replace('{%version%}', version, 1)
    output = output.replace('{%build_date%}', wall_time, 1)

    with out_path.open(mode='w', encoding='UTF-8') as fout:
        fout.write(output + "\n")


if __name__ == "__main__":
    main()
