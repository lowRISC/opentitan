#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Generates chip_info.h for ROM build
"""

import argparse
import logging as log
import os
import sys
from datetime import datetime
from git import Repo
from io import StringIO
from pathlib import Path


# Common header for generated files
gentpl = r"""
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// --------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! ---------//

#ifndef _F_CHIPINFO_H__
#define _F_CHIPINFO_H__

static const char chip_info[128] __attribute__((section(".chip_info"))) =
  "Commit ID:  {%commit_hash%}\r\n"
  "Build Date: {%build_date%}\r\n";

#endif

"""
def main():
    parser = argparse.ArgumentParser(prog="rom_chip_info")
    parser.add_argument('--outdir',
                        '-o',
                        required=True,
                        help='Output Directory'
                        )

    log.basicConfig(format="%(levelname)s: %(message)s")
    args = parser.parse_args()

    if not args.outdir:
        log.error("'--outdir' not specified")
        raise SystemExit(sys.exc_info()[1])
    else:
        outdir = Path(args.outdir)

    outdir.mkdir(parents=True, exist_ok=True)
    out_path = outdir / "chip_info.h"


    repo = Repo(search_parent_directories=True)
    repo_info = repo.head.object.hexsha

    now = datetime.now()
    wall_time = now.strftime("%Y-%m-%d, %H:%M:%S")

    log.info("Info %s" % repo_info)
    log.info("Time %s" % wall_time)

    output = gentpl.replace('{%commit_hash%}', repo_info, 1)
    output = output.replace('{%build_date%}', wall_time, 1)

    with out_path.open(mode='w', encoding='UTF-8') as fout:
        fout.write(output + "\n")


if __name__ == "__main__":
    main()
