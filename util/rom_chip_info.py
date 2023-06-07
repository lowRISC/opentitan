#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Generates chip_info.c for ROM build."""

import argparse
import logging as log
from pathlib import Path


def generate_chip_info_c_source(scm_revision: int) -> str:
    """Return the contents of a C source file that defines `kChipInfo`.

    Args:
        scm_revision: SHA1 sum identifying the current SCM revision.
    """
    SHA1_BYTE_CNT = 20
    assert 0 < scm_revision < 2**(SHA1_BYTE_CNT * 8)
    scm_rev_byte_be = scm_revision.to_bytes(SHA1_BYTE_CNT, "big")
    scm_revision_high = int.from_bytes(scm_rev_byte_be[0:4], "big")
    scm_revision_low = int.from_bytes(scm_rev_byte_be[4:8], "big")

    return f"""
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// --------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! ---------//

#include "sw/device/silicon_creator/lib/chip_info.h"

#include "sw/device/lib/base/macros.h"

OT_SECTION(".chip_info")
const chip_info_t kChipInfo = {{
  .scm_revision = (chip_info_scm_revision_t){{
    .scm_revision_low = {scm_revision_low:#010x},
    .scm_revision_high = {scm_revision_high:#010x},
  }},
  .version = (uint32_t)kChipInfoVersion1,
}};
"""


def read_version_file(path: Path) -> int:
    """Interprets the contents of `path` as a big-endian hex literal."""

    with open(path, "rt") as f:
        version = f.read().strip()
    return int(version, base=16)


def write_source_file(outdir: Path, contents: str) -> Path:
    """Creates chip_info.c in `outdir`. Returns the path to the new file."""

    source_out_path = outdir / "chip_info.c"

    outdir.mkdir(parents=True, exist_ok=True)
    with source_out_path.open(mode='w', encoding='utf-8') as fout:
        fout.write(contents)

    return source_out_path


def main():
    log.basicConfig(format="%(levelname)s: %(message)s")

    parser = argparse.ArgumentParser(prog="rom_chip_info")
    parser.add_argument('--outdir',
                        '-o',
                        required=True,
                        type=Path,
                        help='Output Directory')
    parser.add_argument('--ot_version_file',
                        required=True,
                        type=Path,
                        help='Path to a file with the OpenTitan Version')

    args = parser.parse_args()

    version = read_version_file(args.ot_version_file)
    log.info("Version: %x" % (version, ))

    generated_source = generate_chip_info_c_source(version)
    out_path = write_source_file(args.outdir, generated_source)
    log.info("Generated new source file: %s" % (out_path))


if __name__ == "__main__":
    main()
