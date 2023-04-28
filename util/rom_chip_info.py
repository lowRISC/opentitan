#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Generates chip_info.c for ROM build."""

import argparse
import hashlib
import logging as log
from pathlib import Path


def generate_chip_info_c_source(scm_revision: int) -> str:
    """Return the contents of a C source file that defines `kChipInfo`.

    Args:
        scm_revision: SHA1 sum identifying the current SCM revision.
    """

    SHA1_DIGEST_SIZE_BITS = hashlib.sha1().digest_size * 8
    assert scm_revision.bit_length() <= SHA1_DIGEST_SIZE_BITS
    assert scm_revision >= 0

    # Truncate the SCM revision to the top N bits.
    SCM_REVISION_SIZE_BITS = 64
    shift_amount = SHA1_DIGEST_SIZE_BITS - SCM_REVISION_SIZE_BITS
    scm_revision >>= shift_amount

    return f"""
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// --------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! ---------//

#include "sw/device/silicon_creator/lib/chip_info.h"

const chip_info_t kChipInfo __attribute__((section(".chip_info"))) = {{
    .scm_revision = (uint64_t){scm_revision:#0x},
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
