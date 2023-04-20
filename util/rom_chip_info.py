#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Generates chip_info.h for ROM build
"""

import argparse
import hashlib
import logging as log
import sys
from pathlib import Path


def generate_chip_info_c_source(scm_revision: int) -> str:
    """Return the contents of a C source file that defines `kChipInfo`.

    Args:
        scm_revision: SHA1 sum identifying the current SCM revision.
    """

    SHA1_DIGEST_SIZE_BITS = hashlib.sha1().digest_size * 8
    assert scm_revision.bit_length() <= SHA1_DIGEST_SIZE_BITS

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
    version = int(version, base=16)
    log.info("Version: %x" % (version, ))

    outdir = Path(args.outdir)

    outdir.mkdir(parents=True, exist_ok=True)
    source_out_path = outdir / "chip_info.c"

    output = generate_chip_info_c_source(version)

    with source_out_path.open(mode='w', encoding='UTF-8') as fout:
        fout.write(output)


if __name__ == "__main__":
    main()
