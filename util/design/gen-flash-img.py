#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Takes a compiled vmem image and processes it for flash.
    Long term this should include both layers of ECC and scrambling,
    The first version has only the truncated plaintext ECC.
"""

import argparse
import math
import re
from pathlib import Path

import secded_gen


def _add_plain_ecc(in_val: int) -> str:
    result, m = secded_gen.ecc_encode("hamming", 64, in_val)

    m_nibbles = math.ceil(m / 4)
    result = format(result, '0' + str(16 + m_nibbles) + 'x')

    # due to lack of storage space, the first nibble of the ECC is truncated
    return result[1:]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('infile')
    parser.add_argument('outfile')
    args = parser.parse_args()

    # open original vmem and extract relevant content
    try:
        vmem_orig = Path(args.infile).read_text()
    except IOError:
        raise Exception(f"Unable to open {args.infile}")

    # search only for lines that contain data, skip all other comments
    result = re.findall(r"^@.*$", vmem_orig, flags=re.MULTILINE)

    output = []
    for line in result:
        items = line.split()
        result = ""
        for item in items:
            if re.match(r"^@", item):
                result += item
            else:
                result += f' {_add_plain_ecc(int(item, 16))}'

        # add processed element to output
        output.append(result)

    # open output file
    outfile = open(args.outfile, "w")

    # write processed content
    for entry in output:
        outfile.write(entry + "\n")


if __name__ == "__main__":
    main()
