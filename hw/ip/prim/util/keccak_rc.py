#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Calculate Round Constant
"""

import argparse
import bitarray as ba
import logging as log


def main():
    parser = argparse.ArgumentParser(
        prog="keccak round constant generator",
        description=
        '''This tool generates the round constants based on the given max round number'''
    )
    parser.add_argument(
        '-r',
        type=int,
        default=24,
        help='''Max Round value. Default is SHA3 Keccak round %(default)''')
    parser.add_argument('--verbose', '-v', action='store_true', help='Verbose')

    args = parser.parse_args()

    if (args.verbose):
        log.basicConfig(format="%(levelname)s: %(message)s", level=log.DEBUG)
    else:
        log.basicConfig(format="%(levelname)s: %(message)s")

    if args.r < 1:
        log.error("Max Round value should be greater than 0")

    # Create 0..255 bit array
    rc = ba.bitarray(256)
    rc.setall(0)

    r = ba.bitarray('10000000')
    rc[0] = True  # t%255 == 0 -> 1
    for i in range(1, 256):
        # Update from t=1 to t=255
        r_d = ba.bitarray('0') + r
        if r_d[8]:
            #Flip 0,4,5,6
            r = r_d[0:8] ^ ba.bitarray('10001110')
        else:
            r = r_d[0:8]

        rc[i] = r[0]

    ## Print rc
    print(rc)

    ## Round

    rcs = []  # Each entry represent the round
    for rnd in range(0, args.r):
        # Let RC=0
        rndconst = ba.bitarray(64)
        rndconst.setall(0)
        # for j [0 .. L] RC[2**j-1] = rc(j+7*rnd)
        for j in range(0, 7):  #0 to 6
            rndconst[2**j - 1] = rc[(j + 7 * rnd) % 255]
        print("64'h{}, // Round {}".format(rndhex(rndconst), rnd))


def rndhex(bit) -> str:
    return bit[::-1].tobytes().hex()


if __name__ == "__main__":
    main()
