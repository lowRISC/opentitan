#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Generating a System View Description file:

  This utility generates a CMSIS-SVD[1] file from the top configuration and
  IP module HJSON files. The resulting SVD describes the chip's peripherals
  and register layouts. This enables other tools such as `svd2rust`[2] to
  generate software interfaces to the hardware.

  When invoked from the command line this requires arguments pointing to
  all HJSON files and other configuration options. See `./svdgen.py --help`
  for the full options. The `hw/Makefile` script has an example command
  line to generate `top_earlgrey.svd`.

  [1] http://www.keil.com/pack/doc/CMSIS/SVD/html/index.html
  [2] https://docs.rs/svd2rust/

Semantics of the conversion:

  For the most part the HJSON files used by OpenTitan map directly to SVD
  semantics. However, there are a few places where some interpretation is
  required:

  * SVD files must contain a top-level <cpu> element which describe the
    high-level features of the chip. Some of these reflect SVD's origin
    to describe ARM SOCs, and the values aren't necessary to accurately
    described a RISC-V chip. To maintain compatibility with the SVD
    specification these fields are included.

    The fixed values are created in `generate_cpu()`.

  * OpenTitan uses a single `swaccess` field to define what operations
    software may use on a register. SVD uses a combination of three
    separate elements to do the same: <access>, <readAction>, and
    <modifiedWriteValues>.

    This mapping is performed within `sw_access_modes()`.

  * Most OpenTitan register definitions are assumed to be fixed width
    (32 bits). Smaller register width are specified by listing a single
    "field" element which specifies the reduced bit width. SVD instead
    allows each register to specify the reduced width by directly setting
    the <size> of a <register>.

    The heuristic used to detect and flatten these fields is documented
    in `generate_register()`.

  * Both OpenTitan and SVD allowing grouping registers with related
    funcationality. An OpenTitan "multireg" specifies all offsets
    relative to the peripheral base address, while SVD instead gives a
    <cluster> an <addressOffset>, and each <register> is relative to the
    <cluster>.

    This is computed in `generate_cluster()` and specified via the `base`
    argument to `generate_register()`.
"""

import argparse
from pathlib import Path
from svdgen import convert_top_to_svd, write_svd
from topgen import load_completecfg_and_ips


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--topcfg',
                        required=True,
                        help='`top_{name}.hjson` file.')
    parser.add_argument('--ip_dir',
                        required=True,
                        help='IP module directory')
    parser.add_argument('--version',
                        required=True,
                        help='the version to embed in the SVD')
    parser.add_argument('--readme',
                        required=True,
                        help='the README file to embed in the Svd')
    parser.add_argument('--output',
                        required=True,
                        help='the destination SVD filename')
    args = parser.parse_args()

    description = Path(args.readme).read_text()
    topcfg = Path(args.topcfg)
    ip_dir = Path(args.ip_dir)

    completecfg, ip_objs = load_completecfg_and_ips(topcfg, ip_dir)
    ips = {ip['name'].lower(): ip for ip in ip_objs}
    svd = convert_top_to_svd(completecfg, ips, args.version, description)

    with open(args.output, 'w') as output:
        write_svd(svd, output)


if __name__ == '__main__':
    main()
