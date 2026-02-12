# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Script for generating OpenTitan device IDs for embedding in CP/FT FW."""

import argparse
import sys
from pathlib import Path

import hjson
from mako.template import Template

import util
from device_id import DeviceId, DeviceIdentificationNumber
from sku_config import SkuConfig

_RESERVED_VALUE = 0
_MAX_UINT32 = 2**32 - 1


def main(args_in):
    # Parse cmd line args.
    parser = argparse.ArgumentParser(
        prog=__doc__,
        description="""This tool generates device ID header files.""",
    )
    parser.add_argument(
        "--mode",
        type=str,
        choices=["cp", "ft"],
        help="The device ID header to generate: CP or FT.",
    )
    parser.add_argument(
        "--sku-config",
        required=True,
        type=str,
        help="SKU HJSON configuration file.",
    )
    parser.add_argument(
        "--output",
        required=str,
        type=str,
        help="The output source file path.",
    )
    parser.add_argument(
        "--template",
        required=True,
        type=str,
        help="The template source file to be overwritten.",
    )
    args = parser.parse_args(args_in)

    # Load and validate a SKU configuration file.
    sku_config_args = {}
    with open(args.sku_config, "r") as fp:
        sku_config_args = hjson.load(fp)
    sku_config = SkuConfig(**sku_config_args)

    # Generate CP/FT portion of device ID.
    din = DeviceIdentificationNumber.blind_asm()
    if args.mode == "cp":
        device_id_int = DeviceId(sku_config, din).to_int()
    else:
        device_id_int = DeviceId(sku_config, din).to_int() >> 128
    devid_list = []
    for _ in range(4):
        devid_list.append(util.format_hex(device_id_int & _MAX_UINT32, 8))
        device_id_int >>= 32
    devid_str = ','.join(devid_list)

    # Fill template.
    template = Template(Path(args.template).read_text())
    Path(args.output).write_text(template.render(device_id=devid_str))
    print("Computed {} device ID array: {}".format(args.mode.upper(),
                                                   devid_str))


if __name__ == "__main__":
    main(sys.argv[1:])
