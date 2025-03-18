# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Script for generating OpenTitan FT device IDs for embedding in FT FW."""

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
        description="""This tool ...""",
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
    parser.add_argument(
        "--ast-cfg-version",
        required=True,
        type=int,
        help="AST configuration version to be written to OTP.",
    )
    args = parser.parse_args(args_in)

    # Load and validate a SKU configuration file.
    sku_config_args = {}
    with open(args.sku_config, "r") as fp:
        sku_config_args = hjson.load(fp)
    sku_config = SkuConfig(ast_cfg_version=args.ast_cfg_version,
                           **sku_config_args)

    # Generate FT (SKU specific) portion of device ID.
    din = DeviceIdentificationNumber.blind_asm()
    device_id_int = DeviceId(sku_config, din).to_int() >> 128
    ft_devid_list = []
    for _ in range(4):
        ft_devid_list.append(util.format_hex(device_id_int & _MAX_UINT32, 8))
        device_id_int >>= 32
    ft_devid_str = ','.join(ft_devid_list)

    # Fill template.
    template = Template(Path(args.template).read_text())
    Path(args.output).write_text(template.render(ft_device_id=ft_devid_str))
    print("Computer FT device ID array:", ft_devid_str)


if __name__ == "__main__":
    main(sys.argv[1:])
