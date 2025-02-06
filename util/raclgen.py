#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""RACL Generator.
This utility computes the policy selection vector for a given ip, RACL config, and RACL mapping.
"""

import argparse

from mako.template import Template
from raclgen.lib import parse_racl_config, parse_racl_mapping
from reggen.ip_block import IpBlock


def main():
    parser = argparse.ArgumentParser()

    parser.add_argument('--racl-config',
                        '-r',
                        required=True,
                        help='Path to RACL config hjson file.')

    parser.add_argument('--ip',
                        '-i',
                        required=True,
                        help='Path to IP block hjson file.')

    parser.add_argument('--mapping',
                        '-m',
                        required=True,
                        help='Path to RACL mapping hjson file.')

    parser.add_argument(
        '--if-name',
        default=None,
        help=
        'TLUL path interface name. Required if multiple bus_interfaces exist.')

    args = parser.parse_args()

    try:
        ip_block = IpBlock.from_path(path=args.ip, param_defaults=[])
    except ValueError as err:
        raise SystemExit(f'Failed to parse IP block "{args.ip}". Error: {err}')

    try:
        parsed_racl_config = parse_racl_config(args.racl_config)
    except ValueError as err:
        raise SystemExit(
            f'Failed to parse RACL config "{args.racl_config}". Error: {err}')

    register_mapping, window_mapping, range_mapping, racl_group, policy_names\
        = parse_racl_mapping(parsed_racl_config, args.mapping, args.if_name, ip_block)

    print(Template(filename='util/topgen/templates/toplevel_racl_pkg_parameters.tpl').render(
        register_mapping=register_mapping,
        window_mapping=window_mapping,
        range_mapping=range_mapping,
        policy_names=policy_names,
        racl_group=racl_group,
        module_name=ip_block.name,
        if_name=args.if_name
    ).rstrip())


if __name__ == '__main__':
    main()
