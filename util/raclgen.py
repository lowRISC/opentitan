#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""RACL Generator.
This utility computes the policy selection vector for a given ip, RACL config, and RACL mapping.
"""

import argparse
import sys
from pathlib import Path
from mako.template import Template
from raclgen.lib import parse_racl_config, parse_racl_mapping, gen_md, gen_md_header, _read_hjson
from reggen.ip_block import IpBlock
import topgen.lib as topgen_lib

# This file is under $REPO_TOP/util/, so parents[1] gets back to the top.
REPO_TOP = Path(__file__).resolve().parents[1]


def main():
    is_doc = "--doc" in sys.argv
    parser = argparse.ArgumentParser(usage='''
%(prog)s --doc DOC
    Generates markdown documentation of the RACL configuration for a given top.

%(prog)s --racl-config RACL_CONFIG --ip IP --mapping MAPPING [--if-name IF_NAME]
    Generates the RACL policy selection vector for the given IP, RACL mapping, and interface name.
              ''')

    parser.add_argument('--doc',
                        '-d',
                        help='Path to top_topname.gen.hjson.')

    parser.add_argument('--racl-config',
                        '-r',
                        required=not is_doc,
                        help='Path to RACL config hjson file.')

    parser.add_argument('--ip',
                        '-i',
                        required=not is_doc,
                        help='Path to IP block hjson file.')

    parser.add_argument('--mapping',
                        '-m',
                        required=not is_doc,
                        help='Path to RACL mapping hjson file.')

    parser.add_argument(
        '--if-name',
        default=None,
        help=
        'TLUL path interface name. Required if multiple bus_interfaces exist.')

    args = parser.parse_args()

    if args.doc:
        top = _read_hjson(args.doc)
        if not topgen_lib.find_module(top["module"], "racl_ctrl"):
            raise SystemExit(f'No racl_ctrl module found in {args.doc}')
        if 'racl' not in top:
            raise SystemExit(f'Missing key "racl" in {args.doc}')

        racl_config = top['racl']
        ips_with_racl = {}

        gen_md_header(racl_config)

        for module in top['module']:
            if 'racl_mappings' not in module:
                continue
            ip_name = module['type']
            if ip_name not in ips_with_racl:
                try:
                    ip_path = topgen_lib.get_ip_hjson_path(ip_name, top, REPO_TOP)
                    ips_with_racl[ip_name] = IpBlock.from_path(path=ip_path, param_defaults=[])
                except ValueError as err:
                    raise SystemExit(f'Failed to parse IP block "{ip_name}". Error: {err}')

            for if_name, racl_mappings in module['racl_mappings'].items():
                if 'racl_group' not in racl_mappings:
                    raise SystemExit(f'racl_mappings of {module["name"]} is missing "racl_group".')
                racl_mapping = {
                    'if_name': if_name,
                    'racl_group': racl_mappings['racl_group'],
                    'register_mapping': racl_mappings.get('register_mapping', {}),
                    'window_mapping': racl_mappings.get('window_mapping', {}),
                    'range_mapping': racl_mappings.get('range_mapping', []),
                }
                gen_md(block=ips_with_racl[ip_name],
                       racl_config=racl_config,
                       racl_mapping=racl_mapping,
                       module=module)

        sys.exit(0)

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
        ip_block=ip_block,
        if_name=args.if_name
    ).rstrip())


if __name__ == '__main__':
    main()
