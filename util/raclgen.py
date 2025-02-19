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

# This file is $REPO_TOP/util/, so it takes two parent() calls to get back to the top.
REPO_TOP = Path(__file__).resolve().parent.parent


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
        if 'racl_ctrl' not in (module['name'] for module in top['module']):
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

    template = """\
<%doc>
  Note: The RACL parameters must be generated identically across multiple files.
        Thus, this template needs to be manually synced between the following files:
        util/raclgen.py
        util/topgen/templates/toplevel_racl_pkg.sv.tpl
        hw/top_darjeeling/templates/toplevel.sv.tpl
        hw/top_earlgrey/templates/toplevel.sv.tpl
        hw/top_englishbreakfast/templates/toplevel.sv.tpl
</%doc>\
<% import raclgen.lib as raclgen %>\
<% import math %>\
<% policy_idx_len = math.ceil(math.log10(max(1,len(policy_names)+1))) %>\
<% group_suffix = f"_{racl_group.upper()}" if racl_group and racl_group != "Null" else "" %>\
<% if_suffix = f"_{if_name.upper()}" if if_name else "" %>\
<% reg_name_len = max( (len(name) for name in register_mapping.keys()), default=0 ) %>\
<% window_name_len = max( (len(name) for name in window_mapping.keys()), default=0 ) %>\
<% policy_sel_name = f"RACL_POLICY_SEL_{module_name.upper()}{group_suffix}{if_suffix}" %>\
  /**
   * Policy selection vector for ${module_name}
   *   TLUL interface name: ${if_name}
   *   RACL group: ${racl_group}
      % if len(register_mapping) > 0:
   *   Register to policy mapping:
        % for reg_name, policy_idx in register_mapping.items():
   *     ${f"{reg_name}:".ljust(reg_name_len+1)} ${policy_names[policy_idx]} \
(Idx ${f"{policy_idx}".rjust(policy_idx_len)})
        % endfor
      % endif
      % if len(window_mapping) > 0:
   *   Window to policy mapping:
        % for window_name, policy_idx in window_mapping.items():
   *     ${f"{window_name}:".ljust(window_name_len+1)} ${policy_names[policy_idx]} \
(Idx ${f"{policy_idx}".rjust(policy_idx_len)})
        % endfor
      % endif
      % if len(range_mapping) > 0:
   *   Range to policy mapping:
        % for range in range_mapping:
   *     ${f"0x{range['base']:08x}"} -- ${f"0x{(range['base']+range['size']):08x}"} \
policy: ${policy_names[range['policy']]} (Idx ${f"{range['policy']}".rjust(policy_idx_len)})
        % endfor
      % endif
   */
      % if len(register_mapping) > 0:
<% policy_sel_value = "'{" + ", ".join(map(str, reversed(register_mapping.values()))) + "};" %>\
  parameter racl_policy_sel_t ${policy_sel_name} [${len(register_mapping)}] = ${policy_sel_value}
      % endif
      % for window_name, policy_idx in window_mapping.items():
  parameter racl_policy_sel_t ${policy_sel_name}_WIN_${window_name.upper()} = ${policy_idx};
      % endfor
      % if len(range_mapping) > 0:
  parameter racl_policy_sel_t ${policy_sel_name}_NUM_RANGES = ${len(range_mapping)};
<% value =  ",\\n".join(map(raclgen.format_parameter_range_value, range_mapping)) %>\
  parameter racl_range_t ${policy_sel_name}_RANGES [${len(range_mapping)}] = '{
    ${value}
  };
      % endif

    """

    print(
        Template(template).render(m=ip_block,
                                  if_name=args.if_name,
                                  register_mapping=register_mapping,
                                  window_mapping=window_mapping,
                                  range_mapping=range_mapping,
                                  policy_names=policy_names,
                                  module_name=ip_block.name,
                                  racl_group=racl_group).rstrip())


if __name__ == '__main__':
    main()
