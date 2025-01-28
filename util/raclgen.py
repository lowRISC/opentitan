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

    parsed_register_mapping, parsed_window_mapping, racl_group, policy_names = parse_racl_mapping(
        parsed_racl_config, args.mapping, args.if_name, ip_block)

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
<% import math %>\
<% policy_idx_len = math.ceil(math.log10(max(1,len(policy_names)+1))) %>\
<% group_suffix = f"_{racl_group.upper()}" if racl_group and racl_group != "Null" else "" %>\
<% if_suffix = f"_{if_name.upper()}" if if_name else "" %>\
<% reg_name_len = max( (len(name) for name in register_mapping.keys()), default=0 ) %>\
<% window_name_len = max( (len(name) for name in window_mapping.keys()), default=0 ) %>\
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
   */
<% policy_sel_name = f"RACL_POLICY_SEL_{module_name.upper()}{group_suffix}{if_suffix}" %>\
<% policy_sel_value = "'{" + ", ".join(map(str, reversed(register_mapping.values()))) + "};" %>\
  parameter int unsigned ${policy_sel_name} [${len(register_mapping)}] = ${policy_sel_value}
      % for window_name, policy_idx in window_mapping.items():
  parameter int unsigned ${policy_sel_name}_WIN_${window_name.upper()} = ${policy_idx};
      % endfor
    """

    print(
        Template(template).render(m=ip_block,
                                  if_name=args.if_name,
                                  register_mapping=parsed_register_mapping,
                                  window_mapping=parsed_window_mapping,
                                  policy_names=policy_names,
                                  module_name=ip_block.name,
                                  racl_group=racl_group).rstrip())


if __name__ == '__main__':
    main()
