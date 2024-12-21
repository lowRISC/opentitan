# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import hjson
import logging
import sys
from typing import Dict
from typing import Optional
from reggen.ip_block import IpBlock
from reggen.validate import check_keys

# Required fields for the RACL hjson
racl_required = {
    'error_response': [
        'pb',
        'When true, return TLUL error on denied RACL access, otherwise not'
    ],
    'roles': ['l', 'List, specifying all RACL roles'],
    'policies': ['g', 'Dict, specifying the policies of all RACL groups']
}

# Default configuration to render the RACL package for systems that don't use RACL but need the
# type definitions
DEFAULT_RACL_CONFIG = {
    'nr_policies': 1,
    'policies': {},
}


def _read_hjson(filename: str) -> Dict[str, object]:
    try:
        with open(filename, 'r') as f_racl_config:
            return hjson.load(f_racl_config)
    except ValueError:
        logging.error(f'Error parsing HJSON config file {filename}')
        raise SystemExit(sys.exc_info()[1])
    except OSError:
        raise SystemExit(sys.exc_info()[1])


def parse_racl_config(config_path: str) -> Dict[str, object]:
    racl_config = _read_hjson(config_path)

    # TODO(#25690) Further sanity checks on the parsed RACL config
    error = check_keys(racl_config, racl_required, [], [], 'RACL Config')
    if error:
        raise SystemExit(f"Error occurred while validating {config_path}")

    # Determine the maximum number of policies over all RACL groups for RTL
    # RTL needs to create the vectors based on the largest group
    racl_config['nr_policies'] = max(
        len(policies) for policies in racl_config['policies'].values())

    for racl_group, policies in racl_config['policies'].items():
        for policy in policies:

            def compute_policy_value(permission: str) -> int:
                permission_value = 0
                for role in policy[permission]:
                    role_id = racl_config['roles'][role]['role_id']
                    permission_value += 2**role_id
                return permission_value

            policy['rd_default'] = compute_policy_value('allowed_rd')
            policy['wr_default'] = compute_policy_value('allowed_wr')
    return racl_config


def parse_racl_mapping(racl_config: Dict[str, object], mapping_path: str,
                       if_name: Optional[str],
                       ip_block: IpBlock) -> Dict[str, int]:
    mapping = _read_hjson(mapping_path)
    parsed_register_mapping = {}

    # Mapping must be a dict with a single entry:
    # RACL_GROUP => register mapping
    if len(mapping) != 1:
        raise SystemExit('Mapping file must be a single-element dict mapping '
                         'the RACL group to the register mapping')
    racl_group, register_mapping = list(mapping.items())[0]

    if not isinstance(racl_group, str):
        raise SystemExit('RACL group must be a string')
    if not isinstance(register_mapping, dict):
        raise SystemExit('Register mapping must be a a dict')

    # Special handling of the all star assignment:
    # "*": POLICY
    # Assigns all registers to a given policy
    if list(register_mapping.keys()) == ["*"]:
        policy_name = register_mapping["*"]

        if racl_group not in racl_config['policies']:
            raise SystemExit(
                f'RACL group {racl_group} not defined in RACL config')

        policy_idx = -1
        for idx, policy in enumerate(racl_config['policies'][racl_group]):
            if policy['name'] == policy_name:
                policy_idx = idx
                break

        if policy_idx == -1:
            raise SystemExit(
                f'RACL policy {policy_name} not defined in RACL config '
                f'for group {racl_group}')

        reg_block = ip_block.reg_blocks.get(if_name)
        if not reg_block:
            raise SystemExit(
                f"Register interface {if_name} not defined in in {ip_block['name']}"
            )

        for reg in reg_block.flat_regs:
            parsed_register_mapping[reg.name] = policy_idx
    else:
        # General case not yet implemented
        assert False

    return parsed_register_mapping
