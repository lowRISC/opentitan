# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging
import sys
from collections import OrderedDict
from typing import Dict, Optional, Tuple, List

import hjson
from reggen.ip_block import IpBlock
from reggen.validate import check_keys

# Required fields for the RACL hjson
racl_required = {
    'error_response': [
        'pb',
        'When true, return TLUL error on denied RACL access, otherwise not'
    ],
    'role_bit_lsb': ['d', 'RACL role bit LSB within the TLUL user bit vector'],
    'role_bit_msb': ['d', 'RACL role bit MSB within the TLUL user bit vector'],
    'ctn_uid_bit_lsb': ['d', 'CTN UID bit LSB within the TLUL user bit vector'],
    'ctn_uid_bit_msb': ['d', 'CTN UID bit MSB within the TLUL user bit vector'],
    'roles': ['l', 'List, specifying all RACL roles'],
    'policies': ['g', 'Dict, specifying the policies of all RACL groups']
}

# Default configuration to render the RACL package for systems that don't use RACL but need the
# type definitions
DEFAULT_RACL_CONFIG = {
    'role_bit_lsb': 0,
    'role_bit_msb': 0,
    'ctn_uid_bit_lsb': 0,
    'ctn_uid_bit_msb': 0,
    'nr_role_bits': 1,
    'nr_ctn_uid_bits': 1,
    'nr_policies': 1,
    'policies': {},
    'rot_private_policy_rd': 0,
    'rot_private_policy_wr': 0
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

    if racl_config['role_bit_lsb'] > racl_config['role_bit_msb']:
        raise ValueError('Invalid RACL role bit configuration LSB > MSB')
    if racl_config['ctn_uid_bit_lsb'] > racl_config['ctn_uid_bit_msb']:
        raise ValueError('Invalid RACL CTN UID bit configuration LSB > MSB')

    racl_config['nr_role_bits'] = racl_config['role_bit_msb'] - racl_config['role_bit_lsb'] + 1
    racl_config['nr_ctn_uid_bits'] = racl_config['ctn_uid_bit_msb'] - \
        racl_config['ctn_uid_bit_lsb'] + 1

    # Determine the maximum number of policies over all RACL groups for RTL
    # RTL needs to create the vectors based on the largest group
    racl_config['nr_policies'] = max(
        len(policies) for policies in racl_config['policies'].values())

    # Checking for racl misconfiguration which could lead to code misgeneration, e.g., logic [-1:0]
    #
    # There must be space for at least 1 role and 1 policy
    assert racl_config['nr_role_bits'] > 0
    assert racl_config['nr_policies'] > 0
    # Role selector must fit into nr_role_bits
    assert len(racl_config['roles']) <= 2 ** racl_config['nr_role_bits']
    # MSB >= LSB
    assert racl_config['ctn_uid_bit_msb'] >= racl_config['ctn_uid_bit_lsb']
    assert racl_config['role_bit_msb'] >= racl_config['role_bit_lsb']
    # No overlap between role and ctn_uid
    assert racl_config['role_bit_lsb'] > racl_config['ctn_uid_bit_msb'] or \
           racl_config['ctn_uid_bit_lsb'] > racl_config['role_bit_msb']

    rot_private_policy = None
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
            if policy.get('rot_private'):
                if rot_private_policy:
                    raise ValueError(
                        'Only one policy can be the ROT_PRIVATE policy')
                rot_private_policy = policy

    if not rot_private_policy:
        raise ValueError('No ROT_PRIVATE policy defined')

    # Get the default ROT private policy for static RACL protection of the racl_ctrl IP(s)
    racl_config['rot_private_policy_rd'] = rot_private_policy['rd_default']
    racl_config['rot_private_policy_wr'] = rot_private_policy['wr_default']

    return racl_config


def parse_racl_mapping(
        racl_config: Dict[str,
                          object], mapping_path: str, if_name: Optional[str],
        ip_block: IpBlock) -> Tuple[Dict[str, int], Dict[str, int], str, List[str]]:

    mapping = _read_hjson(mapping_path)
    parsed_register_mapping = OrderedDict()
    parsed_window_mapping = OrderedDict()

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

    racl_policy = racl_config['policies'].get(racl_group)
    if racl_policy is None:
        raise SystemExit(f'RACL group {racl_group} not defined in RACL config')

    policy_names = [policy['name'] for policy in racl_policy]

    # Special handling of the all star assignment:
    # "*": POLICY
    # Assigns all registers to a given policy
    if list(register_mapping.keys()) == ["*"]:
        policy_name = register_mapping["*"]
        try:
            policy_idx = policy_names.index(policy_name)
        except ValueError:
            raise SystemExit(
                f'RACL policy {policy_name} not defined in RACL config '
                f'for group {racl_group}')

        reg_block = ip_block.reg_blocks.get(if_name)
        if not reg_block:
            raise SystemExit(
                f"Register interface {if_name} not defined in {ip_block.name}")

        for reg in reg_block.flat_regs:
            parsed_register_mapping[reg.name] = policy_idx

        for window in reg_block.windows:
            parsed_window_mapping[window.name] = policy_idx

    else:
        # General case not yet implemented
        assert False

    return parsed_register_mapping, parsed_window_mapping, racl_group, policy_names
