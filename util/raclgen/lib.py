# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import hjson
import sys
from reggen.validate import check_keys
from typing import Dict

# Required fields for the RACL hjson
racl_required = {
    'roles': ['l', 'List, specifying all RACL roles'],
    'policies': ['g', 'Dict, specifying the policies of all RACL groups']
}


# Default configuration to render the RACL package for systems that don't use RACL but need the
# type definitions
DEFAULT_RACL_CONFIG = {
    'nr_policies': 1,
    'policies': {},
}


def parse_racl_config(config_path: str) -> Dict[str, object]:
    try:
        with open(config_path, 'r') as f_racl_config:
            racl_config = hjson.load(f_racl_config)
    except OSError:
        raise SystemExit(sys.exc_info()[1])

    # TODO(#25690) Further sanity checks on the parsed RACL config
    error = check_keys(racl_config, racl_required, [], [], 'RACL Config')
    if error:
        raise SystemExit(f"Error occurred while validating {config_path}")

    # Determine the maximum number of policies over all RACL groups for RTL
    # RTL needs to create the vectors based on the largest group
    racl_config['nr_policies'] = max(len(policies) for policies in racl_config['policies'].values())

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
