# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Dashboard project JSON file validation
"""

import logging as log
import sys


def check_keys(obj, required_keys, optional_keys, err_prefix):
    error = 0
    for x in required_keys:
        if not x in obj:
            error += 1
            log.error(err_prefix + " missing required key " + x)
    for x in obj:
        type = ''
        if x in required_keys:
            type = required_keys[x][0]
        elif x in optional_keys:
            type = optional_keys[x][0]
        else:
            log.warning(err_prefix + " contains extra key " + x)

    return error


field_required = {
    'name': ['s', "module name"],
    'version': ['s', "module version"],
    'life_stage': ['s', "life stage of module"]
}
field_optional = {
    'design_stage': ['s', "design stage of module"],
    'verification_stage': ['s', "verification stage of module"],
    'notes': ['s', "random notes"],
}

entry_required = {
    'version': ['s', "module version"],
    'life_stage': ['s', "life stage of module"]
}
entry_optional = {
    'design_stage': ['s', "design stage of module"],
    'verification_stage': ['s', "verification stage of module"],
    'commit_id': ['s', "Staged commit ID"],
    'notes': ['s', "notes"],
}


def validate(regs):
    if not 'name' in regs:
        log.error("Component has no name. Aborting.")
        return 1
    component = regs['name']

    # If `revisions` is not in the object keys, the tool runs previous
    # version checker, which has only one version entry.
    if not "revisions" in regs:
        error = check_keys(regs, field_required, field_optional, component)
        if (error > 0):
            log.error("Component has top level errors. Aborting.")
        return error

    # Assumes `revisions` field exists in the Hjson object.
    # It iterates the entries in the `revisions` group.
    error = 0
    if not isinstance(regs['revisions'], list):
        error += 1
        log.error("`revisions` field should be a list of version entries")
        return error

    for rev in regs['revisions']:
        error += check_keys(rev, entry_required, entry_optional, component)

    if (error > 0):
        log.error("Component has errors in revision field. Aborting.")

    return error
