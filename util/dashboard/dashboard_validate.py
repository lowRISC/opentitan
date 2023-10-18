# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Dashboard project JSON file validation
"""

import logging as log

from reggen.ip_block import OPTIONAL_FIELDS, REQUIRED_FIELDS


def check_keys(obj, required_keys, optional_keys, err_prefix):
    error = 0
    for x in required_keys:
        if x not in obj:
            error += 1
            log.error(err_prefix + " missing required key " + x)
    for x in obj:
        if x not in required_keys and x not in optional_keys:
            log.warning(err_prefix + " contains extra key " + x)

    return error


field_required = {
    'name': ['s', "module name"],
    'version': ['s', "module version"],
    'life_stage': ['s', "life stage of module"]
}
field_optional = {
    'design_spec':
    ['s', "path to the design specification, relative to repo root"],
    'dv_doc': ['s', "path to the DV document, relative to repo root"],
    'hw_checklist': ['s', "path to the hw_checklist, relative to repo root"],
    'sw_checklist': ['s', "path to the sw_checklist, relative to repo root"],
    'design_stage': ['s', "design stage of module"],
    'dif_stage': ['s', 'DIF stage of module'],
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
    'dif_stage': ['s', 'DIF stage of module'],
    'commit_id': ['s', "Staged commit ID"],
    'notes': ['s', "notes"],
}


def validate(regs, is_comportable_spec):
    if 'name' not in regs:
        log.error("Component has no name. Aborting.")
        return 1
    component = regs['name']

    # If this is a comportable IP definition file, we
    # need to use different requirements for validation.
    if is_comportable_spec:
        _field_required = REQUIRED_FIELDS
        _field_optional = OPTIONAL_FIELDS
    else:
        _field_required = field_required
        _field_optional = field_optional

    # If `revisions` is not in the object keys, the tool runs previous
    # version checker, which has only one version entry.
    if "revisions" not in regs:
        error = check_keys(regs, _field_required, _field_optional, component)
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
