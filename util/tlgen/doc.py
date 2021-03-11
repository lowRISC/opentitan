# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""TileLink-Uncached Lightweight Xbar self document
"""
import logging as log

from reggen.validate import val_types

from .validate import root

doc_intro = """

The tables describe each key and the type of the value. The following
types are used:

Type | Description
---- | -----------
"""


def print_control(control, heading):
    """Print a control group and its subgroup recursively
    """
    subgroup = []  # added if the field hit sub control group

    outstr = '#' * heading + ' ' + control['name'] + '\n'
    outstr += '\n'

    outstr += control['description']
    outstr += '\n\n'

    items = {**control['required'], **control['optional'], **control['added']}

    if len(items) > 0:
        outstr += """
Field | Kind | Type | Description
----- | ---- | ---- | ------------
"""
    for k, v in items.items():
        if k in control['required']:
            kind = "required"
        elif k in control['optional']:
            kind = "optional"
        else:
            kind = "added by tool"

        v_type = val_types[v[0]][0]

        if v[0] == 'lg':
            subgroup.append(v[1])
            log.error(val_types[v[0]])
            outstr += '{} | {} | {} | List of {} group\n'.format(
                k, kind, v_type, k)
            continue
        elif v[0] == 'g':
            if not isinstance(v[1], str):
                subgroup.append(v[1])
                outstr += '{} | {} | {} | {} group\n'.format(
                    k, kind, v_type, k)
                continue

        # Generic string print
        outstr += '{} | {} | {} | {}\n'.format(k, kind, v_type, v[1])

    outstr += "\n\n"
    # recursive subgroup
    for e in subgroup:
        outstr += print_control(e, heading)

    return outstr


def selfdoc(heading, cmd=""):
    # heading : Markdown header depth
    # value type
    outstr = doc_intro

    for k, v in val_types.items():
        outstr += v[0] + " | " + v[1] + "\n"

    # root + subgroup
    outstr += print_control(root, heading)

    # connections: Needs custom as the key are hosts (can vary)

    return outstr
