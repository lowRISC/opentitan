# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Generate JSON/compact JSON/Hjson from register JSON tree
"""

import hjson


def gen_json(obj, outfile, format):
    # Temporary hack to deal with the fact that the 'registers' field is a list
    # rather than a dictionary. When we convert the top-level object to a class
    # (with its own _as_dict method), this logic can go in there.
    obj = obj.copy()
    obj['registers'] = obj['registers'].as_dicts()

    if format == 'json':
        hjson.dumpJSON(obj,
                       outfile,
                       ensure_ascii=False,
                       use_decimal=True,
                       indent='  ',
                       for_json=True)
    elif format == 'compact':
        hjson.dumpJSON(obj,
                       outfile,
                       ensure_ascii=False,
                       for_json=True,
                       use_decimal=True,
                       separators=(',', ':'))
    elif format == 'hjson':
        hjson.dump(obj,
                   outfile,
                   ensure_ascii=False,
                   for_json=True,
                   use_decimal=True)
    else:
        raise ValueError('Invalid JSON format ' + format)

    return 0
