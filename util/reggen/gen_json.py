# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Generate JSON/compact JSON/Hjson from register JSON tree
"""

from typing import Any, TextIO

import hjson  # type: ignore


def gen_json(obj: Any, outfile: TextIO, format: str) -> None:
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
