# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Generate C header from validated register JSON tree
"""

import logging as log
from typing import TextIO

from mako import exceptions  # type: ignore
from mako.lookup import TemplateLookup  # type: ignore
from pkg_resources import resource_filename

from reggen.ip_block import IpBlock


def gen_dt_api(block: IpBlock, outfile: TextIO, include_guard: str) -> int:
    '''Generate DT API files for an IpBlock'''

    lookup = TemplateLookup(directories=[resource_filename('reggen', '.')])
    dt_api_tpl = lookup.get_template('dt_api.h.tpl')

    try:
        contents = dt_api_tpl.render(block=block, include_guard=include_guard)
    except:  # noqa F722 for template Exception handling
        log.error(exceptions.text_error_template().render())
        return 1

    outfile.write(contents)
    return 0
