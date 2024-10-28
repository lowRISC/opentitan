# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""This contains a class which is used to help generate `top_{name}.h` and
`top_{name}.h`.
"""
from typing import Dict

from reggen.ip_block import IpBlock

from .lib import CArrayMapping, CEnum, TopGen


class TopGenC(TopGen):
    def __init__(self, top_info, name_to_block: Dict[str, IpBlock]):
        super().__init__(top_info, name_to_block, CEnum, CArrayMapping)
        # The .c file needs the .h file's relative path, store it here
        self.header_path = None
