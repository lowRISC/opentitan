# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""This contains a class which is used to help generate `top_{name}.rs`."""
from typing import Dict

from reggen.ip_block import IpBlock

from .lib import RustArrayMapping, RustEnum, RustFileHeader, TopGen
from version_file import VersionInformation


class TopGenRust(TopGen):
    def __init__(self, top_info, name_to_block: Dict[str, IpBlock],
                 version_stamp: VersionInformation):
        super().__init__(top_info, name_to_block, RustEnum, RustArrayMapping)
        self.file_header = RustFileHeader(version_stamp)
