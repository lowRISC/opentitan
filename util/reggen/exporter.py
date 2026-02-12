# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from abc import ABC, abstractmethod
from typing import TextIO
from reggen.ip_block import IpBlock


class Exporter(ABC):
    """
    An abstract base class defining the interface for a exporting hjson to other formats.
    Any concrete exporter must implement these methods.
    """

    def __init__(self, block: IpBlock):
        self.block = block

    @abstractmethod
    def export(self, outfile: TextIO) -> int:
        pass
