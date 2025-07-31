# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from pathlib import Path
from typing import Any
from systemrdl.udp import UDPDefinition
from systemrdl import RDLCompiler  # type: ignore[attr-defined]
from systemrdl.node import Node
from systemrdl.component import Field


class UDPBoolean(UDPDefinition):
    valid_type = bool
    default_assignment = False

    def validate(self, node: Node, value: Any) -> None:
        if not isinstance(value, bool):
            self.msg.error("The type of {self.name} must be bool.", self.get_src_ref(node))


OPENTITAN_UDPS = Path(__file__).parent / "udp.rdl"


def register_udps(compiler: RDLCompiler) -> None:
    """
    Register opentitan specific UDPs (User Defined Properties)
    """
    compiler.compile_file(OPENTITAN_UDPS)
