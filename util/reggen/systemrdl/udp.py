# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from pathlib import Path
from typing import Any
from systemrdl.udp import UDPDefinition
from systemrdl import RDLCompiler  # type: ignore[attr-defined]
from systemrdl.node import Node
from systemrdl.component import Reg


class UDPBoolean(UDPDefinition):
    valid_type = bool
    default_assignment = False

    def validate(self, node: Node, value: Any) -> None:
        if not isinstance(value, bool):
            self.msg.error("The type of {self.name} must be bool.", self.get_src_ref(node))


class Hwre(UDPBoolean):
    name = "Hwre"
    valid_components = {Reg}


class Shadowed(UDPBoolean):
    name = "shadowed"
    valid_components = {Reg}


class AsyncClk(UDPBoolean):
    name = "async_clk"
    valid_components = {Reg}


OPENTITAN_UDPS = Path(__file__).parent / "udp.rdl"


def register_udps(compiler: RDLCompiler) -> Path:
    """
    Register opentitan specific UDPs (User Defined Properties)
    """
    compiler.register_udp(Hwre)
    compiler.register_udp(Shadowed)
    compiler.register_udp(AsyncClk)
    compiler.compile_file(OPENTITAN_UDPS)
    return OPENTITAN_UDPS
