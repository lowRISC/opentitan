# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from pathlib import Path
from typing import Any
from systemrdl.udp import UDPDefinition
from systemrdl import RDLCompiler  # type: ignore[attr-defined]
from systemrdl.node import Node
from systemrdl.component import Reg, Mem, Signal


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


class IntegrityBypass(UDPBoolean):
    name = "integrity_bypass"
    valid_components = {Mem}


class SigType(UDPDefinition):
    default_assignment = None
    name = "sigtype"
    valid_components = {Signal}
    valid_type = "SigType"

    enum_map = {
        "None": 0,
        "Interrupt": 1,  # Signal is an interrupt
        "Alert": 2,  # Signal is an alert
        "InterModReqRsp": 3,  # Signal is an inter module, with type=req_rsp
        "InterModReq": 4,  # Signal is an inter module, with type=uni and act=req
        "InterModRecv": 5,  # Signal is an inter module, with type=uni and act=recv
        "Output": 6,  # Signal is an output
        "Input": 7,  # Signal is an input
        "Inout": 8,  # Signal is input and/or output
    }

    def validate(self, node: Node, value: Any) -> None:
        if value not in self.enum_map:
            self.msg.error(
                f"Invalid sigtype '{value}'. Expected one of {list(self.enum_map.keys())}"
            )


class InterModStruct(UDPDefinition):
    valid_type = str
    default_assignment = "logic"
    name = "inter_mod_struct"
    valid_components = {Signal}

    def validate(self, node: Node, value: Any) -> None:
        if not isinstance(value, str):
            self.msg.error("The type of {self.name} must be string.", self.get_src_ref(node))


class InterModPackage(UDPDefinition):
    valid_type = str
    name = "inter_mod_package"
    valid_components = {Signal}

    def validate(self, node: Node, value: Any) -> None:
        if not isinstance(value, str):
            self.msg.error("The type of {self.name} must be string.", self.get_src_ref(node))


OPENTITAN_UDPS = Path(__file__).parent / "udp.rdl"


def register_udps(compiler: RDLCompiler) -> Path:
    """
    Register opentitan specific UDPs (User Defined Properties)
    """
    compiler.register_udp(Hwre)
    compiler.register_udp(Shadowed)
    compiler.register_udp(AsyncClk)
    compiler.register_udp(IntegrityBypass)
    # TODO: figure out how to declare the 'valid_types' attribute when it is a user-defined enum.
    # compiler.register_udp(SigType)
    compiler.register_udp(InterModStruct)
    compiler.register_udp(InterModPackage)
    compiler.compile_file(OPENTITAN_UDPS)
    return OPENTITAN_UDPS
