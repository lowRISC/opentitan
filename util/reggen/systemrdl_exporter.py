# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#

"""Generate a SystemRDL description of the block"""

from dataclasses import dataclass
from typing import TextIO
from pathlib import Path

from reggen.ip_block import IpBlock
from reggen.reg_block import RegBlock
from reggen.register import Register
from reggen.multi_register import MultiRegister
from reggen.window import Window
from reggen.field import Field
from reggen.access import SWAccess, HWAccess, HwAccess
from reggen.exporter import Exporter
from reggen.systemrdl.udp import register_udps

import systemrdl.component
from systemrdl import RDLCompiler  # type: ignore[attr-defined]
from systemrdl.messages import FileSourceRef  # type: ignore[attr-defined]
from systemrdl.importer import RDLImporter
from systemrdl.component import Addrmap
from systemrdl.core.parameter import Parameter
from systemrdl import rdltypes
from systemrdl.rdltypes import AccessType, OnReadType, OnWriteType  # type: ignore[attr-defined]
from rdlexporter import RdlExporter


@dataclass
class HWAccess2Systemrdl:
    inner: HWAccess

    # Maps reggen hardware access property to SystemRDL properties. Each line in this table is
    # a set of RDL properties where:
    #    hw: Hardware read and write access
    MAP = {
        HwAccess.HRO: {"hw": AccessType.r},
        HwAccess.HRW: {"hw": AccessType.rw},
        HwAccess.HWO: {"hw": AccessType.w},
        HwAccess.NONE: {"hw": AccessType.na},
    }

    def export(self) -> dict[str, object]:
        return self.MAP[self.inner.value[1]]


@dataclass
class SWAccess2Systemrdl:
    inner: SWAccess

    # Maps reggen software access property to SystemRDL properties. Each line in this table is
    # a set of RDL properties where:
    #   sw: Software read and write access.
    #   onread: Side effect when software reads.
    #   onwrite: Side effect when software writes.
    MAP = {
        "ro": {"sw": AccessType.r},
        "rw": {"sw": AccessType.rw},
        "wo": {"sw": AccessType.w},
        "rc": {"sw": AccessType.rw, "onread": OnReadType.rclr},
        "r0w1c": {"sw": AccessType.w, "onwrite": OnWriteType.woclr},
        "rw1c": {"sw": AccessType.rw, "onwrite": OnWriteType.woclr},
        "rw0c": {"sw": AccessType.rw, "onwrite": OnWriteType.wzc},
        "rw1s": {"sw": AccessType.rw, "onwrite": OnWriteType.woset},
        "none": {"sw": AccessType.na},
    }

    def export(self) -> dict[str, object]:
        return self.MAP[self.inner.key]


@dataclass
class Field2Systemrdl:
    inner: Field
    importer: RDLImporter

    def _get_mubi_name(self) -> str:
        alignment = 4
        aligned_width = (self.inner.bits.width() + alignment - 1) & ~(alignment - 1)
        return f"MultiBitBool{aligned_width}"

    def export(self) -> systemrdl.component.Field:
        rdl_t = self.importer.create_field_definition(self.inner.name)
        field = self.importer.instantiate_field(
            rdl_t, self.inner.name.upper(), self.inner.bits.lsb, self.inner.bits.width()
        )

        swaccess = SWAccess2Systemrdl(self.inner.swaccess).export()
        self.importer.assign_property(field, "sw", swaccess["sw"])
        if "onread" in swaccess:
            self.importer.assign_property(field, "onread", swaccess["onread"])
        if "onwrite" in swaccess:
            self.importer.assign_property(field, "onwrite", swaccess["onwrite"])

        hwaccess = HWAccess2Systemrdl(self.inner.hwaccess).export()
        self.importer.assign_property(field, "hw", hwaccess["hw"])

        if self.inner.resval is not None:
            self.importer.assign_property(field, "reset", self.inner.resval)

        if self.inner.hwqe:
            self.importer.assign_property(field, "swmod", self.inner.hwqe)

        if self.inner.desc:
            self.importer.assign_property(field, "desc", self.inner.desc)

        if self.inner.mubi:
            mubi_enum_name = self._get_mubi_name()
            enum = self.importer.compiler.namespace.lookup_type(mubi_enum_name)
            self.importer.assign_property(field, "encode", enum)

        return field


@dataclass
class Window2Systemrdl:
    inner: Window
    importer: RDLImporter

    def export(self) -> systemrdl.component.Mem:
        rdl_mem_t = self.importer.create_mem_definition(self.inner.name)
        memwidth = self.inner.size_in_bytes // self.inner.items
        self.importer.assign_property(rdl_mem_t, "memwidth", memwidth * 8)
        self.importer.assign_property(rdl_mem_t, "mementries", self.inner.items)
        return self.importer.instantiate_mem(
            rdl_mem_t, self.inner.name, self.inner.offset, [self.inner.items]
        )


class Register2Systemrdl:
    inner: Register
    importer: RDLImporter
    stride: int | None = None
    count: int | None = None

    def __init__(self, reg: MultiRegister | Register, importer: RDLImporter):
        self.importer = importer
        if isinstance(reg, Register):
            self.inner = reg
        elif isinstance(reg, MultiRegister):
            self.inner = reg.cregs[0]
            self.stride = reg.stride
            self.count = len(reg.cregs)

    def export(self) -> systemrdl.component.Reg:
        reg_type = self.importer.create_reg_definition(self.inner.name)
        for rfield in self.inner.fields:
            self.importer.add_child(reg_type, Field2Systemrdl(rfield, self.importer).export())

        reg_type.external = self.inner.hwext

        if self.inner.hwre:
            self.importer.assign_property(reg_type, "hwre", self.inner.hwre)

        if self.inner.shadowed:
            self.importer.assign_property(reg_type, "shadowed", self.inner.shadowed)

        reg = self.importer.instantiate_reg(
            reg_type,
            self.inner.name,
            self.inner.offset,
            [self.count] if self.count else None,
            self.stride if self.stride else None,
        )
        return reg


@dataclass
class RegBlock2Systemrdl:
    inner: RegBlock
    importer: RDLImporter

    def export(self) -> Addrmap | None:
        name = self.inner.name or "Block"
        rdl_addrmap_t = self.importer.create_addrmap_definition(name)
        rdl_addrmap = self.importer.instantiate_addrmap(rdl_addrmap_t, name, 0)

        # registers and multiregs
        for reg in self.inner.registers:
            self.importer.add_child(rdl_addrmap, Register2Systemrdl(reg, self.importer).export())

        # multiregs
        for mreg in self.inner.multiregs:
            self.importer.add_child(rdl_addrmap, Register2Systemrdl(mreg, self.importer).export())

        # windows
        for window in self.inner.windows:
            self.importer.add_child(rdl_addrmap, Window2Systemrdl(window, self.importer).export())

        nonempty = bool(
            len(self.inner.registers) + len(self.inner.multiregs) + len(self.inner.windows)
        )
        return rdl_addrmap if nonempty else None


@dataclass
class IpBlock2Systemrdl:
    inner: IpBlock
    importer: RDLImporter

    def export(self) -> Addrmap | None:
        num_children = 0

        rdl_addrmap = self.importer.create_addrmap_definition(self.inner.name)

        for rb in self.inner.reg_blocks.values():
            rdl_rb = RegBlock2Systemrdl(rb, self.importer).export()

            # Skip empty interfaces
            if rdl_rb is None:
                continue

            self.importer.add_child(rdl_addrmap, rdl_rb)
            num_children += 1

        if num_children > 1:
            rdl_addrmap.properties["bridge"] = True

        for param in self.inner.params.get_localparams():
            value = int(param.value)
            rdl_param = Parameter(rdltypes.get_rdltype(value), param.name)
            rdl_param._value = value
            rdl_addrmap.parameters.append(rdl_param)

        return rdl_addrmap if num_children else None


class SystemrdlExporter(Exporter):
    def export(self, outfile: TextIO) -> int:
        comp = RDLCompiler()
        register_udps(comp)

        imp = RDLImporter(comp)
        imp.default_src_ref = FileSourceRef(outfile.name)

        try:
            rdl_addrmap = IpBlock2Systemrdl(self.block, imp).export()
        except Exception as e:
            raise RuntimeError(f"Error while building RDL AST for {self.block.name}.") from e

        if rdl_addrmap is None:
            raise RuntimeError("Block {self.block.name} has no registers or windows.")

        imp.register_root_component(rdl_addrmap)

        # At this point, we actually have to close outfile and then pass its path
        # to exp.export (which expects a path rather than a stream).
        outfile.close()

        try:
            RdlExporter(comp).export(Path(outfile.name))
        except Exception as e:
            raise RuntimeError(f"Error exporting {self.block.name} to RDL.") from e

        print(f"Successfully generated {outfile.name}")

        return 0
