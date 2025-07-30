# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#

"""Generate a SystemRDL description of the block"""

import re
from dataclasses import dataclass
from typing import TextIO
from pathlib import Path
import shutil

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


def sanitize_str(s: str) -> str:
    substitutions = [(r"\\:", ":"), ("`", ""), (r"\n", ""), ('''"''', '''\\"''')]
    for pattern, replacement in substitutions:
        s = re.sub(pattern, replacement, s)
    return s


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

    def export(
        self, strip_suffix: bool = False, regwen: str | None = None
    ) -> systemrdl.component.Field:
        # Workaround because reggen adds the register index to all multiregisters fields,
        # although it only makes sense when multiregisters are compacted (collapsed)
        # to avoid name colision.

        name = re.sub(r"_\d+$", "", self.inner.name) if strip_suffix else self.inner.name

        rdl_t = self.importer.create_field_definition(name)
        field = self.importer.instantiate_field(
            rdl_t, name.upper(), self.inner.bits.lsb, self.inner.bits.width()
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
            self.importer.assign_property(field, "desc", sanitize_str(self.inner.desc))

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

        swaccess = SWAccess2Systemrdl(self.inner.swaccess).export()
        self.importer.assign_property(rdl_mem_t, "sw", swaccess["sw"])

        if self.inner.data_intg_passthru:
            self.importer.assign_property(rdl_mem_t, "integrity_bypass", True)

        return self.importer.instantiate_mem(rdl_mem_t, self.inner.name.upper(), self.inner.offset)


class Register2Systemrdl:
    inner: Register
    importer: RDLImporter
    stride: int | None = None
    count: int | None = None
    strip_suffix: bool = False
    name: str = ""

    def __init__(self, reg: MultiRegister | Register, importer: RDLImporter):
        self.importer = importer
        if isinstance(reg, Register):
            self.inner = reg
            self.name = reg.name
        elif isinstance(reg, MultiRegister):
            self.inner = reg.cregs[0]
            self.stride = reg.stride
            self.count = len(reg.cregs)
            # Workaround because reggen adds the register index to all multiregisters fields,
            # although it only makes sense when multiregisters are compacted (collapsed)
            # to avoid name colision.
            self.strip_suffix = not self._has_name_colision(reg)
            self.name = re.sub(r"_\d+$", "", self.inner.name)

    def export(self) -> systemrdl.component.Reg:
        reg_type = self.importer.create_reg_definition(self.inner.name)
        for rfield in self.inner.fields:
            self.importer.add_child(
                reg_type,
                Field2Systemrdl(rfield, self.importer).export(self.strip_suffix, self.inner.regwen),
            )

        reg_type.external = self.inner.hwext

        if self.inner.hwre:
            self.importer.assign_property(reg_type, "hwre", self.inner.hwre)

        if self.inner.shadowed:
            self.importer.assign_property(reg_type, "shadowed", self.inner.shadowed)

        if self.inner.desc:
            self.importer.assign_property(reg_type, "desc", sanitize_str(self.inner.desc))

        if self.inner.async_clk:
            self.importer.assign_property(reg_type, "async_clk", True)

        reg = self.importer.instantiate_reg(
            reg_type,
            self.name.upper(),
            self.inner.offset,
            [self.count] if self.count else None,
            self.stride if self.stride else None,
        )
        return reg

    def _has_name_colision(self, reg: MultiRegister) -> bool:
        names = set([re.sub(r"_\d+$", "", f.name) for f in reg.cregs[0].fields])
        return len(names) != len(reg.cregs[0].fields)


@dataclass
class RegBlock2Systemrdl:
    inner: RegBlock
    importer: RDLImporter

    def export(self, addrmap: Addrmap | None = None) -> Addrmap | None:
        if not addrmap:
            name = self.inner.name or "Block"
            rdl_addrmap_t = self.importer.create_addrmap_definition(name)
            addrmap = self.importer.instantiate_addrmap(rdl_addrmap_t, name.upper(), 0)

        # registers and multiregs
        for reg in self.inner.registers:
            self.importer.add_child(addrmap, Register2Systemrdl(reg, self.importer).export())

        # multiregs
        for mreg in self.inner.multiregs:
            self.importer.add_child(addrmap, Register2Systemrdl(mreg, self.importer).export())

        # windows
        for window in self.inner.windows:
            self.importer.add_child(addrmap, Window2Systemrdl(window, self.importer).export())

        nonempty = bool(
            len(self.inner.registers) + len(self.inner.multiregs) + len(self.inner.windows)
        )
        return addrmap if nonempty else None


@dataclass
class IpBlock2Systemrdl:
    inner: IpBlock
    importer: RDLImporter

    def export(self) -> Addrmap | None:
        rdl_addrmap = self.importer.create_addrmap_definition(self.inner.name)

        for param in self.inner.params.get_localparams():
            value = int(param.value)
            rdl_param = Parameter(rdltypes.get_rdltype(value), param.name)
            rdl_param._value = value
            rdl_addrmap.parameters.append(rdl_param)

        interfaces = list(self.inner.reg_blocks.values())
        if len(interfaces) == 1 and not bool(interfaces[0].name):
            # If there's only one interface, the registers can go directly on the root addressmap.
            RegBlock2Systemrdl(interfaces[0], self.importer).export(rdl_addrmap)
            return rdl_addrmap

        num_children = 0
        for rb in interfaces:
            rdl_rb = RegBlock2Systemrdl(rb, self.importer).export()

            # Skip empty interfaces
            if rdl_rb is None:
                continue

            self.importer.add_child(rdl_addrmap, rdl_rb)
            num_children += 1

        if num_children > 1:
            rdl_addrmap.properties["bridge"] = True

        return rdl_addrmap if num_children else None


def check_rdl(rdl: Path) -> None:
    compiler = RDLCompiler()
    try:
        compiler.compile_file(rdl)
        compiler.elaborate()
    except Exception as e:
        raise RuntimeError(f"Error while compiling {rdl}.") from e


class SystemrdlExporter(Exporter):
    def export(self, outfile: TextIO) -> int:
        comp = RDLCompiler()
        udp_path = register_udps(comp)

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

        outpath = Path(outfile.name)
        # Include the user defined enums and properties.
        with outpath.open("w") as f:
            f.write(f'`include "{udp_path.name}"\n\n')
        # Copy the inlcude file to the output dir.
        shutil.copy(udp_path, outpath.parent / udp_path.name)

        try:
            RdlExporter(comp).export(outpath)
        except Exception as e:
            raise RuntimeError(f"Error exporting {self.block.name} to RDL.") from e

        print(f"Successfully generated {outfile.name}, {outpath.parent / udp_path.name}")

        check_rdl(outpath)
        print(f"Successfully generated {outfile.name}, {outpath.parent / udp_path.name}")
        return 0
