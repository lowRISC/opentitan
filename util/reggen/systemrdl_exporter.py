# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#

"""Generate a SystemRDL description of the block"""

from dataclasses import dataclass
from typing import TextIO

from reggen.ip_block import IpBlock
from reggen.reg_block import RegBlock
from reggen.register import Register
from reggen.field import Field
from reggen.access import SWAccess, SwAccess
from reggen.exporter import Exporter

import systemrdl.component
from systemrdl import RDLCompiler  # type: ignore[attr-defined]
from systemrdl.messages import FileSourceRef  # type: ignore[attr-defined]
from systemrdl.importer import RDLImporter
from systemrdl.component import Addrmap
from systemrdl.rdltypes import AccessType, OnReadType, OnWriteType  # type: ignore[attr-defined]
from peakrdl_systemrdl import exporter


@dataclass
class SWAccess2Systemrdl:
    inner: SWAccess

    # Maps reggen software access property to SystemRDL properties. Each line in this table is
    # a set of RDL properties where:
    #   sw: Software read and write access.
    #   onread: Side effect when software reads.
    #   onwrite: Side effect when software writes.
    MAP = {
        SwAccess.RO: {"sw": AccessType.r},
        SwAccess.RC: {"sw": AccessType.r, "onread": OnReadType.rclr},
        SwAccess.R0W1C: {"sw": AccessType.w, "onwrite": OnWriteType.woclr},
        SwAccess.RW: {"sw": AccessType.rw},
        SwAccess.WO: {"sw": AccessType.w},
        SwAccess.W1C: {"sw": AccessType.w, "onwrite": OnWriteType.woset},
        SwAccess.W0C: {"sw": AccessType.w, "onwrite": OnWriteType.wzc},
        SwAccess.W1S: {"sw": AccessType.w, "onwrite": OnWriteType.woset},
        SwAccess.NONE: {"sw": AccessType.r},
    }

    def export(self) -> dict[str, object]:
        return self.MAP[self.inner.value[1]]


@dataclass
class Field2Systemrdl:
    inner: Field
    importer: RDLImporter

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

        hwaccess = self.inner.hwaccess.to_systemrdl()
        self.importer.assign_property(field, "hw", hwaccess["hw"])

        if self.inner.resval is not None:
            self.importer.assign_property(field, "reset", self.inner.resval)

        if self.inner.hwqe:
            self.importer.assign_property(field, "swmod", self.inner.hwqe)

        if self.inner.desc:
            self.importer.assign_property(field, "desc", self.inner.desc)

        return field


@dataclass
class Register2Systemrdl:
    inner: Register
    importer: RDLImporter

    def export(self) -> systemrdl.component.Reg:
        rdl_t = self.importer.create_reg_definition(self.inner.name)
        for rfield in self.inner.fields:
            self.importer.add_child(rdl_t, Field2Systemrdl(rfield, self.importer).export())

        return self.importer.instantiate_reg(rdl_t, self.inner.name, self.inner.offset)


@dataclass
class RegBlock2Systemrdl:
    inner: RegBlock
    importer: RDLImporter

    def export(self) -> Addrmap | None:
        nonempty = False

        name = self.inner.name or "none"
        rdl_addrmap_t = self.importer.create_addrmap_definition(name)
        rdl_addrmap = self.importer.instantiate_addrmap(rdl_addrmap_t, name, 0)

        # registers and multiregs
        for name, flat_reg in self.inner.name_to_flat_reg.items():
            nonempty = True
            self.importer.add_child(
                rdl_addrmap, Register2Systemrdl(flat_reg, self.importer).export()
            )

        # windows
        for window in self.inner.windows:
            nonempty = True
            self.importer.add_child(rdl_addrmap, window.to_systemrdl(self.importer))

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

        return rdl_addrmap if num_children else None


class SystemrdlExporter(Exporter):
    def export(self, outfile: TextIO) -> int:
        comp = RDLCompiler()
        imp = RDLImporter(comp)
        imp.default_src_ref = FileSourceRef(outfile.name)

        rdl_addrmap = IpBlock2Systemrdl(self.block, imp).export()
        if rdl_addrmap is None:
            raise RuntimeError("Block has no registers or windows.")

        imp.register_root_component(rdl_addrmap)

        # At this point, we actually have to close outfile and then pass its path
        # to exp.export (which expects a path rather than a stream).
        outfile.close()

        exporter.SystemRDLExporter().export(comp.elaborate(), outfile.name)

        return 0
