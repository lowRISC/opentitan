# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#

"""Generate a SystemRDL description of the block"""

from dataclasses import dataclass
from typing import TextIO

from reggen.ip_block import IpBlock
from reggen.exporter import Exporter

from systemrdl import RDLCompiler  # type: ignore[attr-defined]
from systemrdl.messages import FileSourceRef  # type: ignore[attr-defined]
from systemrdl.importer import RDLImporter
from systemrdl.component import Addrmap
from peakrdl_systemrdl import exporter


@dataclass
class IpBlock2Systemrdl:
    inner: IpBlock
    importer: RDLImporter

    def export(self) -> Addrmap | None:
        num_children = 0

        rdl_addrmap = self.importer.create_addrmap_definition(self.inner.name)

        for rb in self.inner.reg_blocks.values():
            rdl_rb = rb.to_systemrdl(self.importer)

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
