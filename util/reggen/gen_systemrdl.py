# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#

"""Generate a SystemRDL description of the block"""

from typing import TextIO

from reggen.ip_block import IpBlock

from systemrdl import RDLCompiler  # type: ignore[attr-defined]
from systemrdl.messages import FileSourceRef  # type: ignore[attr-defined]
from systemrdl.importer import RDLImporter
from peakrdl_systemrdl import exporter


def gen(block: IpBlock, outfile: TextIO) -> int:
    comp = RDLCompiler()
    imp = RDLImporter(comp)
    imp.default_src_ref = FileSourceRef(outfile.name)

    rdl_addrmap = block.to_systemrdl(imp)
    if rdl_addrmap is None:
        raise RuntimeError("Block has no registers or windows.")

    imp.register_root_component(rdl_addrmap)

    # At this point, we actually have to close outfile and then pass its path
    # to exp.export (which expects a path rather than a stream).
    outfile.close()

    exporter.SystemRDLExporter().export(comp.elaborate(), outfile.name)

    return 0
