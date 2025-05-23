# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#

'''Generate a SystemRDL description of the block'''

import os

from reggen.ip_block import IpBlock

from systemrdl.importer import RDLImporter, RDLCompiler
from peakrdl_systemrdl import exporter


def gen(block: IpBlock, outdir: str) -> int:
    out_file = os.path.join(outdir or '', 'reg.rdl')

    comp = RDLCompiler()
    imp = RDLImporter(comp)
    imp.default_src_ref = None
    exp = exporter.SystemRDLExporter()

    rdl_addrmap = block.to_systemrdl(imp)
    if rdl_addrmap is None:
        raise RuntimeError('Block has no registers or windows.')

    imp.register_root_component(rdl_addrmap)

    exp.export(comp.elaborate(), out_file)
    return 0
