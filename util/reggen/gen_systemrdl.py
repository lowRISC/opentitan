# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#

'''Generate a SystemRDL description of the block'''

import os

from reggen.ip_block import IpBlock

from systemrdl.node import AddrmapNode
from systemrdl.compiler import RDLEnvironment
from systemrdl.importer import RDLImporter, RDLCompiler
from peakrdl_systemrdl import exporter


def gen(block: IpBlock, outdir: str) -> int:
    out_file = os.path.join(outdir or '', 'reg.rdl')

    comp = RDLCompiler()
    imp = RDLImporter(comp)
    imp.default_src_ref = None
    exp = exporter.SystemRDLExporter()

    empty_env = RDLEnvironment({})
    node = AddrmapNode(block.to_systemrdl(imp),
                       empty_env,
                       None)

    exp.export(node, out_file)
    return 0
