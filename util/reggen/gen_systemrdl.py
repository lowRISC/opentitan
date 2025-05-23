# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#

'''Generate a SystemRDL description of the block'''

from reggen.ip_block import IpBlock

def gen(block: IpBlock, outdir: str) -> int:
    print('gen_systemrdl')
    return 0
