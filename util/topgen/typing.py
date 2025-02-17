# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
'''Code providing types specific to topgen for generation'''

from typing import Dict

from reggen.ip_block import IpBlock

# Some common topgen types.

# This represents a map of names to IpBlocks, as for name_to_block.
IpBlocksT = Dict[str, IpBlock]
