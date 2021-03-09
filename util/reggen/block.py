# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''A subclass that can represent either a single block or a whole chip'''

from typing import Dict

from .reg_block import RegBlock


class Block:
    def __init__(self, name: str, regwidth: int, regs: RegBlock):
        assert regwidth > 0

        self.name = name
        self.regwidth = regwidth
        self.regs = regs

    def _asdict(self) -> Dict[str, object]:
        return {
            'name': self.name,
            'regwidth': self.regwidth,
            'regs': self.regs.as_dicts(),
        }
