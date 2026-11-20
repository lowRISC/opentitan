# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import os
import tempfile
import unittest

from reggen.ip_block import IpBlock
from reggen.systemrdl_exporter import SystemrdlExporter

HMAC_HJSON = os.path.join(os.path.dirname(__file__), '..', '..', 'hw', 'ip',
                          'hmac', 'data', 'hmac.hjson')


class TestWindowExport(unittest.TestCase):
    def test_memwidth_is_in_bits(self):
        # The HMAC MSG_FIFO window has 32-bit entries.
        block = IpBlock.from_path(HMAC_HJSON, [])
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, 'hmac.rdl')
            with open(path, 'w', encoding='utf-8') as outfile:
                SystemrdlExporter(block).export(outfile)
            with open(path, encoding='utf-8') as rdl:
                text = rdl.read()
        self.assertIn('memwidth = 0x20;', text)
        self.assertIn('MSG_FIFO[1024] @ 0x1000 += 0x4;', text)
