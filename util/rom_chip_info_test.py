# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import pathlib
import unittest
from unittest.mock import mock_open
from unittest.mock import patch

import rom_chip_info


EXAMPLE_SHA1_DIGEST = 0x4bbd966dcbfc4aa39291f4de9f52bc0f66ca32a4


class TestGenerateChipInfoCSource(unittest.TestCase):
    def test_simple(self):
        source = rom_chip_info.generate_chip_info_c_source(EXAMPLE_SHA1_DIGEST)
        expected = """
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// --------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! ---------//

#include "sw/device/silicon_creator/lib/chip_info.h"

#include "sw/device/lib/base/macros.h"

OT_SECTION(".chip_info")
const chip_info_t kChipInfo = {
  .scm_revision = (chip_info_scm_revision_t){
    .scm_revision_low = 0xcbfc4aa3,
    .scm_revision_high = 0x4bbd966d,
  },
  .version = (uint32_t)kChipInfoVersion1,
};
"""
        self.assertEqual(source, expected)

    def test_sha1_digest_leading_zero_byte(self):
        digest = EXAMPLE_SHA1_DIGEST >> 8
        source = rom_chip_info.generate_chip_info_c_source(digest)
        expected = """
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// --------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! ---------//

#include "sw/device/silicon_creator/lib/chip_info.h"

#include "sw/device/lib/base/macros.h"

OT_SECTION(".chip_info")
const chip_info_t kChipInfo = {
  .scm_revision = (chip_info_scm_revision_t){
    .scm_revision_low = 0x6dcbfc4a,
    .scm_revision_high = 0x004bbd96,
  },
  .version = (uint32_t)kChipInfoVersion1,
};
"""
        self.assertEqual(source, expected)

    def test_sha1_digest_too_large(self):
        # Compute the max SHA1 digest plus one.
        INVALID_SHA1_DIGEST_LARGE = 2**(20 * 8)
        with self.assertRaises(AssertionError):
            rom_chip_info.generate_chip_info_c_source(
                INVALID_SHA1_DIGEST_LARGE)

    def test_sha1_digest_too_small(self):
        INVALID_SHA1_DIGEST_SMALL = -1
        with self.assertRaises(AssertionError):
            rom_chip_info.generate_chip_info_c_source(
                INVALID_SHA1_DIGEST_SMALL)


class TestFileOperations(unittest.TestCase):
    @patch('rom_chip_info.open',
           mock_open(read_data=f'{EXAMPLE_SHA1_DIGEST:x}'))
    def test_read_version_file(self):
        """Reading a properly-formatted version file produces the expected int.
        """
        version = rom_chip_info.read_version_file(
            pathlib.Path("fake/path/version.txt"))
        self.assertEqual(version, EXAMPLE_SHA1_DIGEST)

    @patch("rom_chip_info.open", mock_open(read_data=''))
    def test_read_version_file_empty(self):
        """Reading an empty version file raises an exception.
        """
        with self.assertRaisesRegex(ValueError, "invalid literal for int"):
            rom_chip_info.read_version_file(
                pathlib.Path("fake/path/version.txt"))

    @patch("rom_chip_info.open", mock_open(read_data='xyz'))
    def test_read_version_file_invalid_hex(self):
        """Reading an invalid version file raises an exception.
        """
        with self.assertRaisesRegex(ValueError, "invalid literal for int"):
            rom_chip_info.read_version_file(
                pathlib.Path("fake/path/version.txt"))

    @patch("pathlib.Path.open", new_callable=mock_open)
    def test_write_source_file(self, mock_path_open):
        """Calling write_source_file() produces the expected file.
        """
        src_path = rom_chip_info.write_source_file(pathlib.Path("fake/out/"),
                                                   "// This is a C program")
        self.assertEqual(src_path, pathlib.Path("fake/out/chip_info.c"))
        mock_path_open.assert_called_once_with(mode='w', encoding='utf-8')

        handle = mock_path_open()
        handle.write.assert_called_once_with('// This is a C program')


if __name__ == '__main__':
    unittest.main()
