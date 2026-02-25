# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Tests for bundler.py."""

import base64
import gzip
import json
import shutil
import tempfile
import unittest
from pathlib import Path

from util.coverage.viewer.bundler import main


class TestBundler(unittest.TestCase):

    def setUp(self) -> None:
        self.test_dir = Path(tempfile.mkdtemp())

    def tearDown(self) -> None:
        shutil.rmtree(self.test_dir)

    def test_bundler_end_to_end(self) -> None:
        html_template = self.test_dir / "template.html"
        html_template.write_text(
            "<html><script>// -- Bundled data --</script></html>")

        json_data = {"test": "data"}
        coverage_json = self.test_dir / "coverage.json.gz"
        with gzip.open(coverage_json, "wt") as f:
            json.dump(json_data, f)

        output_html = self.test_dir / "out.html"

        result = main([
            "--viewer_html",
            str(html_template), "--coverage_json",
            str(coverage_json), "--output",
            str(output_html)
        ])

        self.assertEqual(result, 0)
        self.assertTrue(output_html.exists())

        output_content = output_html.read_text()
        self.assertIn("bundledData.set('coverage.json.gz'", output_content)

        # Verify base64 data
        coverage_bytes = coverage_json.read_bytes()
        expected_b64 = base64.b64encode(coverage_bytes).decode('utf-8')
        self.assertIn(expected_b64, output_content)


if __name__ == "__main__":
    unittest.main()
