#!/usr/bin/env python3

# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Tool to bundle coverage JSON data into a standalone HTML report."""

import argparse
import base64
from pathlib import Path

from typing import List, Optional


def main(argv: Optional[List[str]] = None) -> int:
    """Entry point for the coverage bundler script."""
    parser = argparse.ArgumentParser(
        description='Bundles coverage JSON data into the viewer HTML.')
    parser.add_argument('--viewer_html',
                        type=Path,
                        default=Path(__file__).parent / 'viewer.html',
                        help='Path to the viewer HTML template.')
    parser.add_argument('--coverage_json',
                        type=Path,
                        default=Path('bazel-out/_coverage/coverage.json.gz'),
                        help='Path to the gzipped JSON coverage data file.')
    parser.add_argument('--output',
                        type=Path,
                        default=Path('bazel-out/_coverage/viewer/index.html'),
                        help='Path to the output HTML file with bundled data.')
    args = parser.parse_args(argv)

    if not args.viewer_html.exists():
        print(f"Error: Viewer HTML template not found: {args.viewer_html}")
        return 1

    if not args.coverage_json.exists():
        print(f"Error: Coverage JSON data not found: {args.coverage_json}")
        return 1

    # Read the viewer HTML template
    template = args.viewer_html.read_text()

    # Read and base64 encode the gzipped coverage JSON
    coverage_data_gz = args.coverage_json.read_bytes()
    coverage_data_b64 = base64.b64encode(coverage_data_gz).decode('utf-8')

    # Prepare the bundled data JavaScript
    bundled_data_js = f"""
      bundledData.set('coverage.json.gz', `{coverage_data_b64}`);
    """

    # Insert bundled data into the HTML
    placeholder = '// -- Bundled data --'
    if placeholder not in template:
        print(f"Error: Could not find placeholder in {args.viewer_html}")
        return 1
    output_html_content = template.replace(placeholder, bundled_data_js, 1)

    # Write the output HTML file
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(output_html_content)

    print(f"Bundled coverage data into {args.output}")
    return 0


if __name__ == '__main__':
    exit(main())
