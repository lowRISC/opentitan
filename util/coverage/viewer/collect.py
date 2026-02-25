#!/usr/bin/env python3

# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""CLI tool to collect LCOV files and generate a unified coverage JSON."""

import argparse
import sys
import json
import gzip
import subprocess
from datetime import datetime
from pathlib import Path
from typing import List, Optional

from util.coverage.viewer.lcov import iter_lcov_files
from util.coverage.viewer.coverage_data import CoverageCollection


def get_git_commit() -> Optional[str]:
    """Retrieves the current Git commit hash of the repository."""
    try:
        return subprocess.check_output(['git', 'rev-parse',
                                        'HEAD']).decode().strip()
    except (subprocess.CalledProcessError, FileNotFoundError):
        return None


def main(argv: Optional[List[str]] = None) -> int:
    """Entry point for the coverage collection script."""
    parser = argparse.ArgumentParser(
        description=
        'Collects lcov files and saves coverage data to a gzipped JSON file.')
    parser.add_argument(
        '--lcov_files',
        type=Path,
        default=Path('bazel-out/_coverage/lcov_files.tmp'),
        help='Path to the file containing a list of lcov files.')
    parser.add_argument(
        '--coverage_dir',
        type=Path,
        default=Path('.'),
        help='Directory for resolving relative paths in lcov_files.')
    parser.add_argument(
        '--source_dir',
        type=Path,
        default=Path('.'),
        help='Directory for resolving relative source file paths.')
    parser.add_argument('--output',
                        type=Path,
                        default=Path('bazel-out/_coverage/coverage.json.gz'),
                        help='Path to the output gzipped JSON file.')
    args = parser.parse_args(argv)

    test = CoverageCollection(source_dir=args.source_dir)
    view = CoverageCollection(source_dir=args.source_dir)

    for test_lcov in iter_lcov_files(args.lcov_files, args.coverage_dir):
        if test_lcov.name.endswith('_coverage_view'):
            print(f'Processing view {test_lcov.name}...')
            view.add_test(test_lcov.name, test_lcov.files, add_uncovered=True)
        else:
            print(f'Processing test {test_lcov.name}...')
            test.add_test(test_lcov.name, test_lcov.files, add_uncovered=False)

    result = {
        'metadata': {
            'timestamp': datetime.now().replace(microsecond=0).isoformat(),
            'commit': get_git_commit(),
        },
        'test': test.as_dict(),
        'view': view.as_dict(),
    }

    print(f'Saving json to {args.output}')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with gzip.open(args.output, 'wt') as f:
        json.dump(result, f)

    return 0


if __name__ == '__main__':
    main(sys.argv[1:])
