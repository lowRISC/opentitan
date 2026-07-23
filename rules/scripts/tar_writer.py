#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""
Create a tar archive from a specification.
"""

import sys
import argparse
from pathlib import Path
import json
from tarfile import TarFile


def write_tar(tarpath: Path, spec: object):
    # TODO properly parse the spec
    assert isinstance(spec, dict)
    assert 'files' in spec
    assert isinstance(spec['files'], dict)

    tar = TarFile(tarpath, 'x')
    for (filename, filepath) in spec['files'].items():
        # We always resolve paths so that the archives contains actual files
        # and not symlinks.
        tar.add(Path(filepath).resolve(), filename, recursive = False)

    tar.close()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        '-o',
        action='store',
        required=True,
        dest='output',
        type=Path,
        help="output tar file",
    )
    parser.add_argument(
        '--spec',
        action='store',
        required=True,
        type=Path,
        help='Json specification of the archive')
    args = parser.parse_args()

    spec = json.loads(args.spec.read_text())
    write_tar(args.output, spec)


if __name__ == '__main__':
    sys.exit(main())
