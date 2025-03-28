#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""
Create release tarball with filename stamping.
"""

import argparse
import tarfile
import datetime

from pathlib import Path


def main(args):
    with open(args.stamp_file) as f:
        stamp = dict(line.split(' ', 1) for line in f.readlines())

    version = args.version
    build_date = datetime.datetime.now().strftime('%Y-%m-%d')
    commit_hash = stamp["BUILD_SCM_REVISION_SHORT"].strip()
    commit_status = stamp["BUILD_SCM_STATUS"].strip()

    package_dir = f'{build_date}-v{version}-{commit_hash}'
    if commit_status != 'clean':
        package_dir += f'-{commit_status}'

    with tarfile.open(args.out, 'w') as tar:
        for path in args.files:
            path = Path(path)
            tar.add(path, arcname=f'{package_dir}/{path.name}')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--out', required=True, help='Path of the output tarball.')
    parser.add_argument('--stamp_file', required=True, help='Path of stamp variables.')
    parser.add_argument('--version', required=True, help='Release version string.')
    parser.add_argument('files', nargs='+')

    args = parser.parse_args()

    main(args)
