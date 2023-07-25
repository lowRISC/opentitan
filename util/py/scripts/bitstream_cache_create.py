#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import json
import jsonschema
import os
import stat
import sys
import tarfile

from pathlib import Path
from typing import Dict

"""Creates bitstreams cache directory entry from an input manifest.
The input manifest has the same set of keys as a bitstreams cache manifest,
except the file paths are relative to the bazel execution root. This script
prepares a proper cache directory named by the SCM revision, the manifest in the
root of that directory, and the files in directories below.

This script creates symlinks to the real files. If creating a distributable
archive, make sure to dereference the symlinks and copy the real files into the
archive.
"""

parser = argparse.ArgumentParser(
    description='Bitstream Cache Entry Generator')
parser.add_argument('fragment', nargs='+',
                    help='Path to manifest fragment file')
parser.add_argument('--schema', required=True, help='Path to validation schema')
parser.add_argument('--stamp-file', required=True,
                    help='A file supplying the stamp in BUILD_SCM_REVISION')
parser.add_argument('--out', required=True, help='Path to the output directory.')


def collect_file_map(fragment: Dict, fragment_dir: Path):
    """Get a map of files to their shortened paths in the tar files. The new
    paths will consist of a flat directory collecting all files related to a
    design. The directory will be named the same as the design.
    """
    file_map = {}
    for design, metadata in fragment['designs'].items():
        bitstream = os.path.join(fragment_dir, metadata['bitstream']['file'])
        bitstream_renamed = os.path.join(design, os.path.basename(bitstream))
        file_map[bitstream] = bitstream_renamed
        for mmi in metadata['memory_map_info'].values():
            mmi_file = os.path.join(fragment_dir, mmi['file'])
            mmi_renamed = os.path.join(design, os.path.basename(mmi_file))
            file_map[mmi_file] = mmi_renamed
    return file_map


def get_scm_revision(volatile_status_file: Path):
    """Get BUILD_SCM_REVISION string from the volatile status file.
    """
    with open(volatile_status_file, 'r') as f:
        for line in f:
            tokens = line.strip().split(' ')
            if len(tokens) == 2 and tokens[0] == 'BUILD_SCM_REVISION':
                return tokens[1]
    raise Exception('Could not get BUILD_SCM_REVISION from {}.'.format(volatile_status_file))


def update_manifest_stamps(manifest: Dict, stamp: str):
    """Stamp build_id objects for any files in the manifest that do not have
    them already. The build_id objects should only be missing for files that
    need the new stamp.
    """
    for metadata in manifest['designs'].values():
        if 'build_id' not in metadata:
            metadata['build_id'] = stamp


def create_archive(outfile: str, manifest: Dict, file_map: Dict):
    def reset_info(info):
        info.uname = 'root'
        info.uid = 0
        info.gname = 'root'
        info.gid = 0
        info.mode = stat.S_IWUSR | stat.S_IRUSR | stat.S_IRGRP | stat.S_IROTH
        return info
    tar = tarfile.open(outfile, 'w:gz', dereference=True)
    tar.add(manifest, arcname='manifest.json',
            filter=reset_info)
    for file_path, short_path in file_map.items():
        tar.add(file_path, arcname=short_path,
                filter=reset_info)
    tar.close()


def main(argv: list[str]):
    args = parser.parse_args(args=argv[1:])
    stamp = get_scm_revision(args.stamp_file)
    manifest = {
        'schema_version': 2,
        'designs': {},
    }
    file_map = {}
    with open(args.schema) as schema_file:
        schema = json.load(schema_file)
    for fragment_path in args.fragment:
        with open(fragment_path, 'r') as fragment_file:
            fragment = json.load(fragment_file)
            jsonschema.validate(fragment, schema)
            fragment_dir = os.path.dirname(fragment_path)
            file_map.update(collect_file_map(fragment, fragment_dir))
            manifest['designs'].update(fragment['designs'])

    # Check that all required files are present
    for file_path in file_map.keys():
        if not os.path.exists(file_path):
            raise Exception('Could not locate file {}'.format(file_path))

    # Update build IDs and write out the manifest
    update_manifest_stamps(manifest, stamp)
    os.makedirs(args.out, exist_ok=True)
    manifest_path = os.path.join(args.out, 'manifest.json')
    with open(manifest_path, 'w') as manifest_file:
        json.dump(manifest, manifest_file, indent=True)

    # Create the tarfile
    outfile = os.path.join(args.out, 'bitstream-cache.tar.gz')
    create_archive(outfile, manifest_path, file_map)


if __name__ == '__main__':
    sys.exit(main(sys.argv))
