#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import json
import os
import subprocess
import sys
import tempfile
from urllib.request import urlopen, urlretrieve

TOOLCHAIN_VERSION = 'latest'
RELEASES_URL_BASE = 'https://api.github.com/repos/lowRISC/lowrisc-toolchains/releases'
ASSET_PREFIX = "lowrisc-toolchain-gcc-rv32imc-"
ASSET_SUFFIX = ".tar.xz"
TARGET_DIR = '/tools/riscv'


def get_download_url(toolchain_version):
    if toolchain_version == 'latest':
        releases_url = '%s/%s' % (RELEASES_URL_BASE, toolchain_version)
    else:
        releases_url = '%s/tags/%s' % (RELEASES_URL_BASE, toolchain_version)
    with urlopen(releases_url) as f:
        info = json.loads(f.read().decode('utf-8'))
        return [
            a["browser_download_url"] for a in info["assets"]
            if (a["name"].startswith(ASSET_PREFIX) and
                a["name"].endswith(ASSET_SUFFIX))
        ][0]


def download(url):
    print("Downloading toolchain from %s" % (url, ))
    tmpfile = tempfile.mktemp()
    urlretrieve(url, tmpfile)
    return tmpfile


def install(archive_file, target_dir):
    os.makedirs(target_dir)

    cmd = [
        'tar', '-x', '-f', archive_file, '--strip-components=1', '-C',
        target_dir
    ]
    subprocess.run(cmd, check=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        '--target-dir',
        '-t',
        required=False,
        default=TARGET_DIR,
        help="Target directory (must not exist) (default: %(default)s)")
    parser.add_argument(
        '--release-version',
        '-r',
        required=False,
        default=TOOLCHAIN_VERSION,
        help="Toolchain version (default: %(default)s)")
    args = parser.parse_args()

    target_dir = args.target_dir
    toolchain_version = args.release_version

    if os.path.exists(args.target_dir):
        sys.exit('Target directory %s already exists. Delete it first it you '
                 'want to re-download the toolchain.' % (target_dir, ))

    download_url = get_download_url(toolchain_version)
    try:
        archive_file = download(download_url)
        install(archive_file, target_dir)
    finally:
        os.remove(archive_file)

    print('Toolchain downloaded and installed to %s' % (target_dir, ))


if __name__ == "__main__":
    main()
