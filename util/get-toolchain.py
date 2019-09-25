#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import shutil
import sys
import tempfile
import time
from urllib.request import urlopen, urlretrieve

ASSET_PREFIX = "lowrisc-toolchain-gcc-rv32imc-"
ASSET_SUFFIX = ".tar.xz"
BUILDINFO_FILENAME = "buildinfo"
RELEASES_URL_BASE = 'https://api.github.com/repos/lowRISC/lowrisc-toolchains/releases'
TARGET_DIR = '/tools/riscv'
TOOLCHAIN_VERSION = 'latest'


def prompt_yes_no(msg):
    while True:
        print(msg, end=" ")
        response = input().lower()
        if response in ('yes', 'y'):
            return True
        elif response in ('no', 'n'):
            return False
        else:
            print('Invalid response. Valid options are "yes" or "no"')


def get_release_info(toolchain_version):
    if toolchain_version == 'latest':
        releases_url = '%s/%s' % (RELEASES_URL_BASE, toolchain_version)
    else:
        releases_url = '%s/tags/%s' % (RELEASES_URL_BASE, toolchain_version)
    with urlopen(releases_url) as f:
        return json.loads(f.read().decode('utf-8'))


def get_download_url(release_info):
    return [
        a["browser_download_url"] for a in release_info["assets"]
        if (a["name"].startswith(ASSET_PREFIX) and
            a["name"].endswith(ASSET_SUFFIX))
    ][0]


def get_release_tag(release_info):
    return release_info["tag_name"]


def get_release_tag_from_file(buildinfo_file):
    """Extracts version tag from buildinfo file.

    Args:
        buildinfo_file: Path to buildinfo_file.
    Returns:
        Release tag string if available, otherwise None.
    """
    with open(buildinfo_file, 'r') as f:
        match = re.match(r"Version:\n(?P<version>\d+(-\d+)?)", f.read(), re.M)
    if not match:
        return None
    return match.group("version")


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
    parser.add_argument(
        '--update',
        '-u',
        required=False,
        default=False,
        action='store_true',
        help="Set to update to target version if needed (default: %(default)s)")
    parser.add_argument(
        '--force',
        '-f',
        required=False,
        default=False,
        action='store_true',
        help="Set to skip directory erase prompt when --update is set "
            "(default: %(default)s)")
    args = parser.parse_args()

    target_dir = args.target_dir
    toolchain_version = args.release_version

    if not args.update and os.path.exists(args.target_dir):
        sys.exit('Target directory %s already exists. Delete it first '
             'it you want to re-download the toolchain.' % (target_dir, ))

    release_info = get_release_info(toolchain_version)

    if args.update and os.path.exists(args.target_dir):
        buildinfo_file = str(Path(target_dir) / BUILDINFO_FILENAME)
        if not os.path.exists(buildinfo_file):
            sys.exit('Unable to find buildinfo file at %s. Delete target '
                'directory and try again.' % buildinfo_file)
        current_release_tag = get_release_tag_from_file(buildinfo_file)
        if not current_release_tag:
            sys.exit('Unable to extract current toolchain version from %s. '
                'Delete target directory and try again.' % buildinfo_file)
        if get_release_tag(release_info) == current_release_tag:
            print('Toolchain version %s already installed at %s. Skipping '
                'install.' % (current_release_tag, target_dir))
            return

    download_url = get_download_url(release_info)
    try:
        archive_file = download(download_url)
        if args.update and os.path.exists(args.target_dir):
            # Warn the user before deleting the target directory.
            warning_msg = 'WARNING: Removing directory: %s.' % target_dir
            if not args.force:
                if not prompt_yes_no(warning_msg + ' Continue [yes/no]:'):
                    sys.exit('Aborting update.')
            else:
                print(warning_msg)
            shutil.rmtree(target_dir)
        install(archive_file, target_dir)
    finally:
        os.remove(archive_file)

    print('Toolchain downloaded and installed to %s' % (target_dir, ))


if __name__ == "__main__":
    main()
