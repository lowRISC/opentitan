#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import json
import logging as log
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from urllib.request import urlopen, urlretrieve

log.basicConfig(level=log.INFO, format="%(levelname)s: %(message)s")

ASSET_PREFIX = "lowrisc-toolchain-gcc-rv32imc-"
ASSET_SUFFIX = ".tar.xz"
RELEASES_URL_BASE = 'https://api.github.com/repos/lowRISC/lowrisc-toolchains/releases'

TARGET_DIR = '/tools/riscv'
TOOLCHAIN_VERSION = 'latest'


def get_available_toolchain_info(version):
    if version == 'latest':
        releases_url = '%s/%s' % (RELEASES_URL_BASE, version)
    else:
        releases_url = '%s/tags/%s' % (RELEASES_URL_BASE, version)

    with urlopen(releases_url) as f:
        release_info = json.loads(f.read().decode('utf-8'))

    download_url = [
        a["browser_download_url"] for a in release_info["assets"]
        if (a["name"].startswith(ASSET_PREFIX) and
            a["name"].endswith(ASSET_SUFFIX))
    ][0]

    return {'download_url': download_url, 'version': release_info['tag_name']}


def get_installed_toolchain_info(install_path):

    # Try new-style buildinfo.json first
    try:
        buildinfo = {}
        with open(str(install_path / 'buildinfo.json'), 'r') as f:
            buildinfo = json.loads(f.read())
        return buildinfo
    except Exception as e:
        # buildinfo.json might not exist in older builds
        log.info("Unable to parse buildinfo.json: %s", str(e))
        pass

    # If that wasn't successful, try old-style plaintext buildinfo
    version_re = r"(lowRISC toolchain version|Version):\s*\n?(?P<version>[^\n\s]+)"
    buildinfo_txt_path = install_path / 'buildinfo'
    try:
        with open(str(buildinfo_txt_path), 'r') as f:
            match = re.match(version_re, f.read(), re.M)
        if not match:
            log.warning("Unable extract version from %s",
                        str(buildinfo_txt_path))
            return None
        return {'version': match.group("version")}
    except Exception as e:
        log.error("Unable to read %s: %s", str(buildinfo_txt_path), str(e))
        return None


def download(url):
    log.info("Downloading toolchain from %s", url)
    tmpfile = tempfile.mkstemp()[1]
    urlretrieve(url, tmpfile)
    return Path(tmpfile)


def install(archive_file, target_dir):
    target_dir.mkdir(parents=True, exist_ok=True)

    cmd = [
        'tar', '-x', '-f', str(archive_file), '--strip-components=1', '-C',
        str(target_dir)
    ]
    subprocess.run(cmd, check=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--target-dir',
                        '-t',
                        required=False,
                        default=TARGET_DIR,
                        help="Target directory (default: %(default)s)")
    parser.add_argument('--release-version',
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
        help="Update to target version if needed (default: %(default)s)")
    args = parser.parse_args()

    target_dir = Path(args.target_dir)

    available_toolchain = get_available_toolchain_info(args.release_version)

    if args.update and target_dir.is_dir():
        installed_toolchain = get_installed_toolchain_info(target_dir)
        if installed_toolchain is None:
            sys.exit('Unable to extract current toolchain version. '
                     'Delete target directory and try again.')

        if available_toolchain['version'] == installed_toolchain['version']:
            log.info(
                'Toolchain version %s already installed at %s. Skipping '
                'install.', installed_toolchain['version'], str(target_dir))
            sys.exit(0)

        log.info(
            "Found installed toolchain version %s, updating to version %s.",
            installed_toolchain['version'], available_toolchain['version'])
    else:
        if target_dir.exists():
            sys.exit(
                'Target directory %s already exists. Delete it first, or use --update.'
                % str(target_dir))

    archive_file = None
    try:
        archive_file = download(available_toolchain['download_url'])

        if args.update and target_dir.exists():
            # We only reach this point if |target_dir| contained a toolchain
            # before, so removing it is reasonably safe.
            shutil.rmtree(target_dir)

        install(archive_file, target_dir)
    finally:
        if archive_file:
            archive_file.unlink()

    log.info('Toolchain version %s downloaded and installed to %s.',
             available_toolchain['version'], str(target_dir))


if __name__ == "__main__":
    main()
