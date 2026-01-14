#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import json
import logging as log
import os
import re
import shutil
import subprocess
import sys
import time
import tempfile
from pathlib import Path
from urllib3 import PoolManager, Retry
from urllib3.exceptions import HTTPError, MaxRetryError

log.basicConfig(level=log.INFO, format="%(levelname)s: %(message)s")
http = PoolManager()

# the keys in this dictionary specify valid toolchain kinds
ASSET_PREFIXES = {
    # kind : prefix,
    "combined": "lowrisc-toolchain-rv32imcb-",
    "gcc-only": "lowrisc-toolchain-gcc-rv32imcb-",
}
ASSET_SUFFIX = ".tar.xz"
RELEASES_URL_BASE = 'https://api.github.com/repos/lowRISC/lowrisc-toolchains/releases'

INSTALL_DIR = '/tools/riscv'
TOOLCHAIN_VERSION = 'latest'
TOOLCHAIN_KIND = 'combined'
TOOLCHAIN_ARCHS = ["x86_64", "aarch64"]

FILE_PATTERNS_TO_REWRITE = [
    "riscv32-unknown-elf-*.cmake",
    "meson-riscv32-unknown-elf-*.txt",
]


def get_available_toolchain_info(version, kind, arch):
    assert kind in ASSET_PREFIXES
    assert arch in TOOLCHAIN_ARCHS

    if version == 'latest':
        releases_url = '%s/%s' % (RELEASES_URL_BASE, version)
    else:
        releases_url = '%s/tags/%s' % (RELEASES_URL_BASE, version)

    try:
        retry = Retry(connect=4, backoff_factor=1,
                      status_forcelist=[403, 408, 429, 500, 502, 503, 504])
        response = http.request("GET", releases_url, retries=retry)
        if response.status != 200:
            log.error("Request to %s failed with status code %d", releases_url, response.status)
            sys.exit(1)
        release_info = json.loads(response.data.decode("utf-8"))
    except (HTTPError, MaxRetryError) as e:
        log.error("Request to %s failed after retries: %s", releases_url, str(e))
        sys.exit(1)

    # Search for the desired asset. Newer releases have builds for different architectures whereas
    # older releases don't specify an architecture. To maintain compatibility we first search for
    # an architecture specific asset. If none is found, we repeat the search without the
    # architecture flag.
    for name in [ASSET_PREFIXES[kind] + arch, ASSET_PREFIXES[kind]]:
        for asset in release_info["assets"]:
            if (asset["name"].startswith(name) and
                    asset["name"].endswith(ASSET_SUFFIX)):
                return {
                    'download_url': asset['browser_download_url'],
                    'name': asset['name'],
                    'version': release_info['tag_name'],
                    'kind': kind
                }

    # No matching asset found for the toolchain kind requested
    log.error("No available downloads found for %s toolchain version: %s for architecture %s",
              kind, release_info['tag_name'], arch)
    raise SystemExit(1)


def get_installed_toolchain_info(unpack_dir):

    # Try new-style buildinfo.json first
    try:
        buildinfo = {}
        with open(str(unpack_dir / 'buildinfo.json'), 'r') as f:
            buildinfo = json.loads(f.read())

        # Toolchains before 20200602-4 contained a `buildinfo.json` without a
        # 'kind' field. Setting it to 'unknown' will ensure we never skip
        # updating because we think it's the same as the existing toolchain.
        if 'kind' not in buildinfo:
            buildinfo['kind'] = 'unknown'

        return buildinfo
    except Exception as e:
        # buildinfo.json might not exist in older builds
        log.info("Unable to parse buildinfo.json: %s", str(e))
        pass

    # If that wasn't successful, try old-style plaintext buildinfo
    version_re = r"(lowRISC toolchain version|Version):\s*\n?(?P<version>[^\n\s]+)"
    buildinfo_txt_path = unpack_dir / 'buildinfo'
    try:
        with open(str(buildinfo_txt_path), 'r') as f:
            match = re.match(version_re, f.read(), re.M)
        if not match:
            log.warning("Unable extract version from %s",
                        str(buildinfo_txt_path))
            return None
        return {'version': match.group("version"), 'kind': 'unknown'}
    except Exception as e:
        log.error("Unable to read %s: %s", str(buildinfo_txt_path), str(e))
        return None


def download(url, max_attempts=5):
    log.info("Downloading toolchain from %s", url)
    tmpfile = tempfile.mkstemp(suffix=".tar.xz")[1]
    attempt = 0
    while attempt < max_attempts:
        try:
            # Do not use urllib3 retry logic as we also need to handle stream
            # disruption failures after an initial successful HTTP status
            with http.request("GET", url, preload_content=False) as response:
                print(response.__dict__)
                if response.status != 200:
                    raise Exception(f"Unexpected status code: {response.status}")
                with open(tmpfile, 'wb') as target_file:
                    for part in response.stream(1024):
                        target_file.write(part)
                response.release_conn()
            break
        except Exception:
            # If we get a failure (initial HTTP or mid-stream), retry by
            # restarting the entire operation.
            attempt += 1
            log.exception(f"Toolchain download attempt {attempt} failed")
            if os.path.exists(tmpfile):
                os.remove(tmpfile)
            if attempt >= max_attempts:
                log.exception(f"Toolchain download failed after {attempt} retries.")
                sys.exit(1)
            else:
                time.sleep(2 ** (attempt - 1))
    log.info("Download complete")
    return Path(tmpfile)


def install(archive_file, unpack_dir):
    unpack_dir.mkdir(parents=True, exist_ok=True)

    cmd = [
        'tar',
        '-x',
        '-f',
        str(archive_file),
        '--strip-components=1',
        '-C',
        str(unpack_dir),
    ]
    subprocess.run(cmd, check=True)


def postinstall_rewrite_configs(unpack_dir, install_dir):
    """Rewrites the toolchain configuration files to point to install_dir.

    'unpack_dir' is where the toolchain is unpacked by this script.
    'install_dir' is where the toolchain is eventually invoked from. Typically,
    these are the same, unless a staged installation is being performed by
    supplying both, --install-dir and --dest-dir switches. Regardless, if the
    'install_dir' is different from the default, the config files need to be
    updated to reflect the correct paths.
    """
    if str(install_dir) == INSTALL_DIR:
        return

    for file_pattern in FILE_PATTERNS_TO_REWRITE:
        for config_file_path in unpack_dir.glob(file_pattern):
            # Rewrite INSTALL_DIR to the requested target dir.
            log.info("Updating toolchain paths in %s", str(config_file_path))
            with open(str(config_file_path)) as f:
                original = f.read()
            with open(str(config_file_path), "w") as f:
                f.write(original.replace(INSTALL_DIR, str(install_dir)))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--install-dir',
                        '-i',
                        required=False,
                        default=INSTALL_DIR,
                        help="Installation directory (default: %(default)s)")
    parser.add_argument('--dest-dir',
                        '-d',
                        required=False,
                        help="""Destination directory if performing a staged
                        installation. This is the staging directory where the
                        toolchain is unpacked.""")
    parser.add_argument('--download-only',
                        '-D',
                        required=False,
                        default=False,
                        action='store_true',
                        help="""Just download the archive, don't
                        unpack or install it.  Will be stored in
                        --dest-dir if specified or --install-dir
                        otherwise""")
    parser.add_argument('--release-version',
                        '-r',
                        required=False,
                        default=TOOLCHAIN_VERSION,
                        help="Toolchain version (default: %(default)s)")
    parser.add_argument('--latest-available-version',
                        '-l',
                        required=False,
                        default=False,
                        action='store_true',
                        help="Return the latest available toolchain version.")
    parser.add_argument('--kind',
                        required=False,
                        default=TOOLCHAIN_KIND,
                        choices=ASSET_PREFIXES.keys(),
                        help="Toolchain kind (default: %(default)s)")
    parser.add_argument('--arch',
                        required=False,
                        default=TOOLCHAIN_ARCHS[0],
                        choices=TOOLCHAIN_ARCHS,
                        help="Specify the toolchain architecture (default: %(default)s)")
    parser.add_argument(
        '--update',
        '-u',
        required=False,
        default=False,
        action='store_true',
        help="Update to target version if needed (default: %(default)s)")
    args = parser.parse_args()

    available_toolchain = get_available_toolchain_info(args.release_version,
                                                       args.kind,
                                                       args.arch)

    if args.download_only and args.update:
        print('specify only one of --download-only and --update')
        sys.exit(1)

    if args.latest_available_version:
        print(available_toolchain['version'])
        sys.exit(0)

    log.info("Found available %s toolchain version %s, %s",
             available_toolchain['kind'], available_toolchain['version'],
             available_toolchain['name'])

    install_dir = Path(args.install_dir)
    if args.dest_dir is None:
        unpack_dir = install_dir
    else:
        unpack_dir = Path(args.dest_dir)

    if args.update and unpack_dir.is_dir():
        installed_toolchain = get_installed_toolchain_info(unpack_dir)
        if installed_toolchain is None:
            sys.exit('Unable to extract current toolchain version. '
                     'Delete target directory %s and try again.' %
                     str(unpack_dir))

        version_matches = available_toolchain[
            'version'] == installed_toolchain['version']
        kind_matches = available_toolchain['kind'] == installed_toolchain[
            'kind']

        if installed_toolchain[
                'kind'] != 'unknown' and version_matches and kind_matches:
            log.info(
                'Downloaded %s toolchain is version %s, '
                'same as the %s toolchain installed at %s (version %s).',
                available_toolchain['kind'], available_toolchain['version'],
                installed_toolchain['kind'], installed_toolchain['version'],
                str(unpack_dir))
            log.warning("Skipping install.")
            sys.exit(0)

        log.info(
            "Found installed %s toolchain version %s, updating to %s toolchain "
            "version %s.", installed_toolchain['kind'],
            installed_toolchain['version'], available_toolchain['kind'],
            available_toolchain['version'])
    else:
        if unpack_dir.exists():
            sys.exit('Target directory %s already exists. '
                     'Delete it first, or use --update.' % str(unpack_dir))

    archive_file = None
    try:
        archive_file = download(available_toolchain['download_url'])
        if args.download_only:
            unpack_dir.mkdir(parents=True, exist_ok=True)
            shutil.move(str(archive_file), str(unpack_dir))
            log.info('Downloaded %s toolchain archive version %s to %s.',
                     available_toolchain['kind'],
                     available_toolchain['version'], str(unpack_dir))
            return

        if args.update and unpack_dir.exists():
            # We only reach this point if |unpack_dir| contained a toolchain
            # before, so removing it is reasonably safe.
            shutil.rmtree(str(unpack_dir))

        install(archive_file, unpack_dir)
        postinstall_rewrite_configs(unpack_dir.resolve(),
                                    install_dir.resolve())
    finally:
        if archive_file and not args.download_only:
            archive_file.unlink()

    log.info('Installed %s toolchain version %s to %s.',
             available_toolchain['kind'], available_toolchain['version'],
             str(unpack_dir))


if __name__ == "__main__":
    main()
