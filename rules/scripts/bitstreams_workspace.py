#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import collections
import datetime
import io
import json
import logging
import os.path
import re
import subprocess
import sys
import tarfile
import time
import urllib.request
import xml.etree.ElementTree
from pathlib import Path
from typing import Dict, Set

import jsonschema

# The schema version used for legacy cache entries, JSON files missing a version
# entry, and entries that use a higher version of the schema than supported here
# (attempted in case there is forwards compatibility).
MANIFEST_SCHEMA_VERSION = 2

# Default location of the bitstreams cache.
CACHE_DIR = '~/.cache/opentitan-bitstreams'
# Default bucket URL.
BUCKET_URL = 'https://storage.googleapis.com/opentitan-bitstreams/'
# The xml document returned by the bucket is in this namespace.
XMLNS = {'': 'http://doc.s3.amazonaws.com/2006-03-01'}
# Manifest schema directory
MANIFESTS_DIR = os.path.dirname(__file__) if __file__ else os.path.dirname(sys.argv[0])
# Required designs
KNOWN_DESIGNS = {
    "chip_earlgrey_cw310": {
        "bitstream": "@//hw/bitstream/vivado:fpga_cw310_test_rom",
        "rom_mmi": "@//hw/bitstream/vivado:rom_mmi",
        "otp_mmi": "@//hw/bitstream/vivado:otp_mmi",
    },
    "chip_earlgrey_cw310_hyperdebug": {
        "bitstream": "@//hw/bitstream/vivado:fpga_cw310_test_rom_hyp",
        "rom_mmi": "@//hw/bitstream/vivado:rom_mmi_hyp",
        "otp_mmi": "@//hw/bitstream/vivado:otp_mmi_hyp",
    },
    "chip_earlgrey_cw340": {
        "bitstream": "@//hw/bitstream/vivado:fpga_cw340_test_rom",
        "rom_mmi": "@//hw/bitstream/vivado:fpga_cw340_rom_mmi",
        "otp_mmi": "@//hw/bitstream/vivado:fpga_cw340_otp_mmi",
    },
}

parser = argparse.ArgumentParser(
    description='Bitstream Downloader & Cache manager')
parser.add_argument('--cache', default=CACHE_DIR, help='Cache directory name')
parser.add_argument('--create-symlink', default=True,
                    action=argparse.BooleanOptionalAction,
                    help='Create symlink to cache directory')
parser.add_argument('--latest-update',
                    default='latest.txt',
                    help='Last time the cache was updated')
parser.add_argument('--bucket-url', default=BUCKET_URL, help='GCP Bucket URL')
parser.add_argument('--build-file',
                    default='BUILD.bazel',
                    help='Name of the generated BUILD file')
parser.add_argument('--list',
                    default=False,
                    action=argparse.BooleanOptionalAction,
                    help='List GCP Bucket contents')
parser.add_argument('--offline',
                    default=False,
                    action=argparse.BooleanOptionalAction,
                    help='Operating in an offline environment')
parser.add_argument('--refresh',
                    default=False,
                    action=argparse.BooleanOptionalAction,
                    help='Force a refresh')
parser.add_argument('--refresh-time',
                    default=300,
                    type=int,
                    help='How often to check for new bitstreams')
parser.add_argument('--repo',
                    default='',
                    help="Location of the source git repo")
parser.add_argument(
    'bitstream',
    default='HEAD',
    nargs='?',
    help='Bitstream to retrieve: "latest" or git commit identifier')


class BitstreamCache(object):

    def __init__(self, bucket_url, cachedir, latest_update, offline=False):
        """Initialize the Bitstream Cache Manager."""
        if bucket_url[-1] != '/':
            bucket_url += '/'
        self.bucket_url = bucket_url
        cachedir = os.path.abspath(os.path.expanduser(cachedir))
        self.cachedir = os.path.join(cachedir, 'cache')
        latest_update = os.path.join(cachedir,
                                     os.path.expanduser(latest_update))
        self.latest_update = latest_update
        self.offline = offline
        self.available = {}

    @staticmethod
    def MakeWithDefaults() -> 'BitstreamCache':
        """Create a BitstreamCache with default parameters."""
        args = parser.parse_args([])
        cache = BitstreamCache(args.bucket_url, args.cache, args.latest_update,
                               args.offline)
        return cache

    def InitRepository(self, create_symlink: bool):
        """Create the cache directory and symlink it into the bazel repository dir."""
        os.makedirs(self.cachedir, exist_ok=True)
        if create_symlink:
            os.symlink(self.cachedir, 'cache')

    def Touch(self, key):
        """Set the latest known bitstream.

        Args:
            key: str; The git hash of the latest bitstream.
        """
        with open(self.latest_update, 'wt') as f:
            print(key, file=f)

    def NeedRefresh(self, interval):
        """Determine if the cache needs a refresh.

        Args:
            interval: int; Desired interval between refresh.
        Returns:
            bool: whether a refresh is needed.
        """
        try:
            st = os.stat(self.latest_update)
            return time.time() - st.st_mtime > interval
        except FileNotFoundError:
            return True

    def Get(self, file, **kwargs):
        """Perform an HTTP GET from the GCP bitstream bucket.

        Args:
            file: Filename in the bucket to retrieve.
            kwargs: Any query parameters to include in the request
        Returns:
            bytes
        """
        url_parts = urllib.parse.urlparse(self.bucket_url)
        path = urllib.parse.quote(url_parts.path + file)
        query = urllib.parse.urlencode(kwargs)
        url = url_parts._replace(path=path, query=query).geturl()

        response = urllib.request.urlopen(url)
        return response.read()

    def GetBitstreamsAvailable(self, refresh, load_latest_update=True):
        """Inventory which bitstreams are available.

        Args:
            refresh: bool; whether to refresh from the network.
            load_latest_update: bool; whether to load the latest_update file
        """
        if not refresh:
            for (_, dirnames, _) in os.walk('cache'):
                for d in dirnames:
                    self.available[d] = 'local'
            if load_latest_update:
                try:
                    with open(self.latest_update, 'rt') as f:
                        self.available['latest'] = f.read().strip()
                except FileNotFoundError:
                    if self.offline:
                        logging.error(
                            'Must pre-initialize bitstream cache in offline mode.')
                    else:
                        logging.error(
                            f'Bitstream cache missing {self.latest_update}.')
                    sys.exit(1)
            return

        # Fetching the list of all entries in the cache may require multiple
        # requests since GCP will paginate long reponses. Markers are used to
        # fetch subsequent pages.
        # See the GCP docs and the XML REST API reference for more details:
        # https://cloud.google.com/storage/docs/paginate-results
        # https://cloud.google.com/storage/docs/xml-api/get-bucket-list
        marker = ''
        while True:
            document = self.Get('', marker=marker).decode('utf-8')
            et = xml.etree.ElementTree.fromstring(document)
            for content in et.findall('Contents', XMLNS):
                for key in content.findall('Key', XMLNS):
                    m = re.search(r'bitstream-([0-9A-Fa-f]+).tar.gz', key.text)
                    if m:
                        self.available[m.group(1)] = key.text
            # Handle any pagination
            is_truncated_elt = et.find('IsTruncated', XMLNS)
            if (is_truncated_elt is not None) and \
               (is_truncated_elt.text == 'true'):
                marker = et.find('NextMarker', XMLNS).text
            else:
                break

        latest = self.Get('master/latest.txt').decode('utf-8').split('\n')
        self.available['latest'] = latest[1]

    def GetClosest(self, repodir, key):
        """Get the best match for a bitstream (exact or next older commit).

        Args:
            repodir: path; Path to the repo from which bitstreams are built.
            key: str; A git hash or identifier of the desired bitstream.
        Returns:
            str or None: git hash of the closest bitstream.
        """
        if key in self.available:
            return key
        commits = []
        lines = subprocess.check_output(
            ['git', 'log', '--oneline', '--no-abbrev-commit', key],
            universal_newlines=True,
            cwd=repodir)
        for line in lines.split('\n'):
            commits.append(line.split(' ')[0])

        for commit in commits:
            if commit in self.available:
                return commit
        return None

    def _GetFromLocal(self, key):
        """Get the bitstream files from the local filesystem.

        Args:
            key: str; A git hash or the string 'latest'.
        Returns:
            list[str]: The requested bitstream files or empty list.
        """
        if key == 'latest':
            key = self.available['latest']
        files = []
        local_dir = os.path.join('cache', key)
        for (dirname, _, filenames) in os.walk(local_dir):
            files.extend(os.path.join(dirname, f) for f in filenames)
        return files

    def _GetFromRemote(self, key):
        """Get the bitstream files from GCP bucket.
        The retrieved files are extracted into the cache directory.

        Args:
            key: str; A git hash or the string 'latest'.
        """
        if self.offline:
            return
        if key == 'latest':
            latest = self.available['latest']
            key = latest
        else:
            latest = None

        remote_filename = self.available[key]
        local_dir = os.path.join(self.cachedir, key)
        archive = io.BytesIO(self.Get(remote_filename))
        tar = tarfile.open(fileobj=archive, mode='r|*')
        tar.extractall(local_dir)
        if latest:
            self.Touch(latest)
        if not os.path.exists(self.latest_update):
            self.Touch(key)

    def _GenerateLegacyManifest(self, key: str, files: [str]) -> Dict:
        """Generate a manifest for old cache entries without them.

        Args:
            key: A git hash
            files: A list of file paths
        Returns:
            A dictionary mapping file paths to manifest entries
        """
        legacy_files = {
            "chip_earlgrey_cw310": {
                "build_id": key,
                "bitstream": {
                    "file": "lowrisc_systems_chip_earlgrey_cw310_0.1.bit.orig",
                    "build_target": "//hw/bitstream/vivado:fpga_cw310",
                },
                "memory_map_info": {
                    "otp": {
                        "file": "otp.mmi",
                        "build_target": "//hw/bitstream/vivado:fpga_cw310",
                    },
                    "rom": {
                        "file": "rom.mmi",
                        "build_target": "//hw/bitstream/vivado:fpga_cw310",
                    },
                },
            },
            "chip_earlgrey_cw310_hyperdebug": {
                "build_id": key,
                "bitstream": {
                    "file": "chip_earlgrey_cw310_hyperdebug/"
                            "lowrisc_systems_chip_earlgrey_cw310_hyperdebug_0.1.bit",
                    "build_target": "//hw/bitstream/vivado:fpga_cw310_hyperdebug",
                },
                "memory_map_info": {
                    "otp": {
                        "file": "chip_earlgrey_cw310_hyperdebug/otp.mmi",
                        "build_target": "//hw/bitstream/vivado:fpga_cw310_hyperdebug",
                    },
                    "rom": {
                        "file": "chip_earlgrey_cw310_hyperdebug/rom.mmi",
                        "build_target": "//hw/bitstream/vivado:fpga_cw310_hyperdebug",
                    },
                },
            },
        }
        designs = collections.defaultdict(dict)

        for design, metadata in legacy_files.items():
            design_is_present = True
            required_files = [metadata["bitstream"]["file"]]
            for mmi in metadata["memory_map_info"].values():
                required_files.append(mmi["file"])
            for required_file in required_files:
                if os.path.join("cache", key, required_file) not in files:
                    design_is_present = False
                    break
            if design_is_present:
                designs[design] = metadata

        manifest = {"schema_version": MANIFEST_SCHEMA_VERSION,
                    "designs": designs}
        return manifest

    def GetFromCache(self, key: str) -> (Dict, Path):
        """Get the requested bitstream files manifest.

        Args:
            key: A git hash or the string 'latest'.
        Returns:
            A dictionary that represents a bitstream cache manifest.
        """
        files = self._GetFromLocal(key)
        if not files:
            self._GetFromRemote(key)
            files = self._GetFromLocal(key)

        manifest_path = os.path.join("cache", key, "manifest.json")
        if manifest_path not in files:
            logging.warning("No manifest found."
                            " Attempting to generate manifest from legacy file"
                            " paths.")
            return (self._GenerateLegacyManifest(key, files), None)

        with open(manifest_path, "r") as manifest_file:
            manifest = json.load(manifest_file)

        if "schema_version" not in manifest:
            logging.error("schema is missing a version number."
                          " Generating legacy manifest instead...")
            return (self._GenerateLegacyManifest(key, files), None)

        return (manifest, manifest_path)

    @staticmethod
    def _GetDateTimeStr():
        return datetime.datetime.now().isoformat()

    @staticmethod
    def _WriteSubstituteManifest(contents: Dict, path: Path):
        with open(path, "w") as manifest_file:
            json.dump(contents, manifest_file, indent=True)

    def _ConstructBazelString(self, build_file: Path, key: str) -> str:
        # If `key` passed in is "latest", this updates the `key` to be the hash
        # that "latest" points to.
        if key == 'latest':
            key = self.available['latest']

        (manifest, manifest_path) = self.GetFromCache(key)

        # Schema version 1 was never used and is not valid
        if manifest["schema_version"] <= 1:
            msg_template = "Invalid schema_version {} found in manifest"
            raise Exception(msg_template.format(manifest["schema_version"]))

        designs = collections.defaultdict(dict)
        if manifest["schema_version"] > MANIFEST_SCHEMA_VERSION:
            logging.warning("Warning: Manifest is newer than available schemas")
            logging.warning("Will try parsing an available schema with highest version")
            manifest["schema_version"] = MANIFEST_SCHEMA_VERSION

        if manifest["schema_version"] == 2:
            schema_path = os.path.join(MANIFESTS_DIR, "bitstreams_manifest.schema.json")
            with open(schema_path) as schema_file:
                schema = json.load(schema_file)
            jsonschema.validate(manifest, schema)
            for design_name, metadata in manifest["designs"].items():
                design = collections.defaultdict(dict)
                design["bitstream"] = metadata["bitstream"]["file"]
                for mmi_id, mmi_entry in metadata["memory_map_info"].items():
                    design[mmi_id + "_mmi"] = mmi_entry["file"]
                designs[design_name] = design

        bazel_lines = [
            '# This file was autogenerated. Do not edit!',
            '# Built at {}.'.format(BitstreamCache._GetDateTimeStr()),
            '# Configured for bitstream: {}'.format(key),
            '',
            'package(default_visibility = ["//visibility:public"])',
            '',
            'exports_files(glob(["cache/**"]))',
            '',
        ]

        def filegroup_lines(name, src):
            return [
                'filegroup(',
                '    name = "{}",'.format(name),
                '    srcs = ["{}"],'.format(src),
                ')',
                '',
            ]

        def alias_lines(name, target):
            return [
                'alias(',
                '    name = "{}",'.format(name),
                '    actual = "{}",'.format(target),
                ')',
                '',
            ]

        used_target_names: Set[str] = set()

        cache_base_dir = os.path.join("cache", key)
        for design_name in sorted(designs.keys()):
            design = designs[design_name]
            if "bitstream" not in design:
                error_msg_lines = [
                    "Could not find the bitstreams to generate a BUILD file:" +
                    repr(build_file),
                    "in design " + design_name + ":" + repr(design),
                    "using key:" + repr(key),
                ]
                logging.error('\n'.join(error_msg_lines))
                sys.exit(1)

            for target in sorted(design.keys()):
                target_file = os.path.join(cache_base_dir, design[target])
                target_name = "_".join([design_name, target])

                if target_name in used_target_names:
                    logging.error(
                        "Target name {} for file {} would collide with another target"
                        .format(repr(target_name), repr(target_file)))
                    sys.exit(1)
                used_target_names.add(target_name)

                bazel_lines += filegroup_lines(target_name, target_file)

        if manifest_path is None:
            # Write substitute manifest if none came with the cache entry.
            manifest_path = os.path.join(cache_base_dir,
                                         "substitute_manifest.json")
            abs_manifest_path = os.path.join(self.cachedir,
                                             "substitute_manifest.json")
            self._WriteSubstituteManifest(manifest, abs_manifest_path)

        bazel_lines += filegroup_lines("manifest", manifest_path)

        for design_name in sorted(KNOWN_DESIGNS.keys()):
            if design_name not in designs:
                for target_ext, alias in KNOWN_DESIGNS[design_name].items():
                    target = "{}_{}".format(design_name, target_ext)
                    bazel_lines += alias_lines(target, alias)

        return '\n'.join(bazel_lines)

    def WriteBazelFiles(self, build_file: Path, key: str) -> str:
        """Write a BUILD file for the requested bitstream files.

        Args:
            build: path; Filename of the BUILD file to write.
            key: str; A git hash or the string 'latest'.
        Returns:
            Either `key` or the corresponding commit hash if `key` is 'latest'.
        """
        with open(build_file, 'wt') as f:
            f.write(self._ConstructBazelString(build_file, key))

        if key != 'latest':
            return key
        return self.available[key]


def main(argv):
    # The user can override some basic behaviors with the BITSTREAM
    # environment variable.
    env = os.environ.get('BITSTREAM')
    if env:
        argv.extend(env.split(' '))
    args = parser.parse_args(args=argv[1:])
    desired_bitstream = args.bitstream

    # We need to know the location of the main git repo, since this script
    # will have its CWD in a bazel-managed 'external' directory.
    # If not provided, we assume this script itself is located in the main
    # git repository.
    if args.repo:
        if os.path.isdir(args.repo):
            repo = args.repo
        else:
            repo = os.path.dirname(args.repo)
    else:
        repo = os.path.dirname(argv[0])

    cache = BitstreamCache(args.bucket_url, args.cache, args.latest_update,
                           args.offline)
    cache.InitRepository(args.create_symlink)

    # Do we need a refresh?
    need_refresh = (args.refresh or desired_bitstream != 'latest' or
                    cache.NeedRefresh(args.refresh_time))
    # Do we need to load the latest_update file?
    load_latest_update = (desired_bitstream == 'latest')
    cache.GetBitstreamsAvailable(need_refresh and not args.offline,
                                 load_latest_update)

    # If commanded to print bitstream availability, do so.
    if args.list:
        for k, v in cache.available.items():
            print('{}: {}'.format(k, v))

    # If we aren't getting the latest bitstream, resolve the hash to the closest
    # bitstream we can find.
    if desired_bitstream != 'latest':
        closest_bitstream = cache.GetClosest(repo, desired_bitstream)
        if closest_bitstream is None:
            logging.error('Cannot find a bitstream close to {}'.format(
                desired_bitstream))
            return 1
        if closest_bitstream != desired_bitstream:
            logging.warning('Closest bitstream to {} is {}.'.format(
                desired_bitstream, closest_bitstream))
            desired_bitstream = closest_bitstream

    # Write a build file which allows tests to reference the bitstreams with
    # the labels:
    #   @bitstreams//:{design}_bitstream
    configured_bitream = cache.WriteBazelFiles(args.build_file,
                                               desired_bitstream)
    if desired_bitstream != 'latest' and configured_bitream != desired_bitstream:
        logging.error(
            'Configured bitstream {} does not match desired bitstream {}.'.
            format(configured_bitream, desired_bitstream))
        return 1
    logging.info(
        'Configured latest bitstream as {}.'.format(configured_bitream))

    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
