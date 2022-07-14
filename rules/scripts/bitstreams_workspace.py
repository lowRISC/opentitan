#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import datetime
import io
import logging
import os.path
import re
import subprocess
import sys
import tarfile
import time
import urllib.request
import xml.etree.ElementTree

# Default location of the bitstreams cache.
CACHE_DIR = '~/.cache/opentitan-bitstreams'
# Default bucket URL.
BUCKET_URL = 'https://storage.googleapis.com/opentitan-bitstreams/'
# The xml document returned by the bucket is in this namespace.
XMLNS = {'': 'http://doc.s3.amazonaws.com/2006-03-01'}

parser = argparse.ArgumentParser(
    description='Bitstream Downloader & Cache manager')
parser.add_argument('--cache', default=CACHE_DIR, help='Cache directory name')
parser.add_argument('--latest-update',
                    default='latest.txt',
                    help='Last time the cache was updated')
parser.add_argument('--bucket-url', default=BUCKET_URL, help='GCP Bucket URL')
parser.add_argument('--build-file',
                    default='BUILD.bazel',
                    help='Name of the genrated BUILD file')
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
    default='latest',
    nargs='?',
    help='Bitstream to retrieve: "latest" or git commit identifier')


class BitstreamCache(object):

    def __init__(self, bucket_url, cachedir, latest_update, offline=False):
        """Initialize the Bitstream Cache Manager."""
        if bucket_url[-1] != '/':
            bucket_url += '/'
        self.bucket_url = bucket_url
        cachedir = os.path.expanduser(cachedir)
        self.cachedir = os.path.join(cachedir, 'cache')
        latest_update = os.path.join(cachedir,
                                     os.path.expanduser(latest_update))
        self.latest_update = latest_update
        self.offline = offline
        self.available = {}

    def InitRepository(self):
        """Create the cache directory and symlink it into the bazel repository dir."""
        os.makedirs(self.cachedir, exist_ok=True)
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

    def Get(self, file):
        """Perform an HTTP GET from the GCP bitstream bucket.

        Args:
            file: Filename in the bucket to retrieve.
        Returns:
            bytes
        """
        response = urllib.request.urlopen(self.bucket_url + file)
        return response.read()

    def GetBitstreamsAvailable(self, refresh):
        """Inventory which bitstreams are available.

        Args:
            refresh: bool; whether to refresh from the network.
        """
        if not refresh:
            for (_, dirnames, _) in os.walk('cache'):
                for d in dirnames:
                    self.available[d] = 'local'
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
        document = self.Get('').decode('utf-8')
        et = xml.etree.ElementTree.fromstring(document)
        for content in et.findall('Contents', XMLNS):
            for key in content.findall('Key', XMLNS):
                m = re.search(r'bitstream-([0-9A-Fa-f]+).tar.gz', key.text)
                if m:
                    self.available[m.group(1)] = key.text
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

    def GetFromCache(self, key):
        """Get the requested bitstream files.

        Args:
            key: str; A git hash or the string 'latest'.
        Returns:
            dict[str:str]: A dictionary mapping the bitstream types to
                           their target files.
        """
        files = self._GetFromLocal(key)
        if not files:
            self._GetFromRemote(key)
            files = self._GetFromLocal(key)
        return {os.path.splitext(f)[1][1:]: f for f in files}

    @staticmethod
    def _GetDateTimeStr():
        return datetime.datetime.now().isoformat()

    def WriteBuildFile(self, build, key):
        """Write a BUILD file for the requested bitstream files.

        Args:
            build: path; Filename of the BUILD file to write.
            key: str; A git hash or the string 'latest'.
        """
        param = self.GetFromCache(key)
        param['datetime'] = BitstreamCache._GetDateTimeStr()
        param['key'] = key

        if 'orig' not in param or 'splice' not in param:
            logging.error(
                """Could not find the bitstreams to generate a BUILD file:{}
in params:{}
using key:{}""".format(build, param, key))
            sys.exit(1)
        with open(build, 'wt') as f:
            f.write("""# This file was autogenerated. Do not edit!
# Built at {datetime}.
# Configured for bitstream: {key}

package(default_visibility = ["//visibility:public"])

exports_files(glob(["cache/**"]))

filegroup(
    name = "bitstream_test_rom",
    srcs = ["{orig}"],
)

filegroup(
    name = "bitstream_mask_rom",
    srcs = ["{splice}"],
)
""".format(**param))

        if key == 'latest':
            key = self.available[key]
        return key


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
    cache.InitRepository()

    # Do we need a refresh?
    need_refresh = (args.refresh or desired_bitstream != 'latest' or
                    cache.NeedRefresh(args.refresh_time))
    cache.GetBitstreamsAvailable(need_refresh and not args.offline)

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
    #   @bitstreams//:bitstream_test_rom
    #   @bitstreams//:bitstream_mask_rom
    configured_bitream = cache.WriteBuildFile(args.build_file,
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
