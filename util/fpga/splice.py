#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

###########################################################################
# Bitstream splice cache.
#
# Ideally, we'd rely on bazel to splice and cache bitstreams for us,
# but:
# - For test specification, it is more convenient to configure the
#   test parameters with particular ROMs and OTP rather then to have
#   explicit splice rules.  This is doubly true when one considers
#   multiple exec_envs with different base bitstreams: its easier
#   to specify the required ROM/OTP than to have a collection of splicing
#   rules per exec_env.
# - Bazel's action cache remembers the commandline that was used to create
#   a given result.  Even if the input files between two actions and the
#   program executed are identical, the output filenames are not, and thus
#   the command-line is not identical.  This means if one specifies an
#   identical splice action twice (ie: with different names), the splice
#   will be executed twice.
# - Vivado's `updatemen` utility is SLOW.  We can easily afford the disk
#   space for lots of identical splices, but we cannot afford the impact
#   on execution time.
#
###########################################################################

import argparse
import contextlib
import fcntl
import hashlib
import json
import logging
import os
import os.path
import subprocess
import sys
import tempfile
import time

CACHE_DIR = '~/.cache/opentitan-bitstreams'

flags = argparse.ArgumentParser(description='Bitstream splice cache manager')
flags.add_argument('--logging',
                   default='info',
                   choices=['debug', 'info', 'warning', 'error', 'critical'],
                   help='Logging level')
flags.add_argument('--cache', default=CACHE_DIR, help='Cache directory name')
flags.add_argument('--cache-entries',
                   default=300,
                   type=int,
                   help='Number of splices to keep in the cache')
flags.add_argument('--gen_vivado_image',
                   type=str,
                   help='Path of the gen_vivado_image script')
flags.add_argument('--swap-nibbles',
                   action=argparse.BooleanOptionalAction,
                   default=True,
                   help='Swap nibbles when creating the mem image')
flags.add_argument('--updatemem',
                   default='updatemem',
                   help='Name (or path) of the updatemem program')
flags.add_argument('--opentitantool', help='Path of opentitantool')
flags.add_argument(
    '--update-usr-access',
    help='Use opentitantool to update the USR_ACCESS value after a splice')
flags.add_argument('-o', '--output', type=str, help='Path of the output file')
flags.add_argument('--mmi',
                   type=str,
                   help='Comma-separated paths of MMI files')
flags.add_argument(
    '--data',
    type=str,
    help='Comma-separated paths of data files to splce into the bitstream')
flags.add_argument('--symlink',
                   action=argparse.BooleanOptionalAction,
                   default=True,
                   help='Symlink the output to the cached file')
flags.add_argument('bitstream', type=str, help='The input bitstrem to splice')


def open_locked(filename, binary=False):
    mode = 'b' if binary else ''
    try:
        # Try open the file for exclusive-create.
        f = open(filename, 'x+' + mode)
    except FileExistsError:
        # If that fails, open for read-write.
        f = open(filename, 'r+' + mode)
    # This lock will block when contended.  Closing the file or aborting the
    # process will automatically unlock it.
    fcntl.lockf(f, fcntl.LOCK_EX)
    return f


@contextlib.contextmanager
def LockedFile(filename, binary=False):
    file = open_locked(filename, binary)
    try:
        yield file
    finally:
        file.close()


class CacheControlFile(object):

    def __init__(self, filename):
        self.filename = filename
        self.open()

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.close()

    def open(self):
        """Open and lock the cache."""
        self.cache = {'version': 1, 'entry': {}}
        self.file = open_locked(self.filename)
        data = self.file.read()
        if data:
            self.cache = json.loads(data)
        self.dirty = False

    def refresh(self):
        self.close()
        self.open()

    @property
    def version(self):
        return self.cache['version']

    def get(self, key):
        """Get a key from the cache."""
        return self.cache['entry'].get(key)

    def create(self, key, filename):
        """Create an entry in the cache."""
        entry = {
            'filename': filename,
            'create': int(time.time()),
            'access': int(time.time()),
            'digest': "",
        }
        self.cache['entry'][key] = entry
        self.dirty = True
        return entry

    def update(self, key, **kwargs):
        """Updates an entry's access time and digest value."""
        entry = self.get(key)
        entry.update(kwargs)
        entry['access'] = int(time.time())
        self.dirty = True

    def access(self, key):
        """Updates an entry's access time."""
        entry = self.get(key)
        entry['access'] = int(time.time())
        self.dirty = True

    def expire(self, num_to_keep):
        items = self.cache['entry'].items()
        items = sorted(items, key=lambda x: x[1]['access'])
        self.cache['entry'] = dict(items[:num_to_keep])
        return dict(items[num_to_keep:])

    def close(self):
        """Save and close the cache."""
        if self.dirty:
            self.file.seek(0)
            self.file.truncate()
            self.file.write(json.dumps(self.cache, indent=2))
        self.file.close()


class Tools(object):

    def __init__(self, args):
        self._gen_vivado_image = args.gen_vivado_image
        self._updatemem = args.updatemem
        self._opentitantool = args.opentitantool

    @staticmethod
    def hash(files):
        """Compute a SHA256 hash-of-hashes over the input files.

        Args:
          files: List[str]; A list of filenames
        Returns:
          str: the hex digest of the input hashes.
        """
        h = hashlib.sha256()
        for file in files:
            data = open(file, 'rb').read()
            fh = hashlib.sha256(data)
            h.update(fh.digest())
        return h.hexdigest()

    @staticmethod
    def remove_files(files):
        """Remove a list of files.

        Args:
          files: List[str]; A list of filenames
        """
        for file in files:
            try:
                logging.info(f"Removing expired file {file}.")
                os.unlink(file)
            except FileNotFoundError:
                pass

    def gen_vivado_image(self, infile, outfile, swap_nibbles):
        """Transform an input into a form acceptable for splicing with Vivado.

        Args:
          infile: str; A binary in the form of a vmem file.
          outfile: str; The output `.mem` file.
          swap_nibbles: bool; Whether to swap nibbles.
        """
        cmd = [self._gen_vivado_image, infile, outfile]
        if swap_nibbles:
            cmd.append('--swap-nibbles')
        subprocess.check_call(cmd)

    def updatemem(self, infile, mmi, data, outfile, debug=False):
        """Use updatemem to splice a bitstream.

        Args:
          infile: str; The input bitstream.
          mmi: str; Path to an MMI memory layout file.
          data: str; Path to the data to splice.
          outfile: str; Path to the output file.
          debug: bool; Whether to enable debug mode.
        """
        cmd = [
            self._updatemem,
            '--force',
            '--meminfo',
            mmi,
            '--data',
            data,
            '--bit',
            infile,
            '--proc',
            'dummy',
            '--out',
            outfile,
        ]
        if debug:
            cmd.append('--debug')
        subprocess.check_call(cmd)

    def update_usr_access(self, infile, outfile):
        """Use opentitantool to update the USR_ACCESS value in the bitstream.

        Args:
          infile: str; The input bitstream.
          outfile: str; Path to the output file.
        """
        cmd = [
            self._opentitantool,
            '--rcfile=',
            '--logging=info',
            'fpga',
            'update-usr-access',
            infile,
            outfile,
        ]
        subprocess.check_call(cmd)

    def splice(self, infile, mmis, datas, outfile, swap_nibbles):
        """Splice multiple files into a bitstream and update USR_ACCESS.

        Args:
          infile: str; The input bitstream.
          mmis: List[str]; Paths to MMI memory layout files.
          datas: List[str]; Paths to data files to splice into the bitstream.
          outfile: file: The already-opened output file.
          swap_nibbles: bool; Whether to swap nibbles.
        Return:
          bytes: The spliced bitstream data
        """
        with tempfile.TemporaryDirectory(prefix='splice-') as tmp:
            # Create the mem files from the input data.
            for i, data in enumerate(datas):
                self.gen_vivado_image(data, f'{tmp}/{i}.mem', swap_nibbles)

            if not infile.endswith('.bit'):
                os.symlink(infile, f'{tmp}/infile.bit')
                infile = f'{tmp}/infile.bit'

            # Splice each data file into the bitstream.
            for i, mmi in enumerate(mmis):
                tmpbit = f'{tmp}/{i}.bit'
                self.updatemem(infile, mmi, f'{tmp}/{i}.mem', tmpbit)
                infile = tmpbit

            # Update the usr_access_value to make this bitstream uniquely identifiable.
            self.update_usr_access(infile, f'{tmp}/updated.bit')

            # Copy the final bitstream into the cache and return the bitstream content.
            with open(f'{tmp}/updated.bit', 'rb') as f:
                content = f.read()
                if outfile:
                    outfile.seek(0)
                    outfile.truncate()
                    outfile.write(content)
                    outfile.seek(0)
                return content


def main(args):
    mmi = args.mmi.split(',')
    data = args.data.split(',')
    if len(data) == 0:
        logging.error('No data files to splice')
        return 1
    if len(data) != len(mmi):
        logging.error(
            'There must be a 1:1 correspondence between data and mmi files')
        return 1

    cachedir = os.path.expanduser(args.cache)
    os.makedirs(os.path.join(cachedir, 'splice'), exist_ok=True)

    tools = Tools(args)
    key = tools.hash([args.bitstream] + data + mmi)

    # We open and lock the cache's bitstream file so that any simultaneous
    # attempts to create or access the bitstream file will block here
    # and allow one process to generate the bitstream.
    filename = f'splice/{key}.bit'
    with LockedFile(os.path.join(cachedir, filename),
                    binary=True) as bitstream:

        logging.info(f'Checking cache for bitstream {key}')
        # We open and lock the cache control file so that access or updates of
        # the control file are serialized.
        with CacheControlFile(f'{cachedir}/splices.json') as cache:
            # Expire old bitstreams to prevent the cache from getting too big.
            expired = cache.expire(args.cache_entries)
            tools.remove_files(
                os.path.join(cachedir, ex['filename'])
                for ex in expired.values())

            splice = cache.get(key)
            if splice is None:
                logging.info('Bitstream doesn\'t exist.  Creating it.')
                splice = cache.create(key, filename)
            elif filename != splice['filename']:
                logging.warning('Bitstream file has moved.  Updating.')
                splice = cache.create(key, filename)
            else:
                logging.info(f'Bitstream is {splice["filename"]}')

            content = bitstream.read()
            digest = hashlib.sha256(content).hexdigest()

            if digest == splice['digest']:
                # If we didn't have to generate the bitstream, just update the
                # access time and close the cache.
                cache.access(key)
            else:
                # We close (and unlock) the cache control file during bitstream
                # generation so that other processes can access the cache.
                # Since the bitstream file is still locked, any attempt at
                # simultaneous access of this bitstream will block at bitstream
                # opening above.
                cache.close()
                if len(content) == 0:
                    logging.info('Generating bitstream because size == 0')
                else:
                    logging.info(
                        'Re-generating bitstream because of digest mismatch')
                content = tools.splice(args.bitstream, mmi, data, bitstream,
                                       args.swap_nibbles)

                # Re-open the cache and update the digest of the bitstream.
                # We record the input filenames to aid in debugging.
                # The CacheControl context manager will close it again upon
                # exit of the `with` block.
                digest = hashlib.sha256(content).hexdigest()
                logging.debug('Calculated digest: {digest}')
                cache.open()
                cache.update(key,
                             digest=digest,
                             inputs=[args.bitstream] + data + mmi)

    if args.symlink:
        os.symlink(os.path.join(cachedir, filename), args.output)
    else:
        with open(args.output, 'wb') as output:
            output.write(content)
    return 0


if __name__ == '__main__':
    args = flags.parse_args()
    logging.basicConfig(level=args.logging.upper())
    sys.exit(main(args))
