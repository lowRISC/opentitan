# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""
Code for a wrapper class which represents the "results server".

This is hosted with Google cloud.
"""

import datetime
import logging as log
import subprocess
from shutil import which
from typing import List, Optional


class NoGCPError(Exception):
    """Exception to represent "GCP tools are not installed"."""

    pass


class ResultsServer:
    """A class representing connections to GCP (the results server)."""

    def __init__(self, bucket_name: str):
        """Construct results server; check gsutil is accessible."""
        self.bucket_name = bucket_name

        # A lazy "half check", which tries to check the GCP tools are available
        # on this machine. We could move this check to later (in the methods
        # that actually try to communicate with the server), at which point we
        # could also do permissions checks. But then it's a bit more fiddly to
        # work out what to do when something fails.
        if which('gsutil') is None or which('gcloud') is None:
            raise NoGCPError()

    def _path_in_bucket(self, path: str) -> str:
        """Return path in a format that gsutil understands in our bucket."""
        return "gs://{}/{}".format(self.bucket_name, path)

    def ls(self, path: str) -> List[str]:
        """Find all the files at the given path on the results server.

        This uses "gsutil ls". If gsutil fails, raise a
        subprocess.CalledProcessError.
        """
        process = subprocess.run(['gsutil', 'ls', self._path_in_bucket(path)],
                                 capture_output=True,
                                 universal_newlines=True,
                                 check=True)
        # Get the list of files by splitting into lines, then dropping the
        # empty line at the end.
        return process.stdout.split('\n')[:-1]

    def get_creation_time(self, path: str) -> Optional[datetime.datetime]:
        """Get the creation time at path as a datetime.

        If the file does not exist (or we can't see the creation time for some
        reason), returns None.
        """
        bucket_pfx = 'gs://' + self.bucket_name
        try:
            process = subprocess.run(['gsutil', 'ls', '-l', bucket_pfx + '/' + path],
                                     capture_output=True,
                                     universal_newlines=True,
                                     check=True)
        except subprocess.CalledProcessError:
            log.error("Failed to run ls -l over GCP on {}".format(path))
            return None

        # With gsutil, ls -l on a file prints out something like the following:
        #
        #     35079  2023-07-27T13:26:04Z  gs://rjs-ot-scratch/path/to/my.file
        #
        # Grab the second word on the first (only) line and parse it into a
        # datetime object. Recent versions of Python (3.11+) parse this format
        # with fromisoformat but we can't do that with the minimum version we
        # support.
        timestamp = process.stdout.split()[1]
        try:
            return datetime.datetime.strptime(timestamp, '%Y-%m-%dT%H:%M:%S%z')
        except ValueError:
            log.error("Could not parse creation time ({}) from GCP"
                      .format(timestamp))
            return None

    def mv(self, from_path: str, to_path: str) -> None:
        """Use gsutil mv to move a file/directory."""
        try:
            subprocess.run(['gsutil', 'mv',
                            self._path_in_bucket(from_path),
                            self._path_in_bucket(to_path)],
                           check=True)
        except subprocess.CalledProcessError:
            # If we failed to move the file, print an error message but also
            # fail with an error: we might not want anything downstream to keep
            # going if it assumes some precious object has been moved to a
            # place of safety!
            log.error('Failed to use gsutil to move {} to {}'
                      .format(from_path, to_path))
            raise

    def upload(self,
               local_path: str,
               dst_path: str,
               recursive: bool = False) -> None:
        """Upload a file to GCP.

        Like the "cp" command, dst_path can either be the target directory or
        it can be the name of the file/directory that you're creating inside.

        On failure, prints a message to the log but returns as normal.
        """
        try:
            sub_cmd = ['cp']
            if recursive:
                sub_cmd.append('-r')
            subprocess.run(['gsutil'] + sub_cmd +
                           [local_path,
                            self._path_in_bucket(dst_path)],
                           check=True)
        except subprocess.CalledProcessError:
            # If we failed to copy the file, print an error message but
            # otherwise keep going. We don't want our failed upload to kill the
            # rest of the job.
            log.error('Failed to use gsutil to copy {} to {}'
                      .format(local_path, dst_path))
