# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""
Code for a wrapper class which represents the "results server".

This is hosted with Google cloud.
"""

import subprocess
from shutil import which
from typing import List


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
