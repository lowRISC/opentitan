# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import sys
from typing import Union


class VersionInformation():
    def __init__(self, path: str):
        """
        Parse a bazel version file and store a dictionary of the values.
        If `path` is None, an empty dictionary will be created.
        If an error occurs during parsing, an exception is raised.
        """
        self.version_stamp = {}
        if path is None:
            return
        try:
            with open(path, 'rt') as f:
                for line in f:
                    k, v = line.strip().split(' ', 1)
                    self.version_stamp[k] = v
        except ValueError:
            raise SystemExit(sys.exc_info()[1])

    def scm_version(self, default: Union[str, None] = None) -> Union[str, None]:
        return self.version_stamp.get('BUILD_GIT_VERSION', default)

    def scm_revision(self, default: Union[str, None] = None) -> Union[str, None]:
        return self.version_stamp.get('BUILD_SCM_REVISION', default)

    def scm_status(self, default: Union[str, None] = None) -> Union[str, None]:
        return self.version_stamp.get('BUILD_SCM_STATUS', default)
