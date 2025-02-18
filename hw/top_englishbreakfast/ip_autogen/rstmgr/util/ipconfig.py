# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
This contains a class to access the rstmgr's configuration from its ipconfig
files.
"""
from typing import List


class IpConfig:
    def __init__(self, ipconfig: object):
        """
        Initialize an `IpConfig` from an already loaded and parsed `ipconfog.hjson`
        file, as well as a top configuration.
        """
        self.param_values = ipconfig["param_values"]

    def sw_rsts_list(self) -> List[str]:
        """
        Return the list of SW resets: each reset is described by the name of its
        signal.

        The list is ordered in the same as in the description.
        """
        return self.param_values["sw_rsts"]
