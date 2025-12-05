# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
This contains a class to access the pwrmgr's configuration from its ipconfig
files.
"""
from typing import List, Dict


class PwrmgrIpConfig:
    def __init__(self, ipconfig: object):
        """
        Initialize an `IpConfig` from an already loaded and parsed `ipconfig.hjson`
        files.
        """
        self.param_values = ipconfig["param_values"]

    def wakeup_list(self) -> List[Dict]:
        """
        Return the list of wakeups: each wakeup is described by a dictionary
        with the following fields:
        - `name`: name of the wakeup .
        - `module`: the module where the wakeup comes from.

        The list is ordered as in the description.
        """
        assert self.param_values["NumWkups"] == len(self.param_values["Wkups"])
        return [
            {
                "name": wkup["name"],
                "module": wkup["module"],
            }
            for wkup in self.param_values["Wkups"]
        ]

    def peripheral_reset_req_list(self) -> List[Dict]:
        """
        Return the list of peripheral reset requests: each reset is described by
        a dictionary with the following fields:
        - `name`: name of the reset request.
        - `module`: the module where the reset comes from.

        The list is ordered as in the description.
        """
        assert self.param_values["NumRstReqs"] == len(self.param_values["rst_reqs"]["peripheral"])
        return [
            {
                "name": rst["name"],
                "module": rst["module"],
            }
            for rst in self.param_values["rst_reqs"]["peripheral"]
        ]
