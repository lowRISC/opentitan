# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
This contains a class to access the rstmgr's configuration from its ipconfig
files.
"""
from typing import List, Dict


class IpConfig:
    def __init__(self, ipconfig: object):
        """
        Initialize an `IpConfig` from an already loaded and parsed `ipconfig.hjson`
        file, as well as a top configuration.
        """
        self.param_values = ipconfig["param_values"]

    def sw_rsts_list(self) -> List[str]:
        """
        Return the list of SW resets: each reset is described by the name of its
        signal.

        The list is ordered in the same order as in the description.
        """
        return self.param_values["sw_rsts"]

    def hw_reset_req_list(self) -> List[Dict]:
        """
        Return the list of all reset requests: each reset is described by
        a dictionary with the following fields:
        - `name`: name of the reset request.
        - `module`: the module where the reset comes from.

        The list is ordered as in the `HW_REQ` register.
        """
        reqs = self.param_values["reqs"]
        return [
            {
                "name": rst["name"],
                "module": rst["module"],
            }
            # Watch out for the order: this matches what is used in `pwrmgr.hjson.tpl`.
            for rst in reqs["peripheral"] + reqs["int"] + reqs["debug"]
        ]
