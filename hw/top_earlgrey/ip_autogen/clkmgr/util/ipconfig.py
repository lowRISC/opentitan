# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
This contains a class to access the clkmgr's configuration from its ipconfig
files.
"""
from typing import List, Dict


class ClkmgrIpConfig:
    def __init__(self, ipconfig: object):
        """
        Initialize an `IpConfig` from an already loaded and parsed `ipconfig.hjson`
        file, as well as a top configuration.
        """
        self.param_values = ipconfig["param_values"]

    def sw_clks(self) -> List[Dict]:
        """
        Return the list of software controllable clocks: each clock is described by a
        dictionary with the following fields:
        - `src`: clock source
        - `module`: the module whose clock is controlled.

        The list is ordered as in the description.
        """
        return [
            {
                "src": clk["src_name"],
                "module": clk["endpoint_ip"],
            }
            for clk in self.param_values["typed_clocks"]["sw_clks"].values()
        ]

    def hint_clks(self) -> List[Dict]:
        """
        Return the list of hintable clocks: each clock is described by a
        dictionary with the following fields:
        - `src`: clock source
        - `module`: the module whose clock is controlled.

        The list is ordered as in the description.
        """
        return [
            {
                "src": clk["src_name"],
                "module": clk["endpoint_ip"],
            }
            for clk in self.param_values["typed_clocks"]["hint_clks"].values()
        ]
