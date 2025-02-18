# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
This contains a class to access the rstmgr's configuration from its ipconfig
files.
"""
from typing import List


class IpConfig:
    def __init__(self, topcfg: object, ipconfig: object):
        """
        Initialize an `IpConfig` from an already loaded and parsed `ipconfog.hjson`
        file, as well as a top configuration.
        """
        self.topcfg = topcfg
        self.param_values = ipconfig["param_values"]

        self.rst_map = {}
        for m in topcfg["module"]:
            for (name, conn) in m["reset_connections"].items():
                ll = self.rst_map.get(conn["name"], [])
                ll.append((m["name"], name))
                self.rst_map[conn["name"]] = ll

        # for (name, ll) in self.rst_map.items():
        #     print(f"{name} -> {ll}")

    def sw_rsts_list(self) -> List[Dict]:
        """
        Return the list of SW resets: each reset is described by a dictionary
        with the following fields:
        - `name`: the name of module's reset signal (e.g. `rst_ni`)
        - `module`: the module which is reset (e.g. `usbdev`).

        The list is ordered in the same as in the description.
        """

        sw_rsts = []
        for rstname in self.param_values["sw_rsts"]:
            sw_rst.append({
                "name": "bla",
                "module": "bli"
            })
        return sw_rsts