# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
This contains a class to access the clkmgr's configuration from its ipconfig
files.
"""
from typing import List, Dict

from topgen.lib import Name


class OtpCtrlIpConfig:
    def __init__(self, ipconfig: object, id_prefix: Name):
        """
        Initialize an `IpConfig` from an already loaded and parsed `ipconfig.hjson`
        file, as well as a top configuration. The `id_prefix` argument defines the
        prefix to be used for partition identifiers.
        """
        self._param_values = ipconfig["param_values"]
        self._id_prefix = id_prefix

    def sw_readable_partitions(self) -> List[Dict]:
        """
        Return the list of OTP partitions whose fields are readable after being locked,
        i.e. those that have a digest (SW or HW), that are not secret and that can not
        be read locked (or only through SW).
        Each partition is described by its name and its identifier through the following
        fields:
        - `name` is the OTP partition name, e.g. `CREATOR_SW_CFG`
        - `id` is the OTP partition identifier, e.g. `kOtpCtrlCreatorSwCfg`
        """
        readable_partitions = []
        for partition in self._param_values["otp_mmap"]["partitions"]:
            if partition.get("read_lock") not in ["CSR", "None"]:
                continue
            if partition.get("secret"):
                continue
            if not partition.get("sw_digest") and not partition.get("hw_digest"):
                continue

            readable_partitions.append(partition)

        return [
            {
                "name": Name.from_snake_case(partition["name"]),
                "id": self._id_prefix + Name.from_snake_case(partition["name"]),
            }
            for partition in readable_partitions
        ]
