# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Communication interface for the SHA3 SCA application on OpenTitan.

Communication with OpenTitan happens over the uJson
command interface.
"""
import json
import time
from typing import Optional


class OTTRIGGER:
    def __init__(self, target) -> None:
        self.target = target

    def select_trigger(self, trigger_source: Optional[int] = 0):
        """Select the trigger source for SCA.
        Args:
            trigger_source:
                            - 0: Precise, hardware-generated trigger - FPGA only.
                            - 1: Fully software-controlled trigger.
        """
        self.target.write(json.dumps("TriggerSca").encode("ascii"))
        time.sleep(0.003)
        # SelectTriggerSource command.
        self.target.write(json.dumps("SelectTriggerSource").encode("ascii"))
        # Source payload.
        src = {"source": trigger_source}
        self.target.write(json.dumps(src).encode("ascii"))
