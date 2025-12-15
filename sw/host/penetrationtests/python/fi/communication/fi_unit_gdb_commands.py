# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Communication interface for OpenTitan Symmetric Cryptolib FI framework.

Communication with OpenTitan happens over the uJSON command interface.
"""

import json
import time
from sw.host.penetrationtests.python.util import common_library


class OTFIUnitGdb:
    def __init__(self, target) -> None:
        self.target = target

    def init(
        self,
        core_config: dict = common_library.default_core_config,
        sensor_config: dict = common_library.default_sensor_config,
        alert_config: dict = common_library.default_alert_config,
    ) -> tuple:
        """Initialize the code on the chip.
        Args:
            cfg: Config dict containing the selected test.

        Returns:
            Device id
            The owner info page
            The boot log
            The boot measurements
            The testOS version
        """

        self.target.write(json.dumps("Init").encode("ascii"))
        time.sleep(0.003)

        # Write each configuration block to the target.
        self.target.write(json.dumps(core_config).encode("ascii"))
        self.target.write(json.dumps(sensor_config).encode("ascii"))
        self.target.write(json.dumps(alert_config).encode("ascii"))

        device_id = self.target.read_response()
        sensors = self.target.read_response()
        alerts = self.target.read_response()
        owner_page = self.target.read_response()
        boot_log = self.target.read_response()
        boot_measurements = self.target.read_response()
        version = self.target.read_response()
        return (
            device_id,
            sensors,
            alerts,
            owner_page,
            boot_log,
            boot_measurements,
            version,
        )

    def handle_gdb_try(
        self,
    ) -> None:
        self.target.write(json.dumps("Try").encode("ascii"))

    def handle_gdb_switch(
        self,
    ) -> None:
        self.target.write(json.dumps("Switch").encode("ascii"))

    def handle_gdb_if(
        self,
    ) -> None:
        self.target.write(json.dumps("If").encode("ascii"))
