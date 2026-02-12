# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Communication interface for OpenTitan Alert FI framework.

Communication with OpenTitan happens over the uJSON command interface.
"""
import json
import time
from sw.host.penetrationtests.python.util import common_library


class OTFIAlert:
    def __init__(self, target) -> None:
        self.target = target

    def _ujson_alert_fi_cmd(self) -> None:
        self.target.write(json.dumps("AlertFi").encode("ascii"))
        time.sleep(0.003)

    def handle_alert_trigger(self, alert) -> None:
        # AlertFi command.
        self._ujson_alert_fi_cmd()
        # Trigger command.
        self.target.write(json.dumps("Trigger").encode("ascii"))
        alert_data = {"alert": alert}
        self.target.write(json.dumps(alert_data).encode("ascii"))

    def handle_alert_sensor_ctrl_trigger(self) -> None:
        # AlertFi command.
        self._ujson_alert_fi_cmd()
        # SensorCtrlTrigger command.
        self.target.write(json.dumps("SensorCtrlTrigger").encode("ascii"))

    def handle_alert_ibex_sw_fatal(self) -> None:
        # AlertFi command.
        self._ujson_alert_fi_cmd()
        # IbexSwFatal command.
        self.target.write(json.dumps("IbexSwFatal").encode("ascii"))

    def init(
        self,
        core_config: dict = common_library.default_core_config,
        sensor_config: dict = common_library.default_sensor_config,
        alert_config: dict = common_library.default_alert_config,
    ) -> tuple:
        """Initialize the ALERT FI code on the chip.
        Args:
            cfg: Config dict containing the selected test.

        Returns:
            Device id
            The owner info page
            The boot log
            The boot measurements
            The testOS version
        """

        # AlertFi command.
        self._ujson_alert_fi_cmd()
        # Init command.
        self.target.write(json.dumps("Init").encode("ascii"))

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
