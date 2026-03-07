# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Communication interface for OpenTitan Boot FI framework.

Communication with OpenTitan happens over the uJSON command interface.
"""
import json
import time
from sw.host.penetrationtests.python.util import common_library


class OTFIBoot:
    def __init__(self, target) -> None:
        self.target = target

    def _ujson_boot_fi_cmd(self) -> None:
        self.target.write(json.dumps("BootFi").encode("ascii"))
        time.sleep(0.003)

    def handle_inactive_firmware_invalidate(self) -> None:
        """Invalidate the inactive firmware."""
        # BootFi command.
        self._ujson_boot_fi_cmd()
        # Invalidate command.
        self.target.write(json.dumps("InactiveFirmwareInvalidate").encode("ascii"))

    def handle_next_slot(self) -> None:
        """Sets the next slot as the primary."""
        # BootFi command.
        self._ujson_boot_fi_cmd()
        # NextSlot command.
        self.target.write(json.dumps("NextSlot").encode("ascii"))

    def handle_boot_status(self) -> None:
        """Get status of boot slots."""
        # BootFi command.
        self._ujson_boot_fi_cmd()
        # BootStatus command.
        self.target.write(json.dumps("BootStatus").encode("ascii"))

    def handle_epmp_status(self) -> None:
        """Get status of epmp entries."""
        # BootFi command.
        self._ujson_boot_fi_cmd()
        # EpmpStatus command.
        self.target.write(json.dumps("EpmpStatus").encode("ascii"))

    def init(
        self,
        core_config: dict = common_library.default_core_config,
        sensor_config: dict = common_library.default_sensor_config,
        alert_config: dict = common_library.default_alert_config,
    ) -> tuple:
        """Initialize the Boot FI code on the chip.
        Args:
            cfg: Config dict containing the selected test.

        Returns:
            Device id
            The owner info page
            The boot log
            The boot measurements
            The testOS version
        """

        # BootFi command.
        self._ujson_boot_fi_cmd()
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
