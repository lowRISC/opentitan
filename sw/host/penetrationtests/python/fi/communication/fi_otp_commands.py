# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Communication interface for OpenTitan Otp FI framework.

Communication with OpenTitan happens over the uJSON command interface.
"""
import json
import time
from sw.host.penetrationtests.python.util import common_library


class OTFIOtp:
    def __init__(self, target) -> None:
        self.target = target

    def _ujson_otp_fi_cmd(self) -> None:
        self.target.write(json.dumps("OtpFi").encode("ascii"))
        time.sleep(0.003)

    def otp_fi_vendor_test(self) -> None:
        """Reads otp VENDOR_TEST partition."""
        # IbexFi command.
        self._ujson_otp_fi_cmd()
        # VendorTest command.
        self.target.write(json.dumps("VendorTest").encode("ascii"))

    def otp_fi_owner_sw_cfg(self) -> None:
        """Reads otp OWNER_SW_CFG partition."""
        # IbexFi command.
        self._ujson_otp_fi_cmd()
        # OwnerSwCfg command.
        self.target.write(json.dumps("OwnerSwCfg").encode("ascii"))

    def otp_fi_hw_cfg(self) -> None:
        """Reads otp HW_CFG partition."""
        # IbexFi command.
        self._ujson_otp_fi_cmd()
        # HwCfg command.
        self.target.write(json.dumps("HwCfg").encode("ascii"))

    def otp_fi_life_cycle(self) -> None:
        """Reads otp LIFE_CYCLE partition."""
        # IbexFi command.
        self._ujson_otp_fi_cmd()
        # LifeCycle command.
        self.target.write(json.dumps("LifeCycle").encode("ascii"))

    def init(
        self,
        core_config: dict = common_library.default_core_config,
        sensor_config: dict = common_library.default_sensor_config,
        alert_config: dict = common_library.default_alert_config,
    ) -> tuple:
        """Initialize the Otp FI code on the chip.
        Args:
            cfg: Config dict containing the selected test.

        Returns:
            Device id
            The owner info page
            The boot log
            The boot measurements
            The testOS version
        """

        # OtpFi command.
        self._ujson_otp_fi_cmd()
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

    def start_test(self, cfg: dict) -> None:
        """Start the selected test.

        Call the function selected in the config file. Uses the getattr()
        construct to call the function.

        Args:
            cfg: Config dict containing the selected test.
        """
        test_function = getattr(self, cfg["test"]["which_test"])
        test_function()
