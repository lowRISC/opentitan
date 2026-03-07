# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from sw.host.penetrationtests.python.fi.communication.fi_boot_commands import OTFIBoot
from sw.host.penetrationtests.python.util import common_library


def char_inactive_firmware_invalidate(target, reset=False):
    bootfi = OTFIBoot(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        bootfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    bootfi.handle_inactive_firmware_invalidate()
    return target.read_response()


def char_next_slot(target, reset=False):
    bootfi = OTFIBoot(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        bootfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    # Target resets after this
    bootfi.handle_next_slot()


def char_boot_status(target, reset=False):
    bootfi = OTFIBoot(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        bootfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    bootfi.handle_boot_status()


def char_epmp_status(target, reset=False):
    bootfi = OTFIBoot(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        bootfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    bootfi.handle_epmp_status()
