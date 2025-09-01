# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from sw.host.penetrationtests.python.fi.communication.fi_alert_commands import OTFIAlert
from sw.host.penetrationtests.python.util import common_library


def char_alert_trigger(target, alert, reset = False):
    alertfi = OTFIAlert(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        alertfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    alertfi.handle_alert_trigger(alert)
    return target.check_reset_or_read_reponse()


def char_alert_sensor_ctrl_trigger(target, reset = False):
    alertfi = OTFIAlert(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        alertfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    alertfi.handle_alert_sensor_ctrl_trigger()
    return target.check_reset_or_read_reponse()


def char_alert_ibex_sw_fatal(target, reset = False):
    alertfi = OTFIAlert(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        alertfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    alertfi.handle_alert_ibex_sw_fatal()
    return target.check_reset_or_read_reponse()
