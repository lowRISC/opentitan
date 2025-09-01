# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from sw.host.penetrationtests.python.fi.communication.fi_rom_commands import OTFIRom
from sw.host.penetrationtests.python.util import common_library


def char_rom_read(target, iterations, reset = False):
    romfi = OTFIRom(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        romfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        romfi.handle_rom_read()
        response = target.read_response()
    return response
