# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from sw.host.penetrationtests.python.fi.communication.fi_rng_commands import OTFIRng
from sw.host.penetrationtests.python.util import common_library


def char_csrng_bias(target, iterations, trigger, reset = False):
    rngfi = OTFIRng(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        rngfi.init("char_csrng_bias",
                   alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        rngfi.rng_csrng_bias(trigger)
        response = target.read_response()
    return response


def char_edn_resp_ack(target, iterations, reset = False):
    rngfi = OTFIRng(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        rngfi.init("char_csrng_bias",
                   alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        rngfi.rng_edn_resp_ack()
        response = target.read_response()
    return response


def char_edn_bias(target, iterations, reset = False):
    rngfi = OTFIRng(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        rngfi.init("char_edn_bias",
                   alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        rngfi.rng_edn_bias()
        response = target.read_response()
    return response


def char_entropy_bias(target, iterations, reset = False):
    rngfi = OTFIRng(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        rngfi.init("char_entropy_bias",
                   alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        rngfi.rng_entropy_bias()
        response = target.read_response()
    return response


def char_fw_overwrite(target, iterations, disable_health_check, reset = False):
    rngfi = OTFIRng(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        rngfi.init("char_fw_overwrite",
                   alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        rngfi.rng_fw_overwrite(disable_health_check)
        response = target.read_response()
    return response
