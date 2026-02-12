# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from sw.host.penetrationtests.python.fi.communication.fi_otbn_commands import OTFIOtbn
from sw.host.penetrationtests.python.util import common_library


def char_beq(target, iterations, reset = False):
    otbnfi = OTFIOtbn(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        otbnfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        otbnfi.otbn_char_beq()
        response = target.read_response()
    # Return the result that is read out
    return response


def char_bn_rshi(target, iterations, data, reset = False):
    otbnfi = OTFIOtbn(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        otbnfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        otbnfi.otbn_char_bn_rshi(data)
        response = target.read_response()
    # Return the result that is read out
    return response


def char_bn_sel(target, iterations, data, reset = False):
    otbnfi = OTFIOtbn(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        otbnfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        otbnfi.otbn_char_bn_sel(data)
        response = target.read_response()
    # Return the result that is read out
    return response


def char_bn_wsrr(target, iterations, reset = False):
    otbnfi = OTFIOtbn(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        otbnfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        otbnfi.otbn_char_bn_wsrr()
        response = target.read_response()
    # Return the result that is read out
    return response


def char_bne(target, iterations, reset = False):
    otbnfi = OTFIOtbn(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        otbnfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        otbnfi.otbn_char_bne()
        response = target.read_response()
    # Return the result that is read out
    return response


def char_dmem_access(target, iterations, reset = False):
    otbnfi = OTFIOtbn(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        otbnfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        otbnfi.otbn_char_dmem_access()
        response = target.read_response()
    # Return the result that is read out
    return response


def char_dmem_write(target, iterations, reset = False):
    otbnfi = OTFIOtbn(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        otbnfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        otbnfi.otbn_char_dmem_write()
        response = target.read_response()
    # Return the result that is read out
    return response


def char_dmem_op_loop(target, iterations, reset = False):
    otbnfi = OTFIOtbn(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        otbnfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        otbnfi.otbn_char_hardware_dmem_op_loop()
        response = target.read_response()
    # Return the result that is read out
    return response


def char_reg_op_loop(target, iterations, reset = False):
    otbnfi = OTFIOtbn(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        otbnfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        otbnfi.otbn_char_hardware_reg_op_loop()
        response = target.read_response()
    # Return the result that is read out
    return response


def char_jal(target, iterations, reset = False):
    otbnfi = OTFIOtbn(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        otbnfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        otbnfi.otbn_char_jal()
        response = target.read_response()
    # Return the result that is read out
    return response


def char_lw(target, iterations, reset = False):
    otbnfi = OTFIOtbn(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        otbnfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        otbnfi.otbn_char_lw()
        response = target.read_response()
    # Return the result that is read out
    return response


def char_mem(target, iterations, byte_offset, num_words, imem, dmem, reset = False):
    otbnfi = OTFIOtbn(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        otbnfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    # The config is only set in the first call
    first_call = True
    for _ in range(iterations):
        otbnfi.otbn_char_mem(byte_offset, num_words, imem, dmem, first_call)
        first_call = False
        response = target.read_response()
    # Return the result that is read out
    return response


def char_rf(target, iterations, reset = False):
    otbnfi = OTFIOtbn(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        otbnfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        otbnfi.otbn_char_rf()
        response = target.read_response()
    # Return the result that is read out
    return response


def char_unrolled_dmem_op_loop(target, iterations, reset = False):
    otbnfi = OTFIOtbn(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        otbnfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        otbnfi.otbn_char_unrolled_dmem_op_loop()
        response = target.read_response()
    # Return the result that is read out
    return response


def char_unrolled_reg_op_loop(target, iterations, reset = False):
    otbnfi = OTFIOtbn(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        otbnfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        otbnfi.otbn_char_unrolled_reg_op_loop()
        response = target.read_response()
    # Return the result that is read out
    return response


def char_load_integrity(target, iterations, reset = False):
    otbnfi = OTFIOtbn(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        otbnfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        otbnfi.otbn_load_integrity()
        response = target.read_response()
    # Return the result that is read out
    return response


def char_pc(target, iterations, pc, reset = False):
    otbnfi = OTFIOtbn(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        otbnfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        otbnfi.otbn_pc(pc)
        response = target.read_response()
    # Return the result that is read out
    return response
