# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from sw.host.penetrationtests.python.fi.communication.fi_ibex_commands import OTFIIbex
from sw.host.penetrationtests.python.util import common_library


def char_address_translation(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_address_translation()
        response = target.read_response()
    return response


def char_address_translation_config(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_address_translation_config()
        response = target.read_response()
    return response


def char_addi_single_beq(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_addi_single_beq()
        response = target.read_response()
    return response


def char_addi_single_beq_cm(target, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    ibexfi.ibex_char_addi_single_beq_cm()
    # This crashes the chip in a regular circumstance
    return target.check_fault_or_read_reponse()


def char_addi_single_beq_cm2(target, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    ibexfi.ibex_char_addi_single_beq_cm2()
    # This crashes the chip in a regular circumstance
    return target.check_fault_or_read_reponse()


def char_addi_single_beq_neg(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_addi_single_beq_neg()
        response = target.read_response()
    return response


def char_addi_single_bne(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_addi_single_bne()
        response = target.read_response()
    return response


def char_addi_single_bne_neg(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_addi_single_bne_neg()
        response = target.read_response()
    return response


def char_combi(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_combi()
        response = target.read_response()
    return response


def char_conditional_branch_beq(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_conditional_branch_beq()
        response = target.read_response()
    return response


def char_conditional_branch_bge(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_conditional_branch_bge()
        response = target.read_response()
    return response


def char_conditional_branch_bgeu(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_conditional_branch_bgeu()
        response = target.read_response()
    return response


def char_conditional_branch_blt(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_conditional_branch_blt()
        response = target.read_response()
    return response


def char_conditional_branch_bltu(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_conditional_branch_bltu()
        response = target.read_response()
    return response


def char_conditional_branch_bne(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_conditional_branch_bne()
        response = target.read_response()
    return response


def char_csr_read(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_csr_read()
        response = target.read_response()
    return response


def char_csr_write(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_csr_write()
        response = target.read_response()
    return response


def char_csr_combi(target, trigger, ref_values, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_csr_combi(trigger, ref_values)
        response = target.read_response()
    return response


def char_flash_read(target, flash_region, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_flash_read(flash_region)
        response = target.read_response()
    return response


def char_flash_read_static(target, init, flash_region, iterations, reset=False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = ibexfi.init(
        alert_config=common_library.default_fpga_friendly_alert_config
    )
    for _ in range(iterations):
        ibexfi.ibex_char_flash_read_static(init, flash_region)
        response = target.read_response()
    return response


def char_flash_write(target, flash_region, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_flash_write(flash_region)
        response = target.read_response()
    return response


def char_hardened_check_eq_complement_branch(target, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    ibexfi.ibex_char_hardened_check_eq_complement_branch()
    # This crashes the chip in a regular circumstance
    return target.check_fault_or_read_reponse()


def char_hardened_check_eq_unimp(target, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    ibexfi.ibex_char_hardened_check_eq_unimp()
    # This crashes the chip in a regular circumstance
    return target.check_fault_or_read_reponse()


def char_hardened_check_eq_2_unimps(target, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    ibexfi.ibex_char_hardened_check_eq_2_unimps()
    # This crashes the chip in a regular circumstance
    return target.check_fault_or_read_reponse()


def char_hardened_check_eq_3_unimps(target, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    ibexfi.ibex_char_hardened_check_eq_3_unimps()
    # This crashes the chip in a regular circumstance
    return target.check_fault_or_read_reponse()


def char_hardened_check_eq_4_unimps(target, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    ibexfi.ibex_char_hardened_check_eq_4_unimps()
    # This crashes the chip in a regular circumstance
    return target.check_fault_or_read_reponse()


def char_hardened_check_eq_5_unimps(target, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    ibexfi.ibex_char_hardened_check_eq_5_unimps()
    # This crashes the chip in a regular circumstance
    return target.check_fault_or_read_reponse()


def char_mem_op_loop(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_mem_op_loop()
        response = target.read_response()
    return response


def char_register_file(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_register_file()
        response = target.read_response()
    return response


def char_register_file_read(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_register_file_read()
        response = target.read_response()
    return response


def char_reg_op_loop(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_reg_op_loop()
        response = target.read_response()
    return response


def char_single_beq(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_single_beq()
        response = target.read_response()
    return response


def char_single_bne(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_single_bne()
        response = target.read_response()
    return response


def char_sram_read(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_sram_read()
        response = target.read_response()
    return response


def char_sram_read_ret(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_sram_read_ret()
        response = target.read_response()
    return response


def char_sram_static(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_sram_static()
        response = target.read_response()
    return response


def char_sram_write(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_sram_write()
        response = target.read_response()
    return response


def char_sram_write_read(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_sram_write_read()
        response = target.read_response()
    return response


def char_sram_write_read_alt(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_sram_write_read_alt()
        response = target.read_response()
    return response


def char_sram_write_static_unrolled(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_sram_write_static_unrolled()
        response = target.read_response()
    return response


def char_unconditional_branch(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_unconditional_branch()
        response = target.read_response()
    return response


def char_unconditional_branch_nop(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_unconditional_branch_nop()
        response = target.read_response()
    return response


def char_unrolled_mem_op_loop(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_unrolled_mem_op_loop()
        response = target.read_response()
    return response


def char_unrolled_reg_op_loop(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_unrolled_reg_op_loop()
        response = target.read_response()
    return response


def char_unrolled_reg_op_loop_chain(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_unrolled_reg_op_loop_chain()
        response = target.read_response()
    return response


def char_otp_data_read(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_otp_data_read()
        response = target.read_response()
    return response


def char_otp_read_lock(target, iterations, reset = False):
    ibexfi = OTFIIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        ibexfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        ibexfi.ibex_char_otp_read_lock()
        response = target.read_response()
    return response
