# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from sw.host.penetrationtests.python.sca.communication.sca_ibex_commands import OTIbex
from sw.host.penetrationtests.python.sca.communication.sca_prng_commands import OTPRNG


def char_combi_operations_batch(
    target, iterations, num_segments, trigger, fixed_data1, fixed_data2, reset = False
):
    ibexsca = OTIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = ibexsca.init()
    for _ in range(iterations):
        ibexsca.ibex_sca_combi_operations_batch(
            num_iterations=num_segments,
            trigger=trigger,
            fixed_data1=fixed_data1,
            fixed_data2=fixed_data2,
        )
        response = target.read_response()
    return response


def char_combi_operations_batch_fvsr(
    target, iterations, num_segments, trigger, fixed_data1, fixed_data2, reset = False
):
    # Seed the prng to make synchronized randomness
    # This is the same as using python rand with seed 1
    otprng = OTPRNG(target)
    otprng.seed_prng([1, 0, 0, 0])
    ibexsca = OTIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = ibexsca.init()
    for _ in range(iterations):
        ibexsca.ibex_sca_combi_operations_batch_fvsr(
            num_iterations=num_segments,
            trigger=trigger,
            fixed_data1=fixed_data1,
            fixed_data2=fixed_data2,
        )
        response = target.read_response()
    return response


def char_register_file_read(target, iterations, data, reset = False):
    ibexsca = OTIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = ibexsca.init()
    for _ in range(iterations):
        ibexsca.ibex_sca_register_file_read(data=data)
        response = target.read_response()
    return response


def char_register_file_read_batch_fvsr(target, iterations, data, num_segments, reset = False):
    # Seed the prng to make synchronized randomness
    # This is the same as using python rand with seed 1
    otprng = OTPRNG(target)
    otprng.seed_prng([1, 0, 0, 0])
    ibexsca = OTIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = ibexsca.init()
    for _ in range(iterations):
        ibexsca.ibex_sca_register_file_read_batch_fvsr(
            data=data, num_segments=num_segments
        )
        response = target.read_response()
    return response


def char_register_file_read_batch_random(target, iterations, num_segments, reset = False):
    # Seed the prng to make synchronized randomness
    # This is the same as using python rand with seed 1
    otprng = OTPRNG(target)
    otprng.seed_prng([1, 0, 0, 0])
    ibexsca = OTIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = ibexsca.init()
    for _ in range(iterations):
        ibexsca.ibex_sca_register_file_read_batch_random(num_segments=num_segments)
        response = target.read_response()
    return response


def char_register_file_write(target, iterations, data, reset = False):
    ibexsca = OTIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = ibexsca.init()
    for _ in range(iterations):
        ibexsca.ibex_sca_register_file_write(data=data)
        response = target.read_response()
    return response


def char_register_file_write_batch_fvsr(target, iterations, data, num_segments, reset = False):
    # Seed the prng to make synchronized randomness
    # This is the same as using python rand with seed 1
    otprng = OTPRNG(target)
    otprng.seed_prng([1, 0, 0, 0])
    ibexsca = OTIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = ibexsca.init()
    for _ in range(iterations):
        ibexsca.ibex_sca_register_file_write_batch_fvsr(
            data=data, num_segments=num_segments
        )
        response = target.read_response()
    return response


def char_register_file_write_batch_random(target, iterations, num_segments, reset = False):
    # Seed the prng to make synchronized randomness
    # This is the same as using python rand with seed 1
    otprng = OTPRNG(target)
    otprng.seed_prng([1, 0, 0, 0])
    ibexsca = OTIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = ibexsca.init()
    for _ in range(iterations):
        ibexsca.ibex_sca_register_file_write_batch_random(num_segments=num_segments)
        response = target.read_response()
    return response


def char_tl_read(target, iterations, data, reset = False):
    ibexsca = OTIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = ibexsca.init()
    for _ in range(iterations):
        ibexsca.ibex_sca_tl_read(data=data)
        response = target.read_response()
    return response


def char_tl_read_batch_fvsr(target, iterations, data, num_segments, reset = False):
    # Seed the prng to make synchronized randomness
    # This is the same as using python rand with seed 1
    otprng = OTPRNG(target)
    otprng.seed_prng([1, 0, 0, 0])
    ibexsca = OTIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = ibexsca.init()
    for _ in range(iterations):
        ibexsca.ibex_sca_tl_read_batch_fvsr(data=data, num_segments=num_segments)
        response = target.read_response()
    return response


def char_tl_read_batch_fvsr_fix_address(target, iterations, data, num_segments, reset = False):
    # Seed the prng to make synchronized randomness
    # This is the same as using python rand with seed 1
    otprng = OTPRNG(target)
    otprng.seed_prng([1, 0, 0, 0])
    ibexsca = OTIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = ibexsca.init()
    for _ in range(iterations):
        ibexsca.ibex_sca_tl_read_batch_fvsr_fix_address(
            data=data, num_segments=num_segments
        )
        response = target.read_response()
    return response


def char_tl_read_batch_random(target, iterations, num_segments, reset = False):
    # Seed the prng to make synchronized randomness
    # This is the same as using python rand with seed 1
    otprng = OTPRNG(target)
    otprng.seed_prng([1, 0, 0, 0])
    ibexsca = OTIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = ibexsca.init()
    for _ in range(iterations):
        ibexsca.ibex_sca_tl_read_batch_random(num_segments=num_segments)
        response = target.read_response()
    return response


def char_tl_read_batch_random_fix_address(target, iterations, num_segments, reset = False):
    # Seed the prng to make synchronized randomness
    # This is the same as using python rand with seed 1
    otprng = OTPRNG(target)
    otprng.seed_prng([1, 0, 0, 0])
    ibexsca = OTIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = ibexsca.init()
    for _ in range(iterations):
        ibexsca.ibex_sca_tl_read_batch_random_fix_address(num_segments=num_segments)
        response = target.read_response()
    return response


def char_tl_write(target, iterations, data, reset = False):
    ibexsca = OTIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = ibexsca.init()
    for _ in range(iterations):
        ibexsca.ibex_sca_tl_write(data=data)
        response = target.read_response()
    return response


def char_tl_write_batch_fvsr(target, iterations, data, num_segments, reset = False):
    # Seed the prng to make synchronized randomness
    # This is the same as using python rand with seed 1
    otprng = OTPRNG(target)
    otprng.seed_prng([1, 0, 0, 0])
    ibexsca = OTIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = ibexsca.init()
    for _ in range(iterations):
        ibexsca.ibex_sca_tl_write_batch_fvsr(data=data, num_segments=num_segments)
        response = target.read_response()
    return response


def char_tl_write_batch_fvsr_fix_address(target, iterations, data, num_segments, reset = False):
    # Seed the prng to make synchronized randomness
    # This is the same as using python rand with seed 1
    otprng = OTPRNG(target)
    otprng.seed_prng([1, 0, 0, 0])
    ibexsca = OTIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = ibexsca.init()
    for _ in range(iterations):
        ibexsca.ibex_sca_tl_write_batch_fvsr_fix_address(
            data=data, num_segments=num_segments
        )
        response = target.read_response()
    return response


def char_tl_write_batch_random(target, iterations, num_segments, reset = False):
    # Seed the prng to make synchronized randomness
    # This is the same as using python rand with seed 1
    otprng = OTPRNG(target)
    otprng.seed_prng([1, 0, 0, 0])
    ibexsca = OTIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = ibexsca.init()
    for _ in range(iterations):
        ibexsca.ibex_sca_tl_write_batch_random(num_segments=num_segments)
        response = target.read_response()
    return response


def char_tl_write_batch_random_fix_address(target, iterations, num_segments, reset = False):
    # Seed the prng to make synchronized randomness
    # This is the same as using python rand with seed 1
    otprng = OTPRNG(target)
    otprng.seed_prng([1, 0, 0, 0])
    ibexsca = OTIbex(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = ibexsca.init()
    for _ in range(iterations):
        ibexsca.ibex_sca_tl_write_batch_random_fix_address(num_segments=num_segments)
        response = target.read_response()
    return response
