# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from sw.host.penetrationtests.python.sca.communication.sca_otbn_commands import OTOTBN


def char_combi_operations_batch(
    target,
    iterations,
    num_segments,
    fixed_data1,
    fixed_data2,
    print_flag,
    trigger,
    reset = False
):
    otbnsca = OTOTBN(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = otbnsca.init()
    for _ in range(iterations):
        otbnsca.start_combi_ops_batch(
            num_segments, fixed_data1, fixed_data2, print_flag, trigger
        )
        response = target.read_response()
    return response


def sha2_single(target, msg, msg_len, mode=0, en_masks=True, reset=False):
    otbnsca = OTOTBN(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = otbnsca.init()
    otbnsca.sha2_single(msg, msg_len, mode, en_masks)
    return target.read_response()


def sha2_batch_fvsr(
    target, iterations, num_traces, msg, msg_len, mode=0, en_masks=True, reset=False
):
    otbnsca = OTOTBN(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = otbnsca.init()
    response = None
    for _ in range(iterations):
        otbnsca.sha2_batch_fvsr(num_traces, msg, msg_len, mode, en_masks)
        response = target.read_response()
    return response


def sha2_batch_random(
    target, iterations, num_traces, msg_len, mode=0, en_masks=True, reset=False
):
    otbnsca = OTOTBN(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = otbnsca.init()
    response = None
    for _ in range(iterations):
        otbnsca.sha2_batch_random(num_traces, msg_len, mode, en_masks)
        response = target.read_response()
    return response


def hkdf_single(
    target,
    ikm,
    ikm_len,
    salt,
    salt_len,
    info,
    info_len,
    okm_blocks=1,
    mode=0,
    en_masks=True,
    reset=False,
):
    otbnsca = OTOTBN(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = otbnsca.init()
    otbnsca.hkdf_single(
        ikm, ikm_len, salt, salt_len, info, info_len, okm_blocks, mode, en_masks
    )
    return target.read_response()


def hkdf_batch_fvsr(
    target,
    iterations,
    num_traces,
    ikm,
    ikm_len,
    salt,
    salt_len,
    info,
    info_len,
    okm_blocks=1,
    mode=0,
    en_masks=True,
    reset=False,
):
    otbnsca = OTOTBN(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = otbnsca.init()
    response = None
    for _ in range(iterations):
        otbnsca.hkdf_batch_fvsr(
            num_traces,
            ikm,
            ikm_len,
            salt,
            salt_len,
            info,
            info_len,
            okm_blocks,
            mode,
            en_masks,
        )
        response = target.read_response()
    return response


def hkdf_batch_random(
    target,
    iterations,
    num_traces,
    ikm_len,
    salt_len,
    info,
    info_len,
    okm_blocks=1,
    mode=0,
    en_masks=True,
    reset=False,
):
    otbnsca = OTOTBN(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = otbnsca.init()
    response = None
    for _ in range(iterations):
        otbnsca.hkdf_batch_random(
            num_traces,
            ikm_len,
            salt_len,
            info,
            info_len,
            okm_blocks,
            mode,
            en_masks,
        )
        response = target.read_response()
    return response


def mai_single(
    target,
    in0,
    in1,
    in2,
    mode=0,
    en_masks=True,
    reset=False,
):
    otbnsca = OTOTBN(target)
    if reset:
        target.reset_target()
        target.dump_all()
    device_id, owner_page, boot_log, boot_measurements, version = otbnsca.init()
    otbnsca.mai_single(in0, in1, in2, mode, en_masks)
    return target.read_response()


def mai_batch_fvsr(
    target,
    iterations,
    num_traces,
    in0,
    in1,
    in2,
    mode=0,
    en_masks=True,
    reset=False,
):
    otbnsca = OTOTBN(target)
    if reset:
        target.reset_target()
        target.dump_all()
    device_id, owner_page, boot_log, boot_measurements, version = otbnsca.init()
    response = None
    for _ in range(iterations):
        otbnsca.mai_batch_fvsr(num_traces, in0, in1, in2, mode, en_masks)
        response = target.read_response()
    return response


def mai_batch_random(
    target,
    iterations,
    num_traces,
    mode=0,
    en_masks=True,
    reset=False,
):
    otbnsca = OTOTBN(target)
    if reset:
        target.reset_target()
        target.dump_all()
    device_id, owner_page, boot_log, boot_measurements, version = otbnsca.init()
    response = None
    for _ in range(iterations):
        otbnsca.mai_batch_random(num_traces, mode, en_masks)
        response = target.read_response()
    return response
