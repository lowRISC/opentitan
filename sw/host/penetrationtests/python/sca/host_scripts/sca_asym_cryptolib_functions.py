# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from sw.host.penetrationtests.python.sca.communication.sca_asym_cryptolib_commands import (
    OTAsymCrypto,
)
from sw.host.penetrationtests.python.sca.communication.sca_prng_commands import OTPRNG


def char_rsa_dec(
    target,
    iterations,
    data,
    data_len,
    e,
    n,
    n_len,
    d,
    padding,
    hashing,
    mode,
    cfg,
    trigger,
    reset=False,
):
    asymsca = OTAsymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = asymsca.init()
    # Set the internal prng
    ot_prng = OTPRNG(target=target)
    ot_prng.seed_prng([1, 0, 0, 0])
    for _ in range(iterations):
        asymsca.handle_rsa_dec(data, data_len, e, n, n_len, d, padding, hashing, mode, cfg, trigger)
        response = target.read_response()
    return response


def char_rsa_sign(
    target,
    iterations,
    data,
    data_len,
    e,
    n,
    n_len,
    d,
    padding,
    hashing,
    cfg,
    trigger,
    reset=False,
):
    asymsca = OTAsymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = asymsca.init()
    # Set the internal prng
    ot_prng = OTPRNG(target=target)
    ot_prng.seed_prng([1, 0, 0, 0])

    for _ in range(iterations):
        asymsca.handle_rsa_sign(data, data_len, e, n, n_len, d, padding, hashing, cfg, trigger)
        response = target.read_response()
    return response


def char_prime_generation(
    target,
    iterations,
    e,
    cfg,
    trigger,
    reset=False,
):
    asymsca = OTAsymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = asymsca.init()
    for _ in range(iterations):
        asymsca.handle_prime_generation(
            e,
            cfg,
            trigger,
        )
        response = target.read_response()
    return response


def char_p256_base_mult_fvsr(
    target,
    iterations,
    scalar,
    cfg,
    trigger,
    num_iterations,
    reset=False,
):
    asymsca = OTAsymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = asymsca.init()
    # Set the internal prng
    ot_prng = OTPRNG(target=target)
    ot_prng.seed_prng([1, 0, 0, 0])

    for _ in range(iterations):
        asymsca.handle_p256_base_mult_fvsr(scalar, cfg, trigger, num_iterations)
        response = target.read_response(init_timeout=0.01 * num_iterations)
    return response


def char_p256_base_mult_daisy(
    target,
    iterations,
    scalar,
    cfg,
    trigger,
    num_iterations,
    reset=False,
):
    asymsca = OTAsymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = asymsca.init()
    for _ in range(iterations):
        asymsca.handle_p256_base_mult_daisy(scalar, cfg, trigger, num_iterations)
        response = target.read_response(init_timeout=0.01 * num_iterations)
    return response


def char_p256_point_mult(
    target,
    iterations,
    scalar_alice,
    scalar_bob,
    cfg,
    trigger,
    reset=False,
):
    asymsca = OTAsymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = asymsca.init()
    for _ in range(iterations):
        asymsca.handle_p256_point_mult(scalar_alice, scalar_bob, cfg, trigger)
        response = target.read_response()
    return response


def char_p256_ecdh(
    target,
    iterations,
    private_key,
    public_x,
    public_y,
    cfg,
    trigger,
    reset=False,
):
    asymsca = OTAsymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = asymsca.init()
    for _ in range(iterations):
        asymsca.handle_p256_ecdh(private_key, public_x, public_y, cfg, trigger)
        response = target.read_response()
    return response


def char_p256_sign(
    target,
    iterations,
    scalar,
    pubx,
    puby,
    message,
    cfg,
    trigger,
    reset=False,
):
    asymsca = OTAsymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = asymsca.init()
    for _ in range(iterations):
        asymsca.handle_p256_sign(scalar, pubx, puby, message, cfg, trigger)
        response = target.read_response()
    return response


def char_p384_base_mult_fvsr(
    target,
    iterations,
    scalar,
    cfg,
    trigger,
    num_iterations,
    reset=False,
):
    asymsca = OTAsymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = asymsca.init()
    # Set the internal prng
    ot_prng = OTPRNG(target=target)
    ot_prng.seed_prng([1, 0, 0, 0])
    for _ in range(iterations):
        asymsca.handle_p384_base_mult_fvsr(scalar, cfg, trigger, num_iterations)
        response = target.read_response(init_timeout=0.01 * num_iterations)
    return response


def char_p384_base_mult_daisy(
    target,
    iterations,
    scalar,
    cfg,
    trigger,
    num_iterations,
    reset=False,
):
    asymsca = OTAsymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = asymsca.init()
    for _ in range(iterations):
        asymsca.handle_p384_base_mult_daisy(scalar, cfg, trigger, num_iterations)
        response = target.read_response(init_timeout=0.01 * num_iterations)
    return response


def char_p384_point_mult(
    target,
    iterations,
    scalar_alice,
    scalar_bob,
    cfg,
    trigger,
    reset=False,
):
    asymsca = OTAsymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = asymsca.init()
    for _ in range(iterations):
        asymsca.handle_p384_point_mult(scalar_alice, scalar_bob, cfg, trigger)
        response = target.read_response()
    return response


def char_p384_ecdh(
    target,
    iterations,
    private_key,
    public_x,
    public_y,
    cfg,
    trigger,
    reset=False,
):
    asymsca = OTAsymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = asymsca.init()
    for _ in range(iterations):
        asymsca.handle_p384_ecdh(private_key, public_x, public_y, cfg, trigger)
        response = target.read_response()
    return response


def char_p384_sign(
    target,
    iterations,
    scalar,
    pubx,
    puby,
    message,
    cfg,
    trigger,
    reset=False,
):
    asymsca = OTAsymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = asymsca.init()
    for _ in range(iterations):
        asymsca.handle_p384_sign(scalar, pubx, puby, message, cfg, trigger)
        response = target.read_response()
    return response
