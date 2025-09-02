# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from sw.host.penetrationtests.python.fi.communication.fi_asym_cryptolib_commands import (
    OTFIAsymCrypto,
)
from sw.host.penetrationtests.python.util import common_library


def char_rsa_encrypt(
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
    op_enc,
    cfg,
    trigger,
    reset=False,
):
    asymfi = OTFIAsymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        asymfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        asymfi.handle_rsa_enc(
            data, data_len, e, n, n_len, d, padding, hashing, mode, op_enc, cfg, trigger
        )
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
    asymfi = OTFIAsymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        asymfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        asymfi.handle_rsa_sign(
            data, data_len, e, n, n_len, d, padding, hashing, cfg, trigger
        )
        response = target.read_response()
    return response


def char_rsa_verify(
    target,
    iterations,
    data,
    data_len,
    e,
    n,
    n_len,
    sig,
    sig_len,
    padding,
    hashing,
    cfg,
    trigger,
    reset=False,
):
    asymfi = OTFIAsymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        asymfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        asymfi.handle_rsa_verify(
            data,
            data_len,
            e,
            n,
            n_len,
            sig,
            sig_len,
            padding,
            hashing,
            cfg,
            trigger,
        )
        response = target.read_response()
    return response


def char_prime_generation(target, iterations, e, cfg, trigger, reset=False):
    asymfi = OTFIAsymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        asymfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        asymfi.handle_prime_generation(e, cfg, trigger)
        response = target.read_response()
    return response


def char_p256_base_mult(target, iterations, scalar, cfg, trigger, reset=False):
    asymfi = OTFIAsymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        asymfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        asymfi.handle_p256_base_mult(scalar, cfg, trigger)
        response = target.read_response()
    return response


def char_p256_point_mult(
    target, iterations, scalar_alice, scalar_bob, cfg, trigger, reset=False
):
    asymfi = OTFIAsymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        asymfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        asymfi.handle_p256_point_mult(scalar_alice, scalar_bob, cfg, trigger)
        response = target.read_response()
    return response


def char_p256_ecdh(
    target, iterations, private_key, public_x, public_y, cfg, trigger, reset=False
):
    asymfi = OTFIAsymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        asymfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        asymfi.handle_p256_ecdh(private_key, public_x, public_y, cfg, trigger)
        response = target.read_response()
    return response


def char_p256_sign(
    target, iterations, scalar, pubx, puby, message, cfg, trigger, reset=False
):
    asymfi = OTFIAsymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        asymfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        asymfi.handle_p256_sign(scalar, pubx, puby, message, cfg, trigger)
        response = target.read_response()
    return response


def char_p256_verify(
    target, iterations, pubx, puby, r, s, message, cfg, trigger, reset=False
):
    asymfi = OTFIAsymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        asymfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        asymfi.handle_p256_verify(pubx, puby, r, s, message, cfg, trigger)
        response = target.read_response()
    return response


def char_p384_base_mult(target, iterations, scalar, cfg, trigger, reset=False):
    asymfi = OTFIAsymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        asymfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        asymfi.handle_p384_base_mult(scalar, cfg, trigger)
        response = target.read_response()
    return response


def char_p384_point_mult(
    target, iterations, scalar_alice, scalar_bob, cfg, trigger, reset=False
):
    asymfi = OTFIAsymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        asymfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        asymfi.handle_p384_point_mult(scalar_alice, scalar_bob, cfg, trigger)
        response = target.read_response()
    return response


def char_p384_ecdh(
    target, iterations, private_key, public_x, public_y, cfg, trigger, reset=False
):
    asymfi = OTFIAsymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        asymfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        asymfi.handle_p384_ecdh(private_key, public_x, public_y, cfg, trigger)
        response = target.read_response()
    return response


def char_p384_sign(
    target, iterations, scalar, pubx, puby, message, cfg, trigger, reset=False
):
    asymfi = OTFIAsymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        asymfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        asymfi.handle_p384_sign(scalar, pubx, puby, message, cfg, trigger)
        response = target.read_response()
    return response


def char_p384_verify(
    target, iterations, pubx, puby, r, s, message, cfg, trigger, reset=False
):
    asymfi = OTFIAsymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        asymfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        asymfi.handle_p384_verify(pubx, puby, r, s, message, cfg, trigger)
        response = target.read_response()
    return response
