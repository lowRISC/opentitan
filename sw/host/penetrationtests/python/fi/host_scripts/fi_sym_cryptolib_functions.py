# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from sw.host.penetrationtests.python.fi.communication.fi_sym_cryptolib_commands import (
    OTFISymCrypto,
)
from sw.host.penetrationtests.python.util import common_library


def char_aes(
    target,
    iterations,
    data,
    data_len,
    key,
    key_len,
    iv,
    padding,
    mode,
    op_enc,
    cfg,
    trigger,
    reset=False,
):
    symfi = OTFISymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    (
        device_id,
        sensors,
        alerts,
        owner_page,
        boot_log,
        boot_measurements,
        version,
        cryptolib_version,
    ) = symfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    for _ in range(iterations):
        symfi.handle_aes(
            data, data_len, key, key_len, iv, padding, mode, op_enc, cfg, trigger
        )
        response = target.read_response()
    return response


def char_cmac(
    target, iterations, data, data_len, key, key_len, iv, cfg, trigger, reset=False
):
    symfi = OTFISymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    (
        device_id,
        sensors,
        alerts,
        owner_page,
        boot_log,
        boot_measurements,
        version,
        cryptolib_version,
    ) = symfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    for _ in range(iterations):
        symfi.handle_cmac(data, data_len, key, key_len, iv, cfg, trigger)
        response = target.read_response()
    return response


def char_gcm(
    target,
    iterations,
    data,
    data_len,
    key,
    key_len,
    aad,
    aad_len,
    tag,
    tag_len,
    iv,
    cfg,
    trigger,
    reset=False,
):
    symfi = OTFISymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    (
        device_id,
        sensors,
        alerts,
        owner_page,
        boot_log,
        boot_measurements,
        version,
        cryptolib_version,
    ) = symfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    for _ in range(iterations):
        symfi.handle_gcm(
            data, data_len, key, key_len, aad, aad_len, tag, tag_len, iv, cfg, trigger
        )
        response = target.read_response()
    return response


def char_hmac(
    target,
    iterations,
    data,
    data_len,
    key,
    key_len,
    hash_mode,
    mode,
    cfg,
    trigger,
    reset=False,
):
    symfi = OTFISymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    (
        device_id,
        sensors,
        alerts,
        owner_page,
        boot_log,
        boot_measurements,
        version,
        cryptolib_version,
    ) = symfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    for _ in range(iterations):
        symfi.handle_hmac(data, data_len, key, key_len, hash_mode, mode, cfg, trigger)
        response = target.read_response()
    return response


def char_drbg(
    target,
    iterations,
    entropy,
    entropy_len,
    nonce,
    nonce_len,
    reseed_interval,
    data_len,
    mode,
    cfg,
    trigger,
    reset=False,
):
    symfi = OTFISymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    (
        device_id,
        sensors,
        alerts,
        owner_page,
        boot_log,
        boot_measurements,
        version,
        cryptolib_version,
    ) = symfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    # In this test, we do not trigger the reseeding
    symfi.handle_drbg_reseed(
        entropy, entropy_len, nonce, nonce_len, reseed_interval, mode, 0, 0
    )
    response = target.read_response()
    for _ in range(iterations):
        # In this test, we do not add to the nonce
        symfi.handle_drbg_generate([0], 0, data_len, mode, cfg, trigger)
        response = target.read_response()
    return response


def char_trng(target, iterations, mode, cfg, trigger, reset=False):
    symfi = OTFISymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    (
        device_id,
        sensors,
        alerts,
        owner_page,
        boot_log,
        boot_measurements,
        version,
        cryptolib_version,
    ) = symfi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    # In this test, we do not trigger the init
    symfi.handle_trng_init(mode, 0, 0)
    response = target.read_response()
    for _ in range(iterations):
        symfi.handle_trng_generate(cfg, trigger)
        response = target.read_response()
    return response
