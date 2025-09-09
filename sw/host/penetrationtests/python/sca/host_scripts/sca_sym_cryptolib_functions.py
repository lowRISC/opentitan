# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from sw.host.penetrationtests.python.sca.communication.sca_sym_cryptolib_commands import (
    OTSymCrypto,
)
from sw.host.penetrationtests.python.sca.communication.sca_prng_commands import OTPRNG


def char_aes_fvsr_plaintext(
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
    num_iterations,
    reset=False,
):
    symsca = OTSymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = symsca.init()
    # Set the internal prng
    ot_prng = OTPRNG(target=target)
    ot_prng.seed_prng([1, 0, 0, 0])
    for _ in range(iterations):
        symsca.handle_aes_fvsr_plaintext(
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
            num_iterations,
        )
        response = target.read_response()
    return response


def char_aes_daisy(
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
    num_iterations,
    reset=False,
):
    symsca = OTSymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = symsca.init()

    for _ in range(iterations):
        symsca.handle_aes_daisy(
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
            num_iterations,
        )
        response = target.read_response()
    return response


def char_cmac_fvsr_plaintext(
    target,
    iterations,
    data,
    data_len,
    key,
    key_len,
    iv,
    cfg,
    trigger,
    num_iterations,
    reset=False,
):
    symsca = OTSymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = symsca.init()
    # Set the internal prng
    ot_prng = OTPRNG(target=target)
    ot_prng.seed_prng([1, 0, 0, 0])
    for _ in range(iterations):
        symsca.handle_cmac_fvsr_plaintext(
            data,
            data_len,
            key,
            key_len,
            iv,
            cfg,
            trigger,
            num_iterations,
        )
        response = target.read_response()
    return response


def char_cmac_daisy(
    target,
    iterations,
    data,
    data_len,
    key,
    key_len,
    iv,
    cfg,
    trigger,
    num_iterations,
    reset=False,
):
    symsca = OTSymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = symsca.init()

    for _ in range(iterations):
        symsca.handle_cmac_daisy(
            data,
            data_len,
            key,
            key_len,
            iv,
            cfg,
            trigger,
            num_iterations,
        )
        response = target.read_response()
    return response


def char_gcm_fvsr_plaintext(
    target,
    iterations,
    data,
    data_len,
    key,
    key_len,
    aad,
    aad_len,
    iv,
    cfg,
    trigger,
    num_iterations,
    reset=False,
):
    symsca = OTSymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = symsca.init()
    # Set the internal prng
    ot_prng = OTPRNG(target=target)
    ot_prng.seed_prng([1, 0, 0, 0])
    for _ in range(iterations):
        symsca.handle_gcm_fvsr_plaintext(
            data,
            data_len,
            key,
            key_len,
            aad,
            aad_len,
            iv,
            cfg,
            trigger,
            num_iterations,
        )
        response = target.read_response()
    return response


def char_gcm_daisy(
    target,
    iterations,
    data,
    data_len,
    key,
    key_len,
    aad,
    aad_len,
    iv,
    cfg,
    trigger,
    num_iterations,
    reset=False,
):
    symsca = OTSymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = symsca.init()

    for _ in range(iterations):
        symsca.handle_gcm_daisy(
            data,
            data_len,
            key,
            key_len,
            aad,
            aad_len,
            iv,
            cfg,
            trigger,
            num_iterations,
        )
        response = target.read_response()
    return response


def char_hmac_fvsr_plaintext(
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
    num_iterations,
    reset=False,
):
    symsca = OTSymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = symsca.init()
    # Set the internal prng
    ot_prng = OTPRNG(target=target)
    ot_prng.seed_prng([1, 0, 0, 0])
    for _ in range(iterations):
        symsca.handle_hmac_fvsr_plaintext(
            data,
            data_len,
            key,
            key_len,
            hash_mode,
            mode,
            cfg,
            trigger,
            num_iterations,
        )
        response = target.read_response()
    return response


def char_hmac_daisy(
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
    num_iterations,
    reset=False,
):
    symsca = OTSymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = symsca.init()
    # Set the internal prng
    ot_prng = OTPRNG(target=target)
    ot_prng.seed_prng([1, 0, 0, 0])
    for _ in range(iterations):
        symsca.handle_hmac_daisy(
            data,
            data_len,
            key,
            key_len,
            hash_mode,
            mode,
            cfg,
            trigger,
            num_iterations,
        )
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
    num_segments,
    reset=False,
):
    symsca = OTSymCrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = (
        symsca.init()
    )
    # In this test, we do not trigger the reseeding
    symsca.handle_drbg_reseed(
        entropy, entropy_len, nonce, nonce_len, reseed_interval, mode, 0, 0
    )
    response = target.read_response()
    for _ in range(iterations):
        # In this test, we do not add to the nonce
        symsca.handle_drbg_generate([0], 0, data_len, mode, cfg, trigger, num_segments)
        response = target.read_response()
    return response
