# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from sw.host.penetrationtests.python.fi.communication.fi_crypto_commands import OTFICrypto
from sw.host.penetrationtests.python.util import common_library


def char_aes(target, iterations, plaintext, key, trigger, reset = False):
    cryptofi = OTFICrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        cryptofi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        if trigger == 0:
            # Trigger over loading the key
            cryptofi.crypto_aes_key(plaintext, key)
        if trigger == 1:
            # Trigger over loading the plaintext
            cryptofi.crypto_aes_plaintext(plaintext, key)
        if trigger == 2:
            # Trigger over encryption
            cryptofi.crypto_aes_encrypt(plaintext, key)
        if trigger == 3:
            # Trigger over reading the ciphertext
            cryptofi.crypto_aes_ciphertext(plaintext, key)
        response = target.read_response()
    # Return the ciphertext that is read out
    return response


def char_kmac(target, iterations, trigger, reset = False):
    cryptofi = OTFICrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        cryptofi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        if trigger == 0:
            # Trigger over loading the key
            cryptofi.crypto_kmac_key()
        if trigger == 1:
            # Trigger over loading the input
            cryptofi.crypto_kmac_absorb()
        if trigger == 2:
            # Trigger over the mac itself
            cryptofi.crypto_kmac_static()
        if trigger == 3:
            # Trigger over reading the output
            cryptofi.crypto_kmac_squeeze()
        response = target.read_response()
    # Return the result that is read out
    return response


def char_kmac_state(target, iterations, reset = False):
    cryptofi = OTFICrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        cryptofi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        cryptofi.crypto_kmac_state()
        response = target.read_response()
    # Return the result that is read out
    return response


def char_hmac(
    target,
    iterations,
    msg,
    key,
    trigger,
    enable_hmac,
    message_endianness_big,
    digest_endianness_big,
    key_endianness_big,
    hash_mode,
    reset = False
):
    cryptofi = OTFICrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        cryptofi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        cryptofi.crypto_hmac(
            msg,
            key,
            trigger,
            enable_hmac,
            message_endianness_big,
            digest_endianness_big,
            key_endianness_big,
            hash_mode,
        )
        response = target.read_response()
    # Return the result that is read out
    return response


def char_shadow_reg_access(target, iterations, reset = False):
    cryptofi = OTFICrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        cryptofi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        cryptofi.crypto_shadow_reg_access()
        response = target.read_response()
    # Return the result that is read out
    return response


def char_shadow_reg_read(target, iterations, reset = False):
    cryptofi = OTFICrypto(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, sensors, alerts, owner_page, boot_log, boot_measurements, version = (
        cryptofi.init(alert_config=common_library.default_fpga_friendly_alert_config)
    )
    for _ in range(iterations):
        cryptofi.crypto_shadow_reg_read()
        response = target.read_response()
    # Return the result that is read out
    return response
