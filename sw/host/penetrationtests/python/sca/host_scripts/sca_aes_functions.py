# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from sw.host.penetrationtests.python.sca.communication.sca_aes_commands import OTAES
from sw.host.penetrationtests.python.sca.communication.sca_prng_commands import OTPRNG
from sw.host.penetrationtests.python.sca.communication.sca_trigger_commands import OTTRIGGER


def char_aes_single_encrypt(target, iterations, fpga, masking, key, text, reset = False):
    aessca = OTAES(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = aessca.init(fpga)

    # Check whether we enable the masking
    # Note that disabled masking might create errors on production chips
    if masking:
        lfsr_seed = 1
    else:
        lfsr_seed = 0
    aessca.seed_lfsr(lfsr_seed.to_bytes(4, "little"))

    # Set the trigger
    triggersca = OTTRIGGER(target)
    triggersca.select_trigger(int(not fpga))

    for _ in range(iterations):
        aessca.single_encrypt(key, text)
        response = target.read_response()
    return response


def char_aes_batch_daisy_chain(
    target, iterations, num_segments, fpga, masking, key, text, reset = False
):
    aessca = OTAES(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = aessca.init(fpga)

    # Check whether we enable the masking
    # Note that disabled masking might create errors on production chips
    if masking:
        lfsr_seed = 1
    else:
        lfsr_seed = 0
    aessca.seed_lfsr(lfsr_seed.to_bytes(4, "little"))

    # Set the trigger
    triggersca = OTTRIGGER(target)
    triggersca.select_trigger(int(not fpga))

    # This way of coding does always start from the same plaintext
    # and thus always encrypts the same for all iterations.
    # Instead, one can set a random text every loop here.
    for _ in range(iterations):
        aessca.batch_daisy_chain(num_segments, key, text)
        response = target.read_response()
    return response


def char_aes_batch_fvsr_data(
    target, iterations, num_segments, fpga, masking, key, text, reset = False
):
    aessca = OTAES(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = aessca.init(fpga)

    # Check whether we enable the masking
    # Note that disabled masking might create errors on production chips
    if masking:
        lfsr_seed = 1
    else:
        lfsr_seed = 0
    aessca.seed_lfsr(lfsr_seed.to_bytes(4, "little"))

    # Set the trigger
    triggersca = OTTRIGGER(target)
    triggersca.select_trigger(int(not fpga))

    # Set the internal prng
    ot_prng = OTPRNG(target=target)
    ot_prng.seed_prng([1, 0, 0, 0])

    for _ in range(iterations):
        aessca.batch_fvsr_data(num_segments, key, text)
        response = target.read_response()
    return response


def char_aes_batch_fvsr_key(target, iterations, num_segments, fpga, masking, key, reset = False):
    aessca = OTAES(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = aessca.init(fpga)

    # Check whether we enable the masking
    # Note that disabled masking might create errors on production chips
    if masking:
        lfsr_seed = 1
    else:
        lfsr_seed = 0
    aessca.seed_lfsr(lfsr_seed.to_bytes(4, "little"))

    # Set the trigger
    triggersca = OTTRIGGER(target)
    triggersca.select_trigger(int(not fpga))

    # Set the internal prng
    ot_prng = OTPRNG(target=target)
    ot_prng.seed_prng([1, 0, 0, 0])

    for _ in range(iterations):
        aessca.batch_fvsr_key(num_segments, key)
        response = target.read_response()
    return response


def char_aes_batch_random(target, iterations, num_segments, fpga, masking, key, reset = False):
    aessca = OTAES(target)

    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
        # Initialize our chip and catch its output
        device_id, owner_page, boot_log, boot_measurements, version = aessca.init(fpga)

    # Check whether we enable the masking
    # Note that disabled masking might create errors on production chips
    if masking:
        lfsr_seed = 1
    else:
        lfsr_seed = 0
    aessca.seed_lfsr(lfsr_seed.to_bytes(4, "little"))

    # Set the trigger
    triggersca = OTTRIGGER(target)
    triggersca.select_trigger(int(not fpga))

    # Set the internal prng
    ot_prng = OTPRNG(target=target)
    ot_prng.seed_prng([1, 0, 0, 0])

    for _ in range(iterations):
        aessca.batch_random(num_segments, key)
        response = target.read_response()
    return response
