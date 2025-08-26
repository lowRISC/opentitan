# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from sw.host.penetrationtests.python.sca.communication.sca_kmac_commands import OTKMAC
from sw.host.penetrationtests.python.sca.communication.sca_prng_commands import OTPRNG
from sw.host.penetrationtests.python.sca.communication.sca_trigger_commands import OTTRIGGER


def char_kmac_single(target, iterations, fpga, masking, key, text, reset = False):
    kmacsca = OTKMAC(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = kmacsca.init(fpga)

    if masking:
        lfsr_seed = [0, 1, 2, 3]
    else:
        lfsr_seed = [0, 0, 0, 0]
    kmacsca.write_lfsr_seed(lfsr_seed)

    kmacsca.write_key(key)

    # Set the trigger
    triggersca = OTTRIGGER(target)
    triggersca.select_trigger(int(not fpga))

    for _ in range(iterations):
        kmacsca.absorb(text, len(text))
        response = target.read_response()
    return response


def char_kmac_batch_daisy_chain(
    target, iterations, num_segments, fpga, masking, key, text, reset = False
):
    kmacsca = OTKMAC(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = kmacsca.init(fpga)

    if masking:
        lfsr_seed = [0, 1, 2, 3]
    else:
        lfsr_seed = [0, 0, 0, 0]
    kmacsca.write_lfsr_seed(lfsr_seed)

    # Set the trigger
    triggersca = OTTRIGGER(target)
    triggersca.select_trigger(int(not fpga))

    for _ in range(iterations):
        kmacsca.absorb_daisy_chain(text, key, num_segments)
        response = target.read_response()
    return response


def char_kmac_batch(target, iterations, num_segments, fpga, masking, key, reset = False):
    kmacsca = OTKMAC(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = kmacsca.init(fpga)

    if masking:
        lfsr_seed = [0, 1, 2, 3]
    else:
        lfsr_seed = [0, 0, 0, 0]
    kmacsca.write_lfsr_seed(lfsr_seed)

    # Set the trigger
    triggersca = OTTRIGGER(target)
    triggersca.select_trigger(int(not fpga))

    # Set the internal prng
    ot_prng = OTPRNG(target=target)
    ot_prng.seed_prng([1, 0, 0, 0])

    kmacsca.fvsr_key_set(key, len(key))

    for _ in range(iterations):
        kmacsca.absorb_batch(num_segments)
        response = target.read_response()
    return response
