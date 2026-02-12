# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from sw.host.penetrationtests.python.sca.communication.sca_sha3_commands import OTSHA3
from sw.host.penetrationtests.python.sca.communication.sca_prng_commands import OTPRNG
from sw.host.penetrationtests.python.sca.communication.sca_trigger_commands import OTTRIGGER


def char_sha3_single_absorb(target, iterations, fpga, masking, text, reset = False):
    sha3sca = OTSHA3(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = sha3sca.init(fpga)

    if masking:
        lfsr_seed = [0, 1, 2, 3]
        sha3sca.write_lfsr_seed(lfsr_seed)
    else:
        sha3sca.set_mask_off()

    # Set the trigger
    triggersca = OTTRIGGER(target)
    triggersca.select_trigger(int(not fpga))

    for _ in range(iterations):
        sha3sca.absorb(text, len(text))
        response = target.read_response()
    return response


def char_sha3_batch_absorb(target, iterations, num_segments, fpga, masking, text, reset = False):
    sha3sca = OTSHA3(target)
    if reset:
        target.reset_target()
        # Clear the output from the reset
        target.dump_all()
    # Initialize our chip and catch its output
    device_id, owner_page, boot_log, boot_measurements, version = sha3sca.init(fpga)

    if masking:
        lfsr_seed = [0, 1, 2, 3]
        sha3sca.write_lfsr_seed(lfsr_seed)
    else:
        sha3sca.set_mask_off()

    # Set the internal prng
    ot_prng = OTPRNG(target=target)
    ot_prng.seed_prng([1, 0, 0, 0])

    # Set the trigger
    triggersca = OTTRIGGER(target)
    triggersca.select_trigger(int(not fpga))

    sha3sca.fvsr_fixed_msg_set(text, len(text))

    for _ in range(iterations):
        sha3sca.absorb_batch(num_segments)
        response = target.read_response()
    return response
