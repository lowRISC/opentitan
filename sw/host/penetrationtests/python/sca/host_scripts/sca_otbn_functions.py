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
