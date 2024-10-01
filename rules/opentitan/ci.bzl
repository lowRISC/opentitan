# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//lib:sets.bzl", "sets")

# List of execution environments among which only one should run. The list
# is sorted by priority: the first available will be picked.
#
# Important note: since only one of the those will be chosen, it is important
# that every one of the execution environments be run in some CI job, otherwise
# some tests will not run at all in CI.
_ONLY_RUN_ONE_IN_CI_SORTED = [
    "//hw/top_earlgrey:fpga_cw310_sival_rom_ext",
    "//hw/top_earlgrey:fpga_cw310_rom_ext",
    "//hw/top_earlgrey:fpga_cw310_sival",
    "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys",
    "//hw/top_earlgrey:fpga_cw310_test_rom",
    "//hw/top_earlgrey:fpga_cw340_sival_rom_ext",
    "//hw/top_earlgrey:fpga_cw340_sival",
    "//hw/top_earlgrey:fpga_cw340_rom_ext",
    "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys",
    "//hw/top_earlgrey:fpga_cw340_test_rom",
]

def ci_orchestrator(test_name, exec_envs):
    """
    Given a list of execution environments, return the subset of this list
    that should be skipped in CI.
    """
    exec_env_sets = sets.make(exec_envs)
    only_one_run_sets = sets.make(_ONLY_RUN_ONE_IN_CI_SORTED)
    # List environments among which only one must run.
    skip_in_ci = sets.to_list(sets.intersection(exec_env_sets, only_one_run_sets))
    # Choose one at random.
    if len(skip_in_ci) > 0:
        # FIXME This is not good randomness
        the_one_index = hash(test_name) % len(skip_in_ci)
        the_one = skip_in_ci.pop(the_one_index)

    return skip_in_ci
