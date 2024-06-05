# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//lib:sets.bzl", "sets")

# List of execution environments that are always enabled in CI.
_ALWAYS_RUN_IN_CI = [
    "//hw/top_earlgrey:sim_verilator",
    "//hw/top_earlgrey:sim_dv",
]

# List of execution environments among which only one should run. The list
# is sorted by priority: the first available will be picked.
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
    that needs to run in CI.
    """
    exec_env_sets = sets.make(exec_envs)
    the_one_in_ci = None
    for env in _ONLY_RUN_ONE_IN_CI_SORTED:
        if sets.contains(exec_env_sets, env):
            the_one_in_ci = env
            break

    run_in_ci = [env for env in _ALWAYS_RUN_IN_CI if sets.contains(exec_env_sets, env)]
    if the_one_in_ci != None:
        run_in_ci.append(the_one_in_ci)
    return run_in_ci
