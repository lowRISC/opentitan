# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "opentitan_test",
    "verilator_params",
)

def strap_combination(strap):
    settings = {
        "value": strap,
        "fail": "PASS|FAIL",
    }
    if strap == 63:
        # Strap value 63 is always bootstrap.
        # The ROM emits `bootstrap:1`.
        # The TestROM emits `Boot strap requested`.
        settings["pass"] = "bootstrap:1|Boot strap requested"
    else:
        # All other values:
        # For ROM, the test program is unsigned: we get a boot fault value.
        # The test prints the decoded strap value.
        settings["pass"] = r"BFV:[^\r\n]*\r|sw_strap={}".format(strap)
    for i in range(3):
        val = (strap >> (2 * i)) & 3
        if val == 0:
            settings["b{}_mode".format(i)] = "PushPull"
            settings["b{}_pull".format(i)] = "None"
            settings["b{}_value".format(i)] = "false"
        elif val == 1:
            settings["b{}_mode".format(i)] = "Input"
            settings["b{}_pull".format(i)] = "PullDown"
            settings["b{}_value".format(i)] = "false"  # Don't care
        elif val == 2:
            settings["b{}_mode".format(i)] = "Input"
            settings["b{}_pull".format(i)] = "PullUp"
            settings["b{}_value".format(i)] = "true"  # Don't care
        elif val == 3:
            settings["b{}_mode".format(i)] = "PushPull"
            settings["b{}_pull".format(i)] = "None"
            settings["b{}_value".format(i)] = "true"
    return settings

def strap_combination_test(name, rom, value, evaluator = None, tags = [], extra_verilator_args = ""):
    settings = strap_combination(value)
    if evaluator == None:
        evaluator = "console --exit-success=\"{pass}\" --exit-failure=\"{fail}\""
    settings["evaluator"] = evaluator.format(**settings)

    opentitan_test(
        name = name,
        tags = tags,
        exec_env = {"//hw/top_earlgrey:sim_verilator": None},
        verilator = verilator_params(
            rom = rom,
            binaries = {
                # The test expects an unsigned binary.
                "//sw/device/silicon_creator/rom/e2e:empty_test_slot_a_sim_verilator_scr_vmem64": "firmware",
            },
            test_cmd = extra_verilator_args + """
                --exec="gpio set IOC0 --mode={b0_mode} --value={b0_value} --pull={b0_pull}"
                --exec="gpio set IOC1 --mode={b1_mode} --value={b1_value} --pull={b1_pull}"
                --exec="gpio set IOC2 --mode={b2_mode} --value={b2_value} --pull={b2_pull}"
                --exec='{evaluator}'
                "no-op"
            """.format(**settings),
        ),
    )

def strap_combinations_test(name, rom, tags = [], skip_value = []):
    all_tests = []
    for value in range(64):
        if value in skip_value:
            continue
        n = "{}_{}".format(name, value)
        all_tests.append(n)

        # Strap value 60 triggers a wait for RMA entry and needs to be treated
        # as a special case:
        # - The verilated model doesn't seem to flush stdout very often, so as
        #   an optimization, we tell the simulation to quit after 200000
        #   cycles.
        # - Since we only want to test that the RMA strap value triggers the
        #   spinloop codepath _and_ since we won't actually enter RMA, we
        #   expect the ROM to hit an `unimp` instruction and trigger an
        #   Illegal Instruction fault, which will be visible on verilated
        #   model's stdout.
        if "test_rom" not in rom and value == 60:
            extra_verilator_args = "--verilator-args=--term-after-cycles=200000"
            evaluator = "transport verilator-watch --timeout=300s \"Illegal instruction\""
        else:
            extra_verilator_args = ""
            evaluator = None

        strap_combination_test(
            name = n,
            rom = rom,
            value = value,
            evaluator = evaluator,
            tags = tags,
            extra_verilator_args = extra_verilator_args,
        )

    native.test_suite(
        name = name,
        tests = all_tests,
        tags = tags,  # Add tags so the test_suite may be filtered appropriately.
        # If tests aren't to share a common set of tags, they should be removed
        # here and replaced with a manual tag, so the test_suite can contain
        # the appropriate tests, but will not match filters innapropriately.
    )
