# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:opentitan_test.bzl",
    "opentitan_functest",
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
            settings["b{}_value".format(i)] = "false"
        elif val == 1:
            settings["b{}_mode".format(i)] = "WeakPushPull"
            settings["b{}_value".format(i)] = "false"
        elif val == 2:
            settings["b{}_mode".format(i)] = "WeakPushPull"
            settings["b{}_value".format(i)] = "true"
        elif val == 3:
            settings["b{}_mode".format(i)] = "PushPull"
            settings["b{}_value".format(i)] = "true"
    return settings

def strap_combination_test(name, rom, value, evaluator = None, tags = [], extra_verilator_args = []):
    settings = strap_combination(value)
    if evaluator == None:
        evaluator = r"console --exit-success=\"{pass}\" --exit-failure=\"{fail}\""
    evaluator = evaluator.format(**settings)

    opentitan_functest(
        name = name,
        srcs = ["sw_straps_test.c"],
        signed = False,
        tags = tags,
        targets = [
            "verilator",
        ],
        verilator = verilator_params(
            rom = rom,
            test_cmds = extra_verilator_args + [
                "--exec=\"gpio set-mode IOC0 {b0_mode}\"".format(**settings),
                "--exec=\"gpio set-mode IOC1 {b1_mode}\"".format(**settings),
                "--exec=\"gpio set-mode IOC2 {b2_mode}\"".format(**settings),
                "--exec=\"gpio write IOC0 {b0_value}\"".format(**settings),
                "--exec=\"gpio write IOC1 {b1_value}\"".format(**settings),
                "--exec=\"gpio write IOC2 {b2_value}\"".format(**settings),
                "--exec=\"{}\"".format(evaluator),
                "no-op",
            ],
        ),
        deps = [
            "//sw/device/lib/base:status",
            "//sw/device/lib/dif:gpio",
            "//sw/device/lib/dif:pinmux",
            "//sw/device/lib/testing:pinmux_testutils",
            "//sw/device/lib/testing/test_framework:ottf_main",
        ],
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
            extra_verilator_args = ["--verilator-args=--term-after-cycles=200000"]
            evaluator = r"transport verilator-watch --timeout=300s \"Illegal instruction\""
        else:
            extra_verilator_args = []
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
    )
