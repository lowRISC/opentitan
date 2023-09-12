# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "@lowrisc_opentitan//rules:rv.bzl",
    _OPENTITAN_CPU = "OPENTITAN_CPU",
    _OPENTITAN_PLATFORM = "OPENTITAN_PLATFORM",
    _opentitan_transition = "opentitan_transition",
)
load(
    "@lowrisc_opentitan//rules/opentitan:cc.bzl",
    _opentitan_binary = "opentitan_binary",
    _opentitan_test = "opentitan_test",
)
load(
    "@lowrisc_opentitan//rules/opentitan:fpga_cw310.bzl",
    _fpga_cw310 = "fpga_cw310",
)
load(
    "@lowrisc_opentitan//rules/opentitan:sim_verilator.bzl",
    _sim_verilator = "sim_verilator",
)

"""Rules to build OpenTitan for the RISC-V target"""

# Re-exports of names from transition.bzl; many files in the repo use opentitan.bzl
# to get to them.
OPENTITAN_CPU = _OPENTITAN_CPU
OPENTITAN_PLATFORM = _OPENTITAN_PLATFORM
opentitan_transition = _opentitan_transition

opentitan_binary = _opentitan_binary
fpga_cw310 = _fpga_cw310
sim_verilator = _sim_verilator

def opentitan_test(
        name,
        srcs,
        deps = [],
        copts = [],
        defines = [],
        local_defines = [],
        includes = [],
        linkopts = [],
        exec_env = []):
    #args = [],
    #bitstream = None,
    #rom = None,
    #otp = None,
    #data = [],
    #param = {},
    #test_harness = None
    all_tests = []
    for env in exec_env:
        (_, suffix) = env.split(":")
        test_name = "{}_{}".format(name, suffix)
        all_tests.append(":" + test_name)
        _opentitan_test(
            name = test_name,
            srcs = srcs,
            deps = deps,
            copts = copts,
            defines = defines,
            local_defines = local_defines,
            includes = includes,
            linkopts = linkopts,
            exec_env = env,
            naming_convention = "{name}",
            tags = ["local"],
        )
    native.test_suite(
        name = name,
        tests = all_tests,
        tags = ["manual"],
    )
