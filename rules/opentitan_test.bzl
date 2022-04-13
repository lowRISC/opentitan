# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "opentitan_flash_binary", "opentitan_rom_binary")
load("@bazel_skylib//lib:shell.bzl", "shell")

_EXIT_SUCCESS = r"PASS.*\n"
_EXIT_FAILURE = r"(FAIL|FAULT).*\n"

_BASE_PARAMS = {
    "args": [],
    "data": [],
    "local": True,
    # TODO: the name of this target should be HW target generic
    "otp": "//hw/ip/otp_ctrl/data:rma_image_verilator",
    "rom": "//sw/device/lib/testing/test_rom:test_rom_{}_scr_vmem",
    "tags": [],
    "test_runner": "//util:opentitantool_test_runner.sh",
    "timeout": "moderate",  # 5 minutes
}

_OTTF_DEPS = [
    "//sw/device/lib/arch:device",
    "//sw/device/lib/base:macros",
    "//sw/device/lib/base:csr",
    "//sw/device/lib/base:mmio",
    "//sw/device/lib/runtime:hart",
    "//sw/device/lib/runtime:log",
    "//sw/device/lib/runtime:print",
    "//sw/device/lib/crt",
    "//sw/device/lib/testing/test_framework:ottf_start",
    "//sw/device/lib/testing/test_framework:ottf",
    "//sw/device/lib/base:mmio",
]

def dv_params(
        # Base Parameters
        args = _BASE_PARAMS["args"] + [
            "$(location {dvsim_config})",
        ],
        data = _BASE_PARAMS["data"],
        local = _BASE_PARAMS["local"],
        otp = _BASE_PARAMS["otp"],
        rom = _BASE_PARAMS["rom"].format("sim_dv"),
        tags = _BASE_PARAMS["tags"],
        timeout = _BASE_PARAMS["timeout"],
        # DV-specific Parameters
        bootstrap_sw = False,  # Default to backdoor loading.
        dvsim_config = "//hw/top_earlgrey/dv:chip_sim_cfg.hjson",
        **kwargs):
    """A macro to create DV sim parameters for OpenTitan functional tests.

    This macro emits a dictionary of parameters which are pasted into the DV
    simulation specific test rule.

    Args:
        @param args: Extra arguments to pass to the test runner (`dvsim.py`).
        @param data: Data dependencies of the test.
        @param local: Whether the test should be run locally without sandboxing.
        @param otp: The OTP image to use.
        @param rom: The ROM image to use.
        @param tags: The test tags to apply to the test rule.
        @param timeout: The timeout to apply to the test rule.
        @param bootstrap_sw: Whether to load flash via bootstrap.
        @param dvsim_config: The dvsim.py Hjson config file for the toplevel.
    """
    required_args = [
        "-i",
        "chip_sw_{name}",
    ]
    required_data = [
        dvsim_config,
        "//util/dvsim",
        "//hw:all_files",
    ]
    required_tags = ["dv"]
    kwargs.update(
        args = required_args + args,
        data = required_data + data,
        local = local,
        otp = otp,
        rom = rom,
        tags = required_tags + tags,
        test_runner = "//util:dvsim_test_runner.sh",
        timeout = timeout,
        bootstrap_sw = bootstrap_sw,
        dvsim_config = dvsim_config,
    )
    return kwargs

def verilator_params(
        # Base Parameters
        args = _BASE_PARAMS["args"] + [
            "console",
            "--exit-failure=" + shell.quote(_EXIT_FAILURE),
            "--exit-success=" + shell.quote(_EXIT_SUCCESS),
            "--timeout=3600s",
        ],
        data = _BASE_PARAMS["data"],
        local = _BASE_PARAMS["local"],
        otp = _BASE_PARAMS["otp"],
        rom = _BASE_PARAMS["rom"].format("sim_verilator"),
        tags = _BASE_PARAMS["tags"] + ["cpu:4"],
        timeout = _BASE_PARAMS["timeout"],
        # Verilator-specific Parameters
        # None
        **kwargs):
    """A macro to create Verilator sim parameters for OpenTitan functional tests.

    This macro emits a dictionary of parameters which are pasted into the
    Verilator simulation specific test rule.

    Args:
        @param args: Extra arguments to pass to the test runner (`opentitantool`).
        @param data: Data dependencies of the test.
        @param local: Whether the test should be run locally without sandboxing.
        @param otp: The OTP image to use.
        @param rom: The ROM image to use.
        @param tags: The test tags to apply to the test rule.
        @param timeout: The timeout to apply to the test rule.
    """
    required_args = [
        "--rcfile=",
        "--logging=info",
        "--interface=verilator",
        "--conf=sw/host/opentitantool/config/opentitan_verilator.json",
        "--verilator-bin=$(location //hw:verilator)/sim-verilator/Vchip_sim_tb",
        "--verilator-rom=$(location {rom})",
        "--verilator-flash=$(location {flash})",
        "--verilator-otp=$(location {otp})",
    ]
    required_data = [
        "//sw/host/opentitantool:test_resources",
        "//hw:verilator",
    ]
    required_tags = ["verilator"]
    kwargs.update(
        args = required_args + args,
        data = required_data + data,
        local = local,
        otp = otp,
        rom = rom,
        tags = required_tags + tags,
        test_runner = _BASE_PARAMS["test_runner"],
        timeout = timeout,
    )
    return kwargs

def cw310_params(
        # Base Parameters
        args = _BASE_PARAMS["args"] + [
            "--exec=\"console -q -t0s\"",
            "--exec=\"bootstrap $(location {flash})\"",
            "console",
            "--exit-failure=" + shell.quote(_EXIT_FAILURE),
            "--exit-success=" + shell.quote(_EXIT_SUCCESS),
            "--timeout=3600s",
        ],
        data = _BASE_PARAMS["data"],
        local = _BASE_PARAMS["local"],
        otp = _BASE_PARAMS["otp"],
        rom = _BASE_PARAMS["rom"].format("fpga_cw310"),
        tags = _BASE_PARAMS["tags"] + ["cpu:4"],
        timeout = _BASE_PARAMS["timeout"],
        # CW310-specific Parameters
        # None
        **kwargs):
    """A macro to create CW310 parameters for OpenTitan functional tests.

    This macro emits a dictionary of parameters which are pasted into the
    ChipWhisperer-310 FPGA specific test rule.

    Args:
        @param args: Extra arguments to pass the test runner `opentitantool`.
        @param data: Data dependencies of the test.
        @param local: Whether the test should be run locally without sandboxing.
        @param otp: The OTP image to use.
        @param rom: The ROM image to use.
        @param tags: The test tags to apply to the test rule.
        @param timeout: The timeout to apply to the test rule.
    """
    required_args = [
        "--rcfile=",
        "--logging=info",
        "--interface=cw310",
        "--conf=sw/host/opentitantool/config/opentitan_cw310.json",
    ]
    required_data = [
        "//sw/host/opentitantool:test_resources",
    ]
    required_tags = [
        "cw310",
        "exclusive",
    ]
    kwargs.update(
        args = required_args + args,
        data = required_data + data,
        local = local,
        otp = otp,
        rom = rom,
        tags = required_tags + tags,
        test_runner = _BASE_PARAMS["test_runner"],
        timeout = timeout,
    )
    return kwargs

def _format_list(param_name, list1, datadict, **kwargs):
    """Concatenate and format list items.

    This is used to prepare substitutions in user-supplied args to the
    various test invocations (ie: the location of flash).
    Args:
        @param param_name: The name of the item in `datadict`.
        @param list1: A list of items to prepend to the list item from datadict.
        @param datadict: A dictionary of per-test parameters.
        @param **kwargs: Values to pass to the format function.
    Returns:
        list[str]
    """
    return [x.format(**kwargs) for x in list1 + datadict.pop(param_name, [])]

def opentitan_functest(
        name,
        targets = ["dv", "verilator", "cw310"],
        args = [],
        data = [],
        ottf = _OTTF_DEPS,
        test_in_rom = False,
        signed = False,
        key = "test_key_0",
        dv = None,
        verilator = None,
        cw310 = None,
        **kwargs):
    """A helper macro for generating OpenTitan functional tests.

    This macro is mostly a wrapper around opentitan_flash_binary, but creates
    testing artifacts for each of the hardware targets in `targets`. The testing
    artifacts are then given to an `sh_test` rule which dispatches the test to
    the corresponding hardware target via opentitantool.
    Args:
      @param name: The name of this rule.
      @param targets: A list of hardware targets on which to dispatch tests.
      @param args: Extra arguments (in addition to those defined in the target-
                   specific parameter dictionary) to pass to the test runner
                   (`opentitantool` or `dvsim.py`).
      @param data: Extra data dependencies (in addition to those defined in the
                   target-specific parameter dictionary) needed while executing
                   the test.
      @param ottf: Default dependencies for OTTF tests. Set to empty list if
                   your test doesn't use the OTTF.
      @param test_in_rom: Whether to run the test from ROM, runs from flash by
                          default.
      @param signed: Whether to sign the test image. Unsigned by default.
      @param key: Which signed test image (by key) to use.
      @param dv: DV test parameters.
      @param verilator: Verilator test parameters.
      @param cw310: CW310 test parameters.
      @param **kwargs: Arguments to forward to `opentitan_flash_binary`.

    This macro emits the following rules:
        opentitan_flash_binary named: {name}_prog (and all emitted rules).
        sh_test                named: dv_{name}
        sh_test                named: verilator_{name}
        sh_test                named: cw310_{name}
        test_suite             named: {name}
    """

    # Generate flash artifacts for test.
    deps = depset(direct = kwargs.pop("deps", []) + ottf).to_list()
    if test_in_rom:
        opentitan_rom_binary(
            name = name + "_rom_prog",
            deps = deps,
            **kwargs
        )
    opentitan_flash_binary(
        name = name + "_prog",
        output_signed = signed,
        deps = deps,
        **kwargs
    )

    all_tests = []

    target_params = {
        "sim_dv": dv_params() if not dv else dv,
        "sim_verilator": verilator_params() if not verilator else verilator,
        "fpga_cw310": cw310_params() if not cw310 else cw310,
    }

    for target, params in target_params.items():
        if target.split("_")[-1] not in targets:
            continue

        # Set test name.
        test_name = "{}_{}".format(target, name)
        if "manual" not in params.get("tags"):
            all_tests.append(test_name)

        # Set flash image.
        if target in ["sim_dv", "sim_verilator"]:
            flash = "{}_prog_{}_scr_vmem64".format(name, target)
        else:
            flash = "{}_prog_{}_bin".format(name, target)
        if signed:
            flash += "_signed_{}".format(key)

        # If the (flash) test image is to be loaded via bootstrap in the DV
        # simulation environment, then we need to use a special VMEM image
        # that has been split into SPI flash frames. Currently, signed
        # images loaded via bootstrap in DV sim are not supported.
        # TODO: support signed bootstap images in DV sim.
        if target == "sim_dv" and params.pop("bootstrap_sw"):
            if test_in_rom:
                fail("Tests that run in ROM cannot be bootstrapped.")
            if signed:
                fail("A signed test cannot be bootstrapped in DV sim.")
            flash = "{}_prog_{target}_frames_vmem".format(name, target)

        # Set ROM image.
        rom = params.pop("rom")
        if test_in_rom:
            rom = "{}_rom_prog_{}_scr_vmem".format(name, target)

        # Set OTP image.
        otp = params.pop("otp")

        # Retrieve remaining device-agnostic params.
        test_runner = params.pop("test_runner")

        # Retrieve device-specific params.
        dvsim_config = None
        if target == "sim_dv":
            dvsim_config = params.pop("dvsim_config")

        # Concatenate args / data passed into the opentitan_functest macro
        # with args / data from device-specific params.
        # TODO(lowRISC/opentitan:#11779): remove this concatenation action
        concat_args = _format_list(
            "args",
            args,
            params,
            dvsim_config = dvsim_config,
            flash = flash,
            name = name,
            otp = otp,
            rom = rom,
        )
        concat_data = _format_list(
            "data",
            data,
            params,
            flash = flash,
        )

        native.sh_test(
            name = test_name,
            srcs = [test_runner],
            args = concat_args,
            data = [
                flash,
                rom,
                otp,
            ] + concat_data,
            **params
        )

    native.test_suite(
        name = name,
        tests = all_tests,
    )
