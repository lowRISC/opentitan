# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "opentitan_flash_binary", "opentitan_rom_binary")

_BASE_PARAMS = {
    "args": [],
    "data": [],
    "local": True,
    # TODO: the name of this target should be target generic
    "otp": "//hw/ip/otp_ctrl/data:rma_image_verilator",
    "rom": "//sw/device/lib/testing/test_rom:test_rom_{}_scr_vmem",
    "tags": [],
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
        rom = _BASE_PARAMS["rom"].format("sim_dv"),
        otp = _BASE_PARAMS["otp"],
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
        @param otp: The OTP image to use when running a DV simulation.
        @param rom: The ROM to use when running a DV simulation.
        @param tags: The test tags to apply to the test rule.
        @param timeout: The timeout to apply to the test rule.
        @param bootstrap_sw: Whether to load flash via bootstrap.
        @param dvsim_config: The dvsim.py Hjson config file for the toplevel.
    """
    kwargs.update(
        args = args,
        data = data,
        local = local,
        otp = otp,
        rom = rom,
        tags = tags + ["dv"],
        timeout = timeout,
        bootstrap_sw = bootstrap_sw,
        dvsim_config = dvsim_config,
    )
    return kwargs

def verilator_params(
        # Base Parameters
        args = _BASE_PARAMS["args"] + [
            "console",
            "--exit-failure=FAIL",
            "--exit-success=PASS",
            "--timeout=3600",
        ],
        data = _BASE_PARAMS["data"],
        local = _BASE_PARAMS["local"],
        rom = _BASE_PARAMS["rom"].format("sim_verilator"),
        otp = _BASE_PARAMS["otp"],
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
        @param otp: The OTP image to use when running a Verilator simulation.
        @param rom: The ROM to use when running a Verilator simulation.
        @param tags: The test tags to apply to the test rule.
        @param timeout: The timeout to apply to the test rule.
    """
    kwargs.update(
        args = args,
        data = data,
        local = local,
        otp = otp,
        rom = rom,
        tags = tags + ["verilator"],
        timeout = timeout,
    )
    return kwargs

def cw310_params(
        # Base Parameters
        args = _BASE_PARAMS["args"] + [
            "--exec=\"console -q -t0\"",
            "--exec=\"bootstrap $(location {test_bin})\"",
            "console",
            "--exit-failure=FAIL",
            "--exit-success=PASS",
            "--timeout=3600",
        ],
        data = _BASE_PARAMS["data"],
        local = _BASE_PARAMS["local"],
        # ROM and OTP images are baked into the FPGA bitstream, thus are not
        # loaded by the test runner, and do not need to be specified.
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
        @param tags: The test tags to apply to the test rule.
        @param timeout: The timeout to apply to the test rule.
    """
    kwargs.update(
        args = args,
        data = data,
        local = local,
        tags = tags + ["cw310", "exclusive"],
        timeout = timeout,
    )
    return kwargs

def _format_list(name, list1, datadict, **kwargs):
    """Concatenate and format list items.

    This is used to prepare substitutions in user-supplied args to the
    various test invocations (ie: the location of test_bin).
    Args:
        @param name: The name of the item in `datadict`.
        @param list1: A list of items to prepend to the list item from datadict.
        @param datadict: A dictionary of per-test parameters.
        @param **kwargs: Values to pass to the format function.
    Returns:
        list[str]
    """
    return [x.format(**kwargs) for x in list1 + datadict.pop(name, [])]

def _unique_deps(*deplists):
    uniq = {}
    for deplist in deplists:
        for dep in deplist:
            uniq[dep] = True
    return uniq.keys()

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
      @param args: Extra arguments to pass to the test runner (`opentitantool`
                   or `dvsim.py`).
      @param data: Extra data dependencies needed while executing the test.
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
    deps = _unique_deps(kwargs.pop("deps", []), ottf)
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

    if "dv" in targets:
        # Set default DV sim parameters if none are provided.
        if dv == None:
            dv = dv_params()

        test_name = "dv_{}".format(name)

        # Regardless if the test is signed or not, DV sims backdoor load flash
        # with the scrambled VMEM (unless the bootstrap path is used below).
        test_bin = "{}_prog_sim_dv_scr_vmem64".format(name)

        # If the (flash) test image is to be loaded via bootstrap, then we need
        # to use the VMEM image that has been split into SPI flash frames.
        if dv.pop("bootstrap_sw"):
            if test_in_rom:
                fail("A test runs in ROM cannot be bootstrapped.")
            test_bin = "{}_prog_sim_dv_frames_vmem".format(name)

        if "manual" not in dv.get("tags", []):
            all_tests.append(test_name)

        rom = dv.pop("rom")
        if test_in_rom:
            rom = name + "_rom_prog_sim_dv_scr_vmem"
        otp = dv.pop("otp")
        dvsim_config = dv.pop("dvsim_config")
        dargs = _format_list("args", args, dv, dvsim_config = dvsim_config)
        ddata = _format_list("data", data, dv)

        native.sh_test(
            name = test_name,
            srcs = ["//util:dvsim_test_runner.sh"],
            args = [
                "-i",
                "chip_sw_{}".format(name),
            ] + dargs,
            data = [
                test_bin,
                rom,
                otp,
                dvsim_config,
                "//util/dvsim",
                "//hw:all_files",
            ] + ddata,
            **dv
        )

    if "verilator" in targets:
        # Set default Verilator sim parameters if none are provided.
        if verilator == None:
            verilator = verilator_params()

        test_name = "verilator_{}".format(name)

        # If the test is unsigned, the Verilator sim can backdoor load flash
        # with the ELF.
        test_bin = "{}_prog_sim_verilator_elf".format(name)

        # If the test is signed, the Verilator sim must backdoor load flash with
        # the scrambled VMEM, since only the BIN can be signed by the ROM_EXT
        # signer tool, and this is converted to a scrambled (64-bit) VMEM.
        if signed:
            test_bin = "{}_prog_sim_verilator_scr_vmem64_signed_{}".format(
                name,
                key,
            )

        rom = verilator.pop("rom")
        if test_in_rom:
            rom = name + "_rom_prog_sim_verilator_scr_vmem"
        otp = verilator.pop("otp")
        vargs = _format_list("args", args, verilator, test_bin = test_bin)
        vdata = _format_list("data", data, verilator, test_bin = test_bin)

        if "manual" not in verilator.get("tags", []):
            all_tests.append(test_name)

        native.sh_test(
            name = test_name,
            srcs = ["//util:opentitantool_test_runner.sh"],
            args = [
                "--rcfile=",
                "--logging=info",
                "--interface=verilator",
                "--conf=sw/host/opentitantool/config/opentitan_verilator.json",
                "--verilator-bin=$(location //hw:verilator)/sim-verilator/Vchip_sim_tb",
                "--verilator-rom=$(location {})".format(rom),
                "--verilator-flash=$(location {})".format(test_bin),
                "--verilator-otp=$(location {})".format(otp),
            ] + vargs,
            data = [
                test_bin,
                rom,
                otp,
                "//sw/host/opentitantool:test_resources",
                "//hw:verilator",
            ] + vdata,
            **verilator
        )

    if "cw310" in targets:
        # Set default CW310 FPGA parameters if none are provided.
        if cw310 == None:
            cw310 = cw310_params()

        if test_in_rom:
            fail("test_in_rom only valid on simulation targets.")

        test_name = "cw310_{}".format(name)

        test_bin = "{}_prog_fpga_cw310_bin".format(name)
        if signed:
            test_bin = "{}_prog_fpga_cw310_bin_signed_{}".format(name, key)

        cargs = _format_list("args", args, cw310, test_bin = test_bin)
        cdata = _format_list("data", data, cw310, test_bin = test_bin)

        if "manual" not in cw310.get("tags", []):
            all_tests.append(test_name)

        native.sh_test(
            name = test_name,
            srcs = ["//util:opentitantool_test_runner.sh"],
            args = [
                "--rcfile=",
                "--logging=info",
                "--interface=cw310",
                "--conf=sw/host/opentitantool/config/opentitan_cw310.json",
            ] + cargs,
            data = [
                test_bin,
                "//sw/host/opentitantool:test_resources",
            ] + cdata,
            **cw310
        )

    native.test_suite(
        name = name,
        tests = all_tests,
    )
