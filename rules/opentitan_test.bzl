# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "@//rules:opentitan.bzl",
    "RSA_ONLY_KEY_STRUCTS",
    "opentitan_flash_binary",
    "opentitan_rom_binary",
)
load("@bazel_skylib//lib:shell.bzl", "shell")
load("@bazel_skylib//lib:collections.bzl", "collections")
load("@bazel_skylib//lib:sets.bzl", "sets")

def _fpga_from_fpga_target(target):
    """
    Return the FPGA part of an FPGA target name:
      cw310_rom_with_fake_key -> cw310
    """
    return target.split("_")[0]

def _rom_from_fpga_target(target):
    """
    Return the ROM part of an FPGA target name:
      cw310_rom_with_fake_key -> rom_with_fake_key
    """
    return target.partition("_")[2]

def _fpga_target(fpga, rom):
    """
    Return the target name for a given FPGA and ROM.
    """
    return "{}_{}".format(fpga, rom)

_FPGAS = ["cw310", "cw340"]
_ROMS = ["rom_with_fake_keys", "rom_with_real_keys", "test_rom"]

# We do not have a signed CW340 ROM yet.
_BLACKLIST_TARGETS = [("cw340", "rom_with_real_keys")]
FPGA_TARGETS = [
    _fpga_target(fpga, rom)
    for fpga in _FPGAS
    for rom in _ROMS
    if (fpga, rom) not in _BLACKLIST_TARGETS
]
FPGA_DEFAULT_TARGETS = [
    _fpga_target("cw310", "rom_with_fake_keys"),
    _fpga_target("cw310", "test_rom"),
]
VALID_TARGETS = ["dv", "verilator"] + FPGA_TARGETS

# By default, only build CW310 targets to avoid overloading the CI
DEFAULT_TARGETS = ["dv", "verilator"] + FPGA_DEFAULT_TARGETS

OTTF_SUCCESS_MSG = r"PASS.*\n"
OTTF_FAILURE_MSG = r"(FAIL|FAULT).*\n"
ROM_BOOT_FAILURE_MSG = "BFV:[0-9a-f]{8}"

# These are defined for positive test cases and should be flipped for negative
# test cases, i.e., when a test failure is the expected outcome.
DEFAULT_TEST_SUCCESS_MSG = OTTF_SUCCESS_MSG
DEFAULT_TEST_FAILURE_MSG = "({})|({})".format(
    OTTF_FAILURE_MSG,
    ROM_BOOT_FAILURE_MSG,
)

OPENTITANTOOL_OPENOCD_TEST_CMDS = [
    "--openocd=\"$(rootpath //third_party/openocd:openocd_bin)\"",
    "--openocd-adapter-config=\"$(rootpath //third_party/openocd:jtag_olimex_cfg)\"",
]
OPENTITANTOOL_OPENOCD_DATA_DEPS = [
    "//third_party/openocd:jtag_olimex_cfg",
    "//third_party/openocd:openocd_bin",
]

# This constant holds a dictionary of slot-specific linker script dependencies
# that determine how an `opentitan_flash_binary` is built.
_FLASH_SLOTS = {
    "silicon_creator_a": ["@//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a"],
    "silicon_creator_b": ["@//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_b"],
    "silicon_creator_virtual": ["@//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_virtual"],
}

_BASE_PARAMS = {
    "args": [],  # Passed to test runner as arguments.
    "data": [],
    "local": True,
    "otp": "@//hw/ip/otp_ctrl/data:img_rma",
    "rom": "@//sw/device/lib/testing/test_rom",
    "tags": [],
    "test_runner": "@//util:opentitan_functest_runner.sh",
    "test_cmds": [],  # Passed to test_runner via TEST_CMDS env var.
    "timeout": "moderate",  # 5 minutes
    "exit_success": DEFAULT_TEST_SUCCESS_MSG,
    "exit_failure": DEFAULT_TEST_FAILURE_MSG,
}

def dv_params(
        # Base Parameters
        args = _BASE_PARAMS["args"] + [
            "$(location {dvsim_config})",
        ],
        data = _BASE_PARAMS["data"],
        local = _BASE_PARAMS["local"],
        otp = _BASE_PARAMS["otp"],
        rom = _BASE_PARAMS["rom"],
        tags = _BASE_PARAMS["tags"],
        timeout = _BASE_PARAMS["timeout"],
        test_runner = "@//util:dvsim_test_runner.sh",
        test_cmds = [],
        # DV-specific Parameters
        dvsim_config = "@//hw/top_earlgrey/dv:chip_sim_cfg.hjson",
        **kwargs):
    """A macro to create DV sim parameters for OpenTitan functional tests.

    This macro emits a dictionary of parameters which are pasted into the DV
    simulation specific test rule.

    Parameters:
        @param args: Extra arguments to pass to the test runner (`dvsim.py`).
        @param data: Data dependencies of the test.
        @param local: Whether the test should be run locally without sandboxing.
        @param otp: The OTP image to use.
        @param rom: The ROM image to use.
        @param tags: The test tags to apply to the test rule.
        @param timeout: The timeout to apply to the test rule.
        @param test_cmds: A list of required commands and args that make up the
                          immutable portion of the harness invocation.
        @param dvsim_config: The dvsim.py Hjson config file for the toplevel.
    """
    required_test_cmds = [
        "-i",
        "chip_sw_{name}",
        "--",
    ]
    required_data = [
        dvsim_config,
        "@//util/dvsim",
        "@//hw:all_files",
        "@//hw:fusesoc_ignore",
    ]
    required_tags = ["dv"]
    kwargs.update(
        args = args,
        data = required_data + data,
        local = local,
        otp = otp,
        rom = rom,
        tags = required_tags + tags,
        test_runner = test_runner,
        test_cmds = required_test_cmds + test_cmds,
        timeout = timeout,
        dvsim_config = dvsim_config,
    )
    return kwargs

def verilator_params(
        # Base Parameters
        args = _BASE_PARAMS["args"],
        data = _BASE_PARAMS["data"],
        exit_success = _BASE_PARAMS["exit_success"],
        exit_failure = _BASE_PARAMS["exit_failure"],
        local = _BASE_PARAMS["local"],
        otp = _BASE_PARAMS["otp"],
        rom = _BASE_PARAMS["rom"],
        tags = _BASE_PARAMS["tags"],
        timeout = _BASE_PARAMS["timeout"],
        test_runner = _BASE_PARAMS["test_runner"],
        test_cmds = _BASE_PARAMS["test_cmds"] + [
            "console",
            "--exit-success={exit_success}",
            "--exit-failure={exit_failure}",
        ],
        # Verilator-specific Parameters
        # None
        **kwargs):
    """A macro to create Verilator sim parameters for OpenTitan functional tests.

    This macro emits a dictionary of parameters which are pasted into the
    Verilator simulation specific test rule.

    Parameters:
        @param args: Extra arguments to pass to the test runner (`opentitantool`).
        @param data: Data dependencies of the test.
        @param local: Whether the test should be run locally without sandboxing.
        @param otp: The OTP image to use.
        @param rom: The ROM image to use.
        @param tags: The test tags to apply to the test rule.
        @param timeout: The timeout to apply to the test rule.
        @param test_cmds: A list of required commands and args that make up the
                          immutable portion of the harness invocation.
    """
    default_args = [
        "--rcfile=",
        "--logging={logging}",
    ]
    required_test_cmds = [
        "--interface=verilator",
        "--verilator-bin=$(location @//hw:verilator)",
        "--verilator-rom=$(location {rom})",
        "--verilator-flash=$(location {flash})",
        "--verilator-otp=$(location {otp})",
    ]
    required_data = [
        "@//hw:verilator",
        "@//hw:fusesoc_ignore",
    ]
    required_tags = ["verilator", "cpu:5"]
    kwargs.update(
        args = default_args + args,
        data = required_data + data,
        exit_success = exit_success,
        exit_failure = exit_failure,
        local = local,
        otp = otp,
        rom = rom,
        tags = required_tags + tags,
        test_runner = test_runner,
        test_cmds = required_test_cmds + test_cmds,
        timeout = timeout,
    )
    return kwargs

def fpga_params(
        # Base Parameters
        args = _BASE_PARAMS["args"],
        data = _BASE_PARAMS["data"] + ["{bitstream}"],
        exit_success = _BASE_PARAMS["exit_success"],
        exit_failure = _BASE_PARAMS["exit_failure"],
        local = _BASE_PARAMS["local"],
        otp = _BASE_PARAMS["otp"],
        tags = _BASE_PARAMS["tags"],
        test_runner = _BASE_PARAMS["test_runner"],
        test_cmds = [
            "--exec=\"transport init\"",
            "--exec=\"fpga load-bitstream $(location {bitstream})\"",
            "--exec=\"bootstrap --clear-uart=true $(location {flash})\"",
            "--exec=\"console --exit-success={exit_success} --exit-failure={exit_failure}\"",
            "{clear_bitstream}",
        ],
        # CW-specific Parameters
        bitstream = None,  # A bitstream value of None will cause the default bitstream values to be used
        clear_bitstream = False,
        # None
        timeout = "short",
        interface = None,
        **kwargs):
    """A macro to create ChipWhisperer parameters for OpenTitan functional tests.

    This macro emits a dictionary of parameters which are pasted into the
    ChipWhisperer FPGA specific test rule.

    Parameters:
        @param args: Extra arguments to pass the test runner `opentitantool`.
        @param data: Data dependencies of the test.
        @param local: Whether the test should be run locally without sandboxing.
        @param interface: Which communication interface to use with opentitantool.
        @param otp: The OTP image to use.
        @param tags: The test tags to apply to the test rule.
        @param test_cmds: A list of required commands and args that make up the
                          immutable portion of the harness invocation.
        @param timeout: The timeout to apply to the test rule.
        @param bitstream: The bitstream to load into the FPGA (this specifies
                          the ROM image that is also used, since the ROM is
                          baked into the bitstream).
        @param clear_bitstream: Clear FPGA bitstream at the end of the test.
    """
    default_args = [
        "--rcfile=",
        "--logging={logging}",
    ]
    required_test_cmds = [
        "--interface={}".format(interface),
    ]
    required_tags = [
        interface,
        "exclusive",
    ]
    kwargs.update(
        args = default_args + args,
        data = data,
        exit_success = exit_success,
        exit_failure = exit_failure,
        local = local,
        interface = interface,
        otp = otp,
        tags = required_tags + tags,
        test_runner = test_runner,
        test_cmds = required_test_cmds + test_cmds,
        timeout = timeout,
        bitstream = bitstream,
        clear_bitstream = clear_bitstream,
    )
    return kwargs

def cw310_params(
        interface = "cw310",
        **kwargs):
    """A macro to create CW310-specific parameters for OpenTitan functional tests.

    Parameters:
        @param interface: Which communication interface to use with the CW310
                          board.  Choices are "cw310" or "hyper310".
    All others parameters are forwarded to fpga_params()
    """
    if interface not in ("cw310", "hyper310"):
        fail("The interface must be either 'cw310' or 'hyper310'")
    kwargs.update(interface = interface)
    return fpga_params(**kwargs)

def cw340_params(
        interface = "cw340",
        **kwargs):
    """A macro to create CW340-specific parameters for OpenTitan functional tests.

    Parameters:
        @param interface: Which communication interface to use with the CW340
                          board.  Choices are "cw340".
    All others parameters are forwarded to fpga_params()
    """
    if interface not in ("cw340", "hyper340"):
        fail("The interface must be either 'cw340' or 'hyper340'.")
    kwargs.update(interface = interface)
    return fpga_params(**kwargs)

def opentitan_functest(
        name,
        targets = DEFAULT_TARGETS,
        args = [],
        data = [],
        test_in_rom = False,
        ot_flash_binary = None,
        signed = True,
        manifest = "@//sw/device/silicon_creator/rom_ext:manifest_standard",
        slot = "silicon_creator_a",
        test_harness = "@//sw/host/opentitantool",
        key_struct = RSA_ONLY_KEY_STRUCTS[0],
        logging = "info",
        dv = None,
        verilator = None,
        **kwargs):
    """A helper macro for generating OpenTitan functional tests.

    This macro is mostly a wrapper around `opentitan_flash_binary`, but creates
    testing artifacts for each of the hardware targets in `targets`. The testing
    artifacts are then given to an `sh_test` rule which dispatches the test to
    the corresponding hardware target via `opentitantool`.
    Parameters:
      @param name: The name of this rule.
      @param targets: A list of hardware targets on which to dispatch tests.
      @param args: Extra arguments (in addition to those defined in the target-
                   specific parameter dictionary) to pass to the test harness
                   (e.g., `opentitantool`).
      @param data: Extra data dependencies (in addition to those defined in the
                   target-specific parameter dictionary) needed while executing
                   the test.
      @param test_in_rom: Whether to run the test from ROM, runs from flash by
                          default.
      @param ot_flash_binary: Use the named `opentitan_flash_binary` as the
                              flash image for the test rather than building one
                              from srcs/deps.
      @param signed: Whether to sign the test image. Signed by default.
      @param manifest: Partially populated manifest to set boot stage/slot configs.
      @param slot: What slot to build the image for.
      @param test_harness: The binary on the host side that runs the test.
      @param key_struct: Which signed test image (by key set) to use.
      @param dv: DV test parameters.
      @param verilator: Verilator test parameters.
      @param cw310: CW310 test parameters.
      @param cw340: CW340 test parameters.
      @param **kwargs: Arguments to forward to `opentitan_flash_binary`.

    This macro emits the following rules:
        if `test_in_rom`:
          opentitan_rom_binary named: {name}_rom_prog (and all emitted rules).
        opentitan_flash_binary named: {name}_prog (and all emitted rules).
        sh_test                named: {name}_sim_dv
        sh_test                named: {name}_sim_verilator
        sh_test                named: {name}_fpga_cw310
        test_suite             named: {name}
    """
    deps = kwargs.pop("deps", [])
    all_tests = []
    target_params = {}

    fpga_params_ = {}
    for fpga in _FPGAS:
        fpga_params_[fpga] = kwargs.pop(fpga, fpga_params(interface = fpga))

    # Only build SW for devices we are running tests on.
    devices_to_build_for = []
    for target in targets:
        if target == "dv":
            devices_to_build_for.append("sim_dv")
            target_params["sim_dv"] = dv_params() if not dv else dv
        elif target == "verilator":
            devices_to_build_for.append("sim_verilator")
            target_params["sim_verilator"] = verilator_params() if not verilator else verilator
        elif target in FPGA_TARGETS:
            fpga_name = _fpga_from_fpga_target(target)
            rom_name = _rom_from_fpga_target(target)
            devices_to_build_for.append("fpga_{}".format(fpga_name))

            # Copy parameters for each `target`. This is not a deep copy, thus we
            # also copy tags below.
            params = dict(fpga_params_[fpga_name].items())
            params["tags"] = [t for t in params["tags"]]

            # If the parameter was not provided or was provided without
            # the bitstream field, determine the bitstream argument based on
            # the target. Otherwise, use the provided bitstream argument.
            _DEFAULT_BITSTREAM_PATH = {
                "cw310": {
                    "cw310": "@//hw/bitstream",
                    "hyper310": "@//hw/bitstream/hyperdebug",
                },
                "cw340": {
                    "cw340": "@//hw/bitstream/cw340",
                    "hyper340": "@//hw/bitstream/cw340",
                },
            }
            if params.get("bitstream") == None:
                if fpga_name not in _DEFAULT_BITSTREAM_PATH:
                    fail("Could not find a default bitstream for FPGA target '{}'", fpga_name)
                intf = params["interface"]
                if intf not in _DEFAULT_BITSTREAM_PATH[fpga_name]:
                    fail(
                        "Could not find a default bitstream for interface {} for FPGA target '{}'",
                        intf,
                        fpga_name,
                    )
                params["bitstream"] = "{}:{}".format(
                    _DEFAULT_BITSTREAM_PATH[fpga_name][intf],
                    rom_name,
                )

            # If the bitstream field was provided, it will already have been copied into the parameters.

            # Fill in the remaining arguments
            params["tags"].append(target)
            target_params[target] = params
        else:
            fail("Invalid target {}. Target must be in {}".format(target, VALID_TARGETS))
    devices_to_build_for = collections.uniq(devices_to_build_for)

    # Handle the special case were the test is run at the ROM stage.
    if test_in_rom:
        if ot_flash_binary:
            fail("Tests that run in ROM stage cannot use pre-built flash binary.")
        if target in FPGA_TARGETS:
            fail("Tests that run in ROM stage cannot run on FPGA.")
        ot_flash_binary = name + "_rom_prog"
        opentitan_rom_binary(
            name = ot_flash_binary,
            deps = deps,
            devices = devices_to_build_for,
            testonly = True,
            **kwargs
        )

    # Generate SW artifacts for the tests.
    if not ot_flash_binary:
        # Set the linker script for the specified slot.
        if slot not in _FLASH_SLOTS:
            fail("Invalid slot: {}. Valid slots are: silicon_creator_{a,b,virtual}".format(slot))
        deps += _FLASH_SLOTS[slot]

        # Get OTP image for sim targets. We need to pass the OTP image to the
        # flash scrambling script since it contains the seeds to derive the
        # scrambling keys. No need to worry about flash image scrambling for
        # FPGA targets as the flash is loaded through bootstrap (i.e., the front
        # door), unlike the sim targets which load via backdoor.
        sim_otp_ = None
        if "sim_dv" in target_params:
            sim_otp_ = target_params["sim_dv"]["otp"]
        elif "sim_verilator" in target_params:
            sim_otp_ = target_params["sim_verilator"]["otp"]
        ot_flash_binary = name + "_prog"
        opentitan_flash_binary(
            name = ot_flash_binary,
            signed = signed,
            sim_otp = sim_otp_,
            deps = deps,
            devices = devices_to_build_for,
            manifest = manifest,
            testonly = True,
            **kwargs
        )

    for target, params in target_params.items():
        # Set test name.
        test_name = "{}_{}".format(name, target)

        all_tests.append(test_name)

        # The args/data lists will hold all of the test arguments/artifacts that
        # need to be present at runtime.
        target_args = args
        target_data = data + [test_harness]
        target_test_cmds = []

        ########################################################################
        # Retrieve host-side test components.
        ########################################################################
        # Environment variables to pass to the `sh_test`.
        env = {}

        # Set the test runner (i.e., the script that invokes the "test harness").
        test_runner = params.pop("test_runner")

        # Set the test harness (i.e., the host-side test component, or
        # `opentitantool` in most cases).
        env["TEST_HARNESS"] = "$(location {})".format(test_harness)

        ########################################################################
        # Retrieve device-side test components.
        ########################################################################
        # Set ROM image.
        # Note: FPGA targets will not specify a ROM image as the ROM imaged is
        # specified via the `bitstream` parameter (since the ROM is baked into
        # the bitstream).
        rom = params.pop("rom", None)
        if rom:
            if test_in_rom:
                rom_filegroup = "{}_rom_prog_{}".format(name, target)
                rom = "{}_scr_vmem".format(rom_filegroup)
            else:
                rom_label = Label(rom)
                rom_filegroup = "@{}//{}:{}_{}".format(
                    rom_label.workspace_name,
                    rom_label.package,
                    rom_label.name,
                    target,
                )
                rom = "{}_scr_vmem".format(rom_filegroup)
            target_data.append(rom)
            target_data.append(rom_filegroup)

        # Set flash image.
        if target in ["sim_dv", "sim_verilator"]:
            flash = "{}_{}_scr_vmem64".format(ot_flash_binary, target)
        elif target in FPGA_TARGETS:
            flash = "{}_fpga_{}_bin".format(ot_flash_binary, _fpga_from_fpga_target(target))
        else:
            fail("Unexpected target: {}".format(target))
        if signed:
            flash += "_signed"

            # Multislot flash binaries could have different slots / stages
            # signed with different keys. Therefore, the key name will not be
            # part of the target name for such images.
            if key_struct != "multislot":
                if type(key_struct) == "string":
                    suffix = key_struct
                else:
                    suffix_parts = []
                    if key_struct.rsa:
                        suffix_parts.append(key_struct.rsa.name)
                    if key_struct.spx:
                        suffix_parts.append(key_struct.spx.name)
                    suffix = "_".join(suffix_parts)
                flash += "_{}".format(suffix)

        # If test is to be run in ROM we load the same image into flash as a
        # as a placeholder (since execution will never reach flash). Moreover,
        # there is no need to update the data dependencies list as the ROM
        # targets were already added above.
        if test_in_rom:
            flash = rom
        else:
            target_data.append(flash)
            if target in FPGA_TARGETS:
                target_data.append("{}_fpga_{}".format(ot_flash_binary, _fpga_from_fpga_target(target)))
            else:
                target_data.append("{}_{}".format(ot_flash_binary, target))

        # Set OTP image.
        otp = params.pop("otp")
        target_data.append(otp)

        ########################################################################
        # Retrieve hardware-target-specific parameters.
        ########################################################################
        interface = params.pop("interface", None)

        # Set Bitstream (for FPGA targets).
        bitstream = params.pop("bitstream", None)
        clear_bitstream = "no-op"
        if params.pop("clear_bitstream", False):
            clear_bitstream = "fpga clear-bitstream"

        # Set success/failure strings for target platforms that print test
        # results over the UART (e.g., Verilator and FPGA).
        exit_strings_kwargs = {}
        if target in FPGA_TARGETS + ["sim_verilator"]:
            exit_strings_kwargs = {
                "exit_success": shell.quote(params.pop("exit_success")),
                "exit_failure": shell.quote(params.pop("exit_failure")),
            }

        # Set dvsim configuration file (for DV simulation target).
        dvsim_config = params.pop("dvsim_config", None)

        ########################################################################
        # Format arguments to send to the test running scripts/tools.
        ########################################################################
        # Concatenate args / data passed into the opentitan_functest macro with
        # args / data from device-specific params.
        target_args = target_args + params.pop("args")
        target_data = target_data + params.pop("data")
        target_test_cmds = target_test_cmds + params.pop("test_cmds")

        # Fill placeholders in arg/data lists.
        format_dict = {
            "name": name,
            "flash": flash,
            "rom": rom,
            "otp": otp,
            "dvsim_config": dvsim_config,
            "clear_bitstream": clear_bitstream,
            "bitstream": bitstream,
            "logging": params.pop("logging", logging),
        }
        format_dict.update(exit_strings_kwargs)
        target_args = [a.format(**format_dict) for a in target_args]
        target_data = [d.format(**format_dict) for d in target_data]
        target_test_cmds = [s.format(**format_dict) for s in target_test_cmds]
        env["TEST_CMDS"] = " ".join(target_test_cmds)

        if target in FPGA_TARGETS:
            # We attach the UART configuration to the front of the command line
            # so that they'll be parsed as global options rather than
            # command-specific options.
            select_options = {
                "//conditions:default": [],
            }
            fpga_name = _fpga_from_fpga_target(target)
            if fpga_name == "cw310":
                select_options["@//ci:lowrisc_fpga_cw310"] = ["--uarts=/dev/ttyACM_CW310_1,/dev/ttyACM_CW310_0"]
            elif fpga_name == "cw340":
                # The CW340 supports different options for the UARTs: they can be wired to the SAM3x or the FTDI.
                # The CI currently uses the FTDI.
                select_options["@//ci:lowrisc_fpga_cw340"] = ["--uarts=/dev/ttyCW340_FTDI_2,/dev/ttyCW340_FTDI_3"]

            target_args = select(select_options) + target_args

        ########################################################################
        # Instantiate the test rule.
        ########################################################################
        native.sh_test(
            name = test_name,
            srcs = [test_runner],
            args = target_args,
            data = target_data,
            env = env,
            **params
        )

    # Guarantee that the test suite will only run tests in `all_tests`. This
    # check is necessary because `test_suite()` defaults to all the tests in the
    # caller's BUILD file when its `tests` attribute is the empty list.
    if all_tests == []:
        fail("Zero tests generated for :{}, test_suite() would run the wrong tests.".format(name))

    ############################################################################
    # Instantiate a suite of tests to run the same test on each hardware target.
    ############################################################################
    native.test_suite(
        name = name,
        tests = all_tests,
        # In test_suites, tags perform a filtering function and will select
        # matching tags internally instead of allowing filters to select
        # test_suites.
        # There are exceptions: "small", "medium", "large", "enourmous", "manual"
        tags = [
            # The manual tag is a special case and is applied to the test suite
            # it prevents it from being included in wildcards so that
            # --build_tag_filters=-verilator works as expected and excludes
            # building verilator tests so the verilator build wont be invoked.
            "manual",
            # For more see https://bazel.build/reference/be/general#test_suite.tags
        ],
    )

def _manual_test_impl(ctx):
    executable = ctx.actions.declare_file("manual_test_wrapper")
    ctx.actions.write(
        output = executable,
        content = "{runner} {testplan}".format(
            runner = ctx.executable._runner.short_path,
            testplan = ctx.file.testplan.short_path,
        ),
    )
    return [
        DefaultInfo(
            runfiles = ctx.runfiles(
                files = [
                    ctx.executable._runner,
                    ctx.file.testplan,
                ],
            ).merge(ctx.attr._runner[DefaultInfo].default_runfiles),
            executable = executable,
        ),
    ]

manual_test = rule(
    _manual_test_impl,
    attrs = {
        "testplan": attr.label(
            allow_single_file = [".hjson"],
            doc = "Testplan with manual testpoints",
            mandatory = True,
        ),
        "_runner": attr.label(
            default = "//util:run_manual_tests",
            executable = True,
            cfg = "exec",
        ),
    },
    doc = "Walks through the manual testpoints in a testplan",
    test = True,
)
