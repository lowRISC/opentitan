# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "@lowrisc_opentitan//rules/opentitan:providers.bzl",
    "Cw305BinaryInfo",
    "Cw310BinaryInfo",
    "Cw340BinaryInfo",
)
load(
    "@lowrisc_opentitan//rules/opentitan:util.bzl",
    "assemble_for_test",
    "get_fallback",
)
load(
    "//rules/opentitan:exec_env.bzl",
    "ExecEnvInfo",
    "common_test_setup",
    "exec_env_as_dict",
    "exec_env_common_attrs",
)
load(
    "@lowrisc_opentitan//rules/opentitan:transform.bzl",
    "convert_to_scrambled_rom_vmem",
    "convert_to_vmem",
)
load(
    "@lowrisc_opentitan//rules/opentitan:openocd.bzl",
    "OPENTITANTOOL_OPENOCD_DATA_DEPS",
    "OPENTITANTOOL_OPENOCD_TEST_CMD",
)

_TEST_SCRIPT = """#!/bin/bash
set -e

TEST_CMD=({test_cmd})
echo Invoking test: {test_harness} {args} "${{TEST_CMD[@]}}"
RUST_BACKTRACE=1 {test_harness} {args} "${{TEST_CMD[@]}}"
"""

def _transform(ctx, exec_env, name, elf, binary, signed_bin, disassembly, mapfile):
    """Transform binaries into the preferred forms for fpga_cw310.

    Args:
      ctx: The rule context.
      exec_env: The ExecEnvInfo for this environment.
      name: The rule name/basename.
      elf: The compiled elf program.
      binary: The raw binary of the compiled program.
      signed_bin: The signed binary (if available).
      disassembly: A disassembly listing.
      mapfile: The linker-created mapfile.
    Returns:
      dict: A dict of fields to create in the provider.
    """

    if ctx.attr.kind == "rom":
        rom = convert_to_scrambled_rom_vmem(
            ctx,
            name = name,
            src = elf,
            suffix = "39.scr.vmem",
            rom_scramble_config = exec_env.rom_scramble_config,
            rom_scramble_tool = ctx.executable.rom_scramble_tool,
        )

        # The englishbreakfast verilator model does not understand ROM
        # scrambling, so we also create a non-scrambled VMEM file.
        rom32 = convert_to_vmem(
            ctx,
            name = name,
            src = binary,
            word_size = 32,
        )
        default = rom
    elif ctx.attr.kind == "ram":
        default = elf
        rom = None
        rom32 = None
    elif ctx.attr.kind == "flash":
        default = signed_bin if signed_bin else binary
        rom = None
        rom32 = None
    else:
        fail("Not implemented: kind ==", ctx.attr.kind)

    return {
        "elf": elf,
        "binary": binary,
        "default": default,
        "rom": rom,
        "rom32": rom32,
        "signed_bin": signed_bin,
        "disassembly": disassembly,
        "mapfile": mapfile,
    }

def _test_dispatch(ctx, exec_env, firmware):
    """Dispatch a test for the fpga_cw310 environment.

    Args:
      ctx: The rule context.
      exec_env: The ExecEnvInfo for this environment.
      firmware: A label with a Cw310BinaryInfo provider attached.
    Returns:
      (File, List[File]) The test script and needed runfiles.
    """
    if ctx.attr.kind == "rom":
        fail("CW310 is not capable of executing ROM tests")

    test_harness, data_labels, data_files, param, action_param = common_test_setup(ctx, exec_env, firmware)

    # If the test requested an assembled image, then use opentitantool to
    # assemble the image.  Replace the firmware param with the newly assembled
    # image.
    if "assemble" in param:
        assemble = param["assemble"].format(**action_param)
        assemble = ctx.expand_location(assemble, data_labels)
        image = assemble_for_test(
            ctx,
            name = ctx.attr.name,
            spec = assemble.split(" "),
            data_files = data_files,
            opentitantool = exec_env._opentitantool,
        )
        param["firmware"] = image.short_path
        action_param["firmware"] = image.path
        data_files.append(image)

    # FIXME: maybe splice a bitstream here

    # Perform all relevant substitutions on the test_cmd.
    test_cmd = get_fallback(ctx, "attr.test_cmd", exec_env)
    test_cmd = test_cmd.format(**param)
    test_cmd = ctx.expand_location(test_cmd, data_labels)

    # Get the pre-test_cmd args.
    args = get_fallback(ctx, "attr.args", exec_env)
    args = " ".join(args).format(**param)
    args = ctx.expand_location(args, data_labels)

    # Construct the test script
    script = ctx.actions.declare_file(ctx.attr.name + ".bash")
    ctx.actions.write(
        script,
        _TEST_SCRIPT.format(
            test_harness = test_harness.short_path,
            args = args,
            test_cmd = test_cmd,
        ),
        is_executable = True,
    )
    return script, data_files

def _fpga_cw310(ctx):
    fields = exec_env_as_dict(ctx)
    return ExecEnvInfo(
        provider = Cw310BinaryInfo,
        test_dispatch = _test_dispatch,
        transform = _transform,
        **fields
    )

fpga_cw310 = rule(
    implementation = _fpga_cw310,
    attrs = exec_env_common_attrs(),
)

def _fpga_cw305(ctx):
    fields = exec_env_as_dict(ctx)
    return ExecEnvInfo(
        provider = Cw305BinaryInfo,
        test_dispatch = _test_dispatch,
        transform = _transform,
        **fields
    )

fpga_cw305 = rule(
    implementation = _fpga_cw305,
    attrs = exec_env_common_attrs(),
)

def _fpga_cw340(ctx):
    fields = exec_env_as_dict(ctx)
    return ExecEnvInfo(
        provider = Cw340BinaryInfo,
        test_dispatch = _test_dispatch,
        transform = _transform,
        **fields
    )

fpga_cw340 = rule(
    implementation = _fpga_cw340,
    attrs = exec_env_common_attrs(),
)

def cw310_params(
        tags = [],
        timeout = "short",
        local = True,
        test_harness = None,
        binaries = {},
        rom = None,
        rom_ext = None,
        otp = None,
        bitstream = None,
        test_cmd = "",
        data = [],
        **kwargs):
    """A macro to create CW310 parameters for OpenTitan tests.

    Args:
      tags: The test tags to apply to the test rule.
      timeout: The timeout to apply to the test rule.
      local: Whether to set the `local` flag on this test.
      test_harness: Use an alternative test harness for this test.
      binaries: Dict of binary labels to substitution parameter names.
      rom: Use an alternate ROM for this test.
      rom_ext: Use an alternate ROM_EXT for this test.
      otp: Use an alternate OTP configuration for this test.
      bitstream: Use an alternate bitstream for this test.
      test_cmd: Use an alternate test_cmd for this test.
      data: Additional files needed by this test.
      kwargs: Additional key-value pairs to override in the test `param` dict.
    Returns:
      struct of test parameters.
    """
    return struct(
        tags = ["hyper310", "exclusive"] + tags,
        timeout = timeout,
        local = local,
        test_harness = test_harness,
        binaries = binaries,
        rom = rom,
        rom_ext = rom_ext,
        otp = otp,
        bitstream = bitstream,
        test_cmd = test_cmd,
        data = data,
        param = kwargs,
    )

def cw310_jtag_params(
        tags = [],
        timeout = "short",
        local = True,
        test_harness = None,
        binaries = {},
        rom = None,
        rom_ext = None,
        otp = None,
        bitstream = None,
        test_cmd = "",
        data = [],
        **kwargs):
    """A macro to create CW310 parameters for OpenTitan JTAG tests.

    This creates version of the CW310 parameter structure pre-initialized
    with OpenOCD dependencies and test_cmd parameters.

    Args:
      tags: The test tags to apply to the test rule.
      timeout: The timeout to apply to the test rule.
      local: Whether to set the `local` flag on this test.
      test_harness: Use an alternative test harness for this test.
      binaries: Dict of binary labels to substitution parameter names.
      rom: Use an alternate ROM for this test.
      rom_ext: Use an alternate ROM_EXT for this test.
      otp: Use an alternate OTP configuration for this test.
      bitstream: Use an alternate bitstream for this test.
      test_cmd: Use an alternate test_cmd for this test.
      data: Additional files needed by this test.
      kwargs: Additional key-value pairs to override in the test `param` dict.
    Returns:
      struct of test parameters.
    """
    return struct(
        tags = ["hyper310", "exclusive"] + tags,
        timeout = timeout,
        local = local,
        test_harness = test_harness,
        binaries = binaries,
        rom = rom,
        rom_ext = rom_ext,
        otp = otp,
        bitstream = bitstream,
        test_cmd = OPENTITANTOOL_OPENOCD_TEST_CMD + test_cmd,
        data = OPENTITANTOOL_OPENOCD_DATA_DEPS + data,
        param = kwargs,
    )
