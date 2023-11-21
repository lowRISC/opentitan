# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@lowrisc_opentitan//rules/opentitan:providers.bzl", "SimVerilatorBinaryInfo")
load("@lowrisc_opentitan//rules/opentitan:util.bzl", "get_fallback")
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
load("//rules/opentitan:toolchain.bzl", "LOCALTOOLS_TOOLCHAIN")

_TEST_SCRIPT = """#!/bin/bash
set -e

TEST_CMD=({test_cmd})
echo Invoking test: {test_harness} {args} "$@" "${{TEST_CMD[@]}}"
RUST_BACKTRACE=1 {test_harness} {args} "$@" "${{TEST_CMD[@]}}"
"""

def _transform(ctx, exec_env, name, elf, binary, signed_bin, disassembly, mapfile):
    """Transform binaries into the preferred forms for sim_verilator.

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
        vmem = rom
    elif ctx.attr.kind == "ram":
        default = elf
        rom = None
        rom32 = None

        # Generate Un-scrambled RAM VMEM (for testing SRAM injection in DV)
        vmem = convert_to_vmem(
            ctx,
            name = name,
            src = signed_bin if signed_bin else binary,
            word_size = 32,
        )
    elif ctx.attr.kind == "flash":
        vmem = convert_to_vmem(
            ctx,
            name = name,
            src = signed_bin if signed_bin else binary,
            word_size = 64,
        )
        default = vmem
        rom = None
        rom32 = None
    else:
        fail("Not implemented: kind ==", ctx.attr.kind)

    return {
        "elf": elf,
        "binary": binary,
        "default": vmem,
        "rom": rom,
        "signed_bin": signed_bin,
        "disassembly": disassembly,
        "mapfile": mapfile,
        "vmem": vmem,
        "rom32": rom32,
    }

def _test_dispatch(ctx, exec_env, firmware):
    """Dispatch a test for the sim_verilator environment.

    Args:
      ctx: The rule context.
      exec_env: The ExecEnvInfo for this environment.
      firmware: A label with a SimVerilatorBinaryInfo provider attached.
    Returns:
      (File, List[File]) The test script and needed runfiles.
    """
    if ctx.attr.kind == "ram":
        fail("verilator is not capable of executing RAM tests")

    test_harness, data_labels, data_files, param, action_param = common_test_setup(ctx, exec_env, firmware)

    # Perform all relevant substitutions on the test_cmd.
    test_cmd = get_fallback(ctx, "attr.test_cmd", exec_env)
    test_cmd = test_cmd.format(**param)
    test_cmd = ctx.expand_location(test_cmd, data_labels)

    # Get the pre-test_cmd args.
    args = get_fallback(ctx, "attr.args", exec_env)
    if ctx.attr.kind == "rom":
        # FIXME: This is a bit of inside-baseball: We know the opentitantool
        # args for a verilator based test will contain an argument with the
        # firmware substitution.  For a ROM test, we eliminate this arg because
        # we don't want to load any firmware.
        args = [a for a in args if "{firmware}" not in a]
    args = " ".join(args).format(**param)
    args = ctx.expand_location(args, data_labels)

    # Construct the test script
    script = ctx.actions.declare_file(ctx.attr.name + ".bash")
    ctx.actions.write(
        script,
        _TEST_SCRIPT.format(
            test_harness = test_harness.executable.short_path,
            args = args,
            test_cmd = test_cmd,
        ),
        is_executable = True,
    )
    return script, data_files

def _sim_verilator(ctx):
    fields = exec_env_as_dict(ctx)
    return ExecEnvInfo(
        provider = SimVerilatorBinaryInfo,
        test_dispatch = _test_dispatch,
        transform = _transform,
        **fields
    )

sim_verilator = rule(
    implementation = _sim_verilator,
    attrs = exec_env_common_attrs(),
    toolchains = [LOCALTOOLS_TOOLCHAIN],
)

def verilator_params(
        tags = [],
        timeout = "moderate",
        local = True,
        test_harness = None,
        binaries = {},
        rom = None,
        rom_ext = None,
        otp = None,
        test_cmd = "",
        data = [],
        **kwargs):
    """A macro to create verilator parameters for OpenTitan tests.

    Args:
      tags: The test tags to apply to the test rule.
      timeout: The timeout to apply to the test rule.
      local: Whether to set the `local` flag on this test.
      test_harness: Use an alternative test harness for this test.
      binaries: Dict of binaries labels to substitution parameter names.
      rom: Use an alternate ROM for this test.
      rom_ext: Use an alternate ROM_EXT for this test.
      otp: Use an alternate OTP configuration for this test.
      test_cmd: Use an alternate test_cmd for this test.
      data: Additional files needed by this test.
      kwargs: Additional key-value pairs to override in the test `param` dict.
    Returns:
      struct of test parameters.
    """
    return struct(
        tags = ["verilator", "cpu:5"] + tags,
        timeout = timeout,
        local = local,
        test_harness = test_harness,
        binaries = binaries,
        rom = rom,
        rom_ext = rom_ext,
        otp = otp,
        bitstream = None,
        test_cmd = test_cmd,
        data = data,
        param = kwargs,
    )
