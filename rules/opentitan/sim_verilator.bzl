# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@lowrisc_opentitan//rules/opentitan:providers.bzl", "SimVerilatorBinaryInfo", "get_one_binary_file")
load("@lowrisc_opentitan//rules/opentitan:util.bzl", "get_fallback", "get_files", "get_override")
load(
    "//rules/opentitan:exec_env.bzl",
    "ExecEnvInfo",
    "exec_env_as_dict",
    "exec_env_common_attrs",
)
load(
    "@lowrisc_opentitan//rules/opentitan:transform.bzl",
    "convert_to_scrambled_rom_vmem",
    "convert_to_vmem",
)

_TEST_SCRIPT = """#!/bin/bash
set -e

echo Invoking test: {test_harness} {args} {test_cmd}
RUST_BACKTRACE=1 {test_harness} {args} {test_cmd}
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
        default = rom
        vmem = rom
    elif ctx.attr.kind == "flash":
        vmem = convert_to_vmem(
            ctx,
            name = name,
            src = signed_bin if signed_bin else binary,
            word_size = 64,
        )
        default = vmem
        rom = None
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
    }

def _create_provider(ctx, exec_env, **kwargs):
    """Create a provider for this exec_env."""
    return SimVerilatorBinaryInfo(**kwargs)

def _get_provider(item):
    """Given an attr from a rule, return the SimVerilatorBinaryInfo provider if preseent.

    Args:
      item: a label that may have a provider attached.
    Returns:
      SimVerilatorBinaryInfo or None
    """
    if SimVerilatorBinaryInfo in item:
        return item[SimVerilatorBinaryInfo]
    return None

def _test_dispatch(ctx, exec_env, provider):
    """Dispatch a test for the sim_verilator environment.

    Args:
      ctx: The rule context.
      exec_env: The ExecEnvInfo for this environment.
      provider: A label with a SimVerilatorBinaryInfo provider attached.
    Returns:
      (File, List[File]) The test script and needed runfiles.
    """

    # If there is no explicitly specified test_harness, then the harness is opentitantool.
    test_harness = ctx.executable.test_harness
    if test_harness == None:
        test_harness = exec_env._opentitantool

    # Get the files we'll need to run the test.
    otp = get_fallback(ctx, "file.otp", exec_env)
    rom = get_fallback(ctx, "attr.rom", exec_env)
    data_labels = ctx.attr.data + exec_env.data
    data_files = get_files(data_labels)
    if rom:
        rom = get_one_binary_file(rom, field = "rom", providers = [SimVerilatorBinaryInfo])
        data_files.append(rom)
    if otp:
        data_files.append(otp)
    data_files.append(provider.default)
    data_files.append(test_harness)
    if ctx.attr.kind == "rom":
        # For a ROM test, the default test binary is the item to load into ROM.
        rom = provider.default

    # Construct a param dictionary by combining the exec_env.param, the rule's
    # param and and some extra file references.
    param = dict(exec_env.param)
    param.update(ctx.attr.param)
    if rom and "rom" not in param:
        param["rom"] = rom.short_path
    if otp and "otp" not in param:
        param["otp"] = otp.short_path
    if "firmware" not in param:
        param["firmware"] = provider.default.short_path

    # Perform all relevant substitutions on the test_cmd.
    test_cmd = get_fallback(ctx, "attr.test_cmd", exec_env)
    test_cmd = test_cmd.replace("\n", " ").format(**param)
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
            test_harness = test_harness.short_path,
            args = args,
            test_cmd = test_cmd,
        ),
        is_executable = True,
    )
    return script, data_files

def _sim_verilator(ctx):
    fields = exec_env_as_dict(ctx)
    return ExecEnvInfo(
        get_provider = _get_provider,
        test_dispatch = _test_dispatch,
        transform = _transform,
        create_provider = _create_provider,
        **fields
    )

sim_verilator = rule(
    implementation = _sim_verilator,
    attrs = exec_env_common_attrs(),
)

def verilator_params(
        tags = [],
        timeout = "moderate",
        local = True,
        test_harness = None,
        rom = None,
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
      rom: Use an alternate ROM for this test.
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
        rom = rom,
        otp = otp,
        bitstream = None,
        test_cmd = test_cmd,
        data = data,
        param = kwargs,
    )
