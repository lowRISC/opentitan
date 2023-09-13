# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@lowrisc_opentitan//rules/opentitan:providers.bzl", "Cw310BinaryInfo")
load("@lowrisc_opentitan//rules/opentitan:util.bzl", "get_fallback", "get_files")
load(
    "//rules/opentitan:exec_env.bzl",
    "ExecEnvInfo",
    "exec_env_as_dict",
    "exec_env_common_attrs",
)

_TEST_SCRIPT = """#!/bin/bash
set -e

echo Invoking test: {test_harness} {args} {test_cmd}
RUST_BACKTRACE=1 {test_harness} {args} {test_cmd}
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

    # The CW310 environment doesn't need any transformations; just
    # return the files as a dictionary.
    default = signed_bin if signed_bin else binary
    return {
        "elf": elf,
        "binary": binary,
        "default": default,
        "signed_bin": signed_bin,
        "disassembly": disassembly,
        "mapfile": mapfile,
    }

def _create_provider(ctx, exec_env, **kwargs):
    """Create a provider for this exec_env."""
    return Cw310BinaryInfo(**kwargs)

def _get_provider(item):
    """Given an attr from a rule, return the Cw310BinaryInfo provider if preseent.

    Args:
      item: a label that may have a provider attached.
    Returns:
      Cw310BinaryInfo or None
    """
    if Cw310BinaryInfo in item:
        return item[Cw310BinaryInfo]
    return None

def _test_dispatch(ctx, exec_env, provider):
    """Dispatch a test for the fpga_cw310 environment.

    Args:
      ctx: The rule context.
      exec_env: The ExecEnvInfo for this environment.
      provider: A label with a Cw310BinaryInfo provider attached.
    Returns:
      (File, List[File]) The test script and needed runfiles.
    """

    # If there is no explicitly specified test_harness, then the harness is opentitantool.
    test_harness = ctx.executable.test_harness
    if test_harness == None:
        test_harness = exec_env._opentitantool

    # Get the files we'll need to run the test.
    bitstream = get_fallback(ctx, "file.bitstream", exec_env)
    otp = get_fallback(ctx, "file.otp", exec_env)
    rom = get_fallback(ctx, "file.rom", exec_env)
    data_labels = ctx.attr.data + exec_env.data
    data_files = get_files(data_labels)
    if bitstream:
        data_files.append(bitstream)
    if rom:
        data_files.append(rom)
    if otp:
        data_files.append(otp)
    data_files.append(provider.default)
    data_files.append(test_harness)

    # Construct a param dictionary by combining the exec_env.param, the rule's
    # param and and some extra file references.
    param = dict(exec_env.param)
    param.update(ctx.attr.param)
    if bitstream and "bitstream" not in param:
        param["bitstream"] = bitstream.short_path
    if rom and "rom" not in param:
        param["rom"] = rom.short_path
    if otp and "otp" not in param:
        param["otp"] = otp.short_path
    if "firmware" not in param:
        param["firmware"] = provider.default.short_path

    # FIXME: maybe splice a bitstream here

    # Perform all relevant substitutions on the test_cmd.
    test_cmd = get_fallback(ctx, "attr.test_cmd", exec_env)
    test_cmd = test_cmd.replace("\n", " ").format(**param)
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
        get_provider = _get_provider,
        test_dispatch = _test_dispatch,
        transform = _transform,
        create_provider = _create_provider,
        **fields
    )

fpga_cw310 = rule(
    implementation = _fpga_cw310,
    attrs = exec_env_common_attrs(),
)

def cw310_params(
        tags = [],
        timeout = "short",
        local = True,
        test_harness = None,
        rom = None,
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
      rom: Use an alternate ROM for this test.
      otp: Use an alternate OTP configuration for this test.
      bitstream: Use an alternate bitstream for this test.
      test_cmd: Use an alternate test_cmd for this test.
      data: Additional files needed by this test.
      kwargs: Additional key-value pairs to override in the test `param` dict.
    Returns:
      struct of test parameters.
    """
    return struct(
        tags = ["cw310", "exclusive"] + tags,
        timeout = timeout,
        local = local,
        test_harness = test_harness,
        rom = rom,
        otp = otp,
        bitstream = bitstream,
        test_cmd = test_cmd,
        data = data,
        param = kwargs,
    )
