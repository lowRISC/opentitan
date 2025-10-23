# Copyright lowRISC contributors (OpenTitan project).
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
    "recursive_format",
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
load("//rules/opentitan:toolchain.bzl", "LOCALTOOLS_TOOLCHAIN")

_TEST_COMMANDS = """
TEST_SETUP_CMD=({test_setup_cmd})
TEST_CMD=({test_cmd})
TEST_CLEANUP_CMD=({test_cleanup_cmd})
POST_TEST_CMD=({post_test_cmd})
"""

_TEST_SCRIPT = """#!/bin/bash
set -e

{test_commands}

export RUST_BACKTRACE=1

function cleanup {{
  {post_test_harness} "${{POST_TEST_CMD[@]}}"
  {opentitantool} {args} "${{TEST_CLEANUP_CMD[@]}}" no-op
}}

# Bazel will send a SIGTERM when the timeout expires and will
# wait for a short amount of time (local_termination_grace_seconds)
# before it kills the process. Therefore the trap will run even
# on timeout.
trap cleanup EXIT

set -x

{opentitantool} {args} "${{TEST_SETUP_CMD[@]}}" no-op
{test_harness} {args} "$@" "${{TEST_CMD[@]}}"
"""

def _transform(ctx, exec_env, name, elf, binary, signed_bin, disassembly, mapfile):
    """Transform binaries into the preferred forms for fpga_cw3{05,10,40}.

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
    hashfile = None
    if ctx.attr.kind == "rom":
        (rom, hashfile) = convert_to_scrambled_rom_vmem(
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
        "hashfile": hashfile,
    }

def _get_bool(param, name, default = "False"):
    value = param.get(name, default).lower()
    if value == "true":
        return True
    if value == "false":
        return False
    fail("Invalid boolean value {} for field {}".format(name, value))

def _get_test_commands(ctx, param, exec_env):
    """Process the testopt flags to generate test commands.

    Test Option Param Fields:
      testopt_bootstrap: If True, bootstrap the firmware before test.
      testopt_clear_before_test: If True, clear the bitstream before test.
      testopt_clear_after_test: If True, clear the bitstream after test.
      testopt_needs_jtag: If True, tests require JTAG access.

    Common Param Fields:
      exit_success: The console output for test success.
      exit_failure: The console output for test failure.
      jtag_test_cmd: The JTAG test command (if testopt_needs_jtag is True).
      bitstream: The bitstream to load before test.
      firmware: The firmware to load with bootstrap.

    Args:
      ctx: The rule context.
      param: A dictionary of key-value test parameters.
      exec_env: The ExecEnvInfo for this environment.

    Returns:
      (string, string) A tuple of (test_setup_cmd, test_cleanup_cmd), which are
      opentitantool arguments.
    """

    test_cmd = get_fallback(ctx, "attr.test_cmd", exec_env)

    # If no test_cmd or custom harness is specified, run the default console harness.
    if not test_cmd.strip() and not ctx.attr.test_harness:
        test_cmd = """
          console --non-interactive --exit-success='{exit_success}' --exit-failure='{exit_failure}'
        """

    if _get_bool(param, "testopt_needs_jtag"):
        test_cmd = " {jtag_test_cmd} " + test_cmd

    # Construct the opentitantool test setup commands
    test_setup_cmd = ['--exec="transport init"']
    if _get_bool(param, "testopt_clear_before_test"):
        test_setup_cmd.append('--exec="fpga clear-bitstream"')
    if "bitstream" in param:
        test_setup_cmd.append('--exec="fpga load-bitstream {bitstream}"')
    if _get_bool(param, "testopt_bootstrap") and "firmware" in param:
        test_setup_cmd.append('--exec="bootstrap --leave-in-reset --clear-uart=true {firmware}"')
    test_setup_cmd = "\n".join(test_setup_cmd)

    # Construct the opentitantool test cleanup commands
    test_cleanup_cmd = []
    if _get_bool(param, "testopt_clear_after_test"):
        test_cleanup_cmd.append('--exec="fpga clear-bitstream"')

    test_cleanup_cmd = "\n".join(test_cleanup_cmd)

    return _TEST_COMMANDS.format(
        test_setup_cmd = test_setup_cmd,
        test_cmd = test_cmd,
        test_cleanup_cmd = test_cleanup_cmd,
        post_test_cmd = ctx.attr.post_test_cmd,
    )

def _test_dispatch(ctx, exec_env, firmware):
    """Dispatch a test for the fpga_cw3{05,10,40} environment.

    Args:
      ctx: The rule context.
      exec_env: The ExecEnvInfo for this environment.
      firmware: A label with a Cw3{05,10,40}BinaryInfo provider attached.
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
        assemble = param.get("assemble")
        assemble = recursive_format(assemble, action_param)
        assemble = ctx.expand_location(assemble, data_labels)
        image = assemble_for_test(
            ctx,
            name = ctx.attr.name,
            spec = assemble.strip().split(" "),
            data_files = data_files,
            opentitantool = exec_env._opentitantool,
        )
        param["firmware"] = image.short_path
        action_param["firmware"] = image.path
        data_files.append(image)

    # FIXME: maybe splice a bitstream here

    # Get the pre-test_cmd args.
    args = get_fallback(ctx, "attr.args", exec_env)
    args = " ".join(args).format(**param)
    args = ctx.expand_location(args, data_labels)

    # Perform all relevant substitutions on the test_cmd.
    test_commands = _get_test_commands(ctx, param, exec_env)
    test_commands = test_commands.format(**param)
    test_commands = ctx.expand_location(test_commands, data_labels)

    # Construct the post test commands
    post_test_harness_path = ctx.executable.post_test_harness
    if post_test_harness_path != None:
        data_files.append(post_test_harness_path)
        post_test_harness_path = post_test_harness_path.short_path
    else:
        post_test_harness_path = ""

    # Construct the test script
    script = ctx.actions.declare_file(ctx.attr.name + ".bash")
    ctx.actions.write(
        script,
        _TEST_SCRIPT.format(
            test_harness = test_harness.executable.short_path,
            args = args,
            test_commands = test_commands,
            post_test_harness = post_test_harness_path,
            opentitantool = exec_env._opentitantool.executable.short_path,
        ),
        is_executable = True,
    )
    data_files.append(exec_env._opentitantool.executable)

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
    toolchains = [LOCALTOOLS_TOOLCHAIN],
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
    toolchains = [LOCALTOOLS_TOOLCHAIN],
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
    toolchains = [LOCALTOOLS_TOOLCHAIN],
)

def fpga_params(
        tags = [],
        timeout = "short",
        test_harness = None,
        binaries = {},
        rom = None,
        rom_ext = None,
        otp = None,
        bitstream = None,
        changes_otp = False,
        needs_jtag = False,
        test_cmd = "",
        data = [],
        defines = [],
        post_test_cmd = "",
        post_test_harness = None,
        **kwargs):
    """A macro to create CW3{05,10,40} parameters for OpenTitan tests.

    Args:
      tags: The test tags to apply to the test rule.
      timeout: The timeout to apply to the test rule.
      test_harness: Use an alternative test harness for this test.
      binaries: Dict of binary labels to substitution parameter names.
      rom: Use an alternate ROM for this test.
      rom_ext: Use an alternate ROM_EXT for this test.
      otp: Use an alternate OTP configuration for this test.
      bitstream: Use an alternate bitstream for this test.
      changes_otp: Whether this test may change the OTP. Bitstream will be cleared if True.
      needs_jtag: If this test requires JTAG access, set this to True.
      test_cmd: Use an alternate test_cmd for this test.
      data: Additional files needed by this test.
      kwargs: Additional key-value pairs to override in the test `param` dict.
    Returns:
      struct of test parameters.
    """
    if bitstream and (rom or otp):
        fail("Cannot use rom or otp with bitstream.")
    if not bitstream:
        bitstream = "@//hw/bitstream/universal:splice"

    # Clear bitstream after the test if it changes the OTP.
    if changes_otp:
        kwargs["testopt_clear_after_test"] = "True"
    if needs_jtag:
        kwargs["testopt_needs_jtag"] = "True"
    return struct(
        # We do not yet know what FPGA platform the test will target (as this is
        # defined in the execution environment), so we do not know that tag
        # (out of: "cw305", "cw310", ...") to apply. Therefore, we apply the tag
        # via the "_hacky_tags" macro in "rules/opentitan/defs.bzl".
        tags = ["exclusive"] + (["changes_otp"] if changes_otp else []) + tags,
        timeout = timeout,
        test_harness = test_harness,
        binaries = binaries,
        rom = rom,
        rom_ext = rom_ext,
        otp = otp,
        bitstream = bitstream,
        needs_jtag = needs_jtag,
        test_cmd = test_cmd,
        data = data,
        param = kwargs,
        post_test_cmd = post_test_cmd,
        post_test_harness = post_test_harness,
        defines = defines,
    )
