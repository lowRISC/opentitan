# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "@lowrisc_opentitan//rules/opentitan:providers.bzl",
    "Cw305BinaryInfo",
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

# Memories to be loaded onto the FPGA after the bitstream is loaded
# to replicate the specified execution environment.
FPGA_LOADED_MEMORIES = [
    "rom",
    "otp",
]

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
            rom_scramble_tool = ctx.executable.rom_scramble_tool,
            top_gen_hjson = exec_env.top_gen_hjson,
            top_secret_cfg = exec_env.top_secret_cfg,
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
      testopt_clear_before_test: If True, reset the state of the FPGA before
        the test (including all non-volatile memory). Currently implemented
        by clearing the FPGA bitstream.
      testopt_clear_after_test: If True, reset the state of the FPGA after
        the test (including all non-volatile memory). Currently implemneted
        by clearing the FPGA bitstream.
      testopt_needs_jtag: If True, tests require JTAG access.

    Common Param Fields:
      exit_success: The console output for test success.
      exit_failure: The console output for test failure.
      jtag_test_cmd: The JTAG test command.
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
        test_setup_cmd.append('--exec="fpga load-bitstream {jtag_test_cmd} {bitstream}"')

    # Reset OT and enter the backdoor loader
    test_setup_cmd.append('--exec="fpga backdoor enter"')

    # Zero all flash pages and SRAM to replicate a new bitstream.
    # Eventually, this should be replaced with flash info splicing.
    #
    # This is necessary as tests tend not to be judicious about clearing non-volatile
    # state both before and after running, allowing tests to have side effects and
    # influence each other.
    #
    # In `sw/device/silicon_creator/lib/ownership/test_owner.c`, we override the weak
    # `sku_creator_owner_init` symbol for FPGA environments. We detect bad ownership states
    # from the active boot data and thus initialize a default ownership configuration which
    # can be used for testing on FPGA. This is a workaround for the lack of info page
    # splicing, but means that for now we need to make sure that at least the boot data
    # info pages are cleared between each run.
    backdoor_writes = "--clear AON=ALL --clear SRAM=ALL"
    backdoor_writes += " --clear FB0=ALL --clear FI00=ALL --clear FI01=ALL --clear FI02=ALL"
    backdoor_writes += " --clear FB1=ALL --clear FI10=ALL --clear FI11=ALL --clear FI12=ALL"

    # Load the ROM & OTP over the backdoor loader. ROM is read-only once mission mode is
    # entered, so its content can't have changed since the last time this FPGA was preloaded
    # with the same image; check its hash first and skip the (slow) preload when unchanged.
    if "rom" in param:
        backdoor_writes += " --write ROM={rom}"
        backdoor_writes += " --check-memory-hash ROM"
    if "otp" in param:
        backdoor_writes += " --write OTP={otp}"
    test_setup_cmd.append('--exec="fpga backdoor {{jtag_test_cmd}} batch {backdoor_writes} --start"'.format(backdoor_writes = backdoor_writes))

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
        fail("FPGA is not capable of executing ROM tests")

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
      needs_jtag: If this test requires JTAG access, set this to True.
      test_cmd: Use an alternate test_cmd for this test.
      data: Additional files needed by this test.
      kwargs: Additional key-value pairs to override in the test `param` dict.
    Returns:
      struct of test parameters.
    """

    if needs_jtag:
        kwargs["testopt_needs_jtag"] = "True"
    return struct(
        # We do not yet know what FPGA platform the test will target (as this is
        # defined in the execution environment), so we do not know that tag
        # (out of: "cw305", "cw340", ...") to apply. Therefore, we apply the tag
        # via the "_hacky_tags" macro in "rules/opentitan/defs.bzl".
        tags = ["exclusive"] + tags,
        timeout = timeout,
        test_harness = test_harness,
        binaries = binaries,
        rom = rom,
        rom_ext = rom_ext,
        otp = otp,
        bitstream = bitstream,
        # FPGA tests always need JTAG for the bkdr_loader flow.
        needs_jtag = True,
        test_cmd = test_cmd,
        data = data,
        param = kwargs,
        post_test_cmd = post_test_cmd,
        post_test_harness = post_test_harness,
        defines = defines,
    )
