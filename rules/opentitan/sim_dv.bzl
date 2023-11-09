# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@lowrisc_opentitan//rules/opentitan:providers.bzl", "SimDvBinaryInfo")
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
    "extract_software_logs",
    "scramble_flash",
)
load("//rules/opentitan:toolchain.bzl", "LOCALTOOLS_TOOLCHAIN")

_TEST_SCRIPT = """#!/bin/bash
set -e

readonly DVSIM="util/dvsim/dvsim.py"
TEST_CMD=({test_cmd})
echo "At this time, dvsim.py must be run manually (after building SW) via:
${{DVSIM}} {args} ${{TEST_CMD[@]}}"
"""

def _transform(ctx, exec_env, name, elf, binary, signed_bin, disassembly, mapfile):
    """Transform binaries into the preferred forms for sim_dv.

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
    elif ctx.attr.kind == "ram":
        default = elf
        rom = None

        # Generate Un-scrambled RAM VMEM (for testing SRAM injection in DV)
        vmem = convert_to_vmem(
            ctx,
            name = name,
            src = signed_bin if signed_bin else binary,
            word_size = 32,
        )
    elif ctx.attr.kind == "flash":
        # First convert to VMEM, then scramble according to flash
        # scrambling settings.
        vmem = convert_to_vmem(
            ctx,
            name = name,
            src = signed_bin if signed_bin else binary,
            word_size = 64,
        )
        vmem = scramble_flash(
            ctx,
            name = name,
            suffix = "64.scr.vmem",
            src = vmem,
            otp = get_fallback(ctx, "file.otp", exec_env),
            otp_mmap = exec_env.otp_mmap,
            otp_seed = exec_env.otp_seed,
            otp_data_perm = exec_env.otp_data_perm,
            _tool = exec_env.flash_scramble_tool.files_to_run,
        )
        rom = None
        default = vmem
    else:
        fail("Not implemented: kind ==", ctx.attr.kind)

    logs = extract_software_logs(
        ctx,
        name = name,
        src = elf,
        _tool = exec_env.extract_sw_logs.files_to_run,
    )
    return {
        "elf": elf,
        "binary": binary,
        "default": default,
        "rom": rom,
        "signed_bin": signed_bin,
        "disassembly": disassembly,
        "logs": logs,
        "mapfile": mapfile,
        "vmem": vmem,
    }

def _test_dispatch(ctx, exec_env, firmware):
    """Dispatch a test for the sim_dv environment.

    Args:
      ctx: The rule context.
      exec_env: The ExecEnvInfo for this environment.
      firmware: A label with a SimDvBinaryInfo provider attached.
    Returns:
      (File, List[File]) The test script and needed runfiles.
    """
    test_harness, data_labels, data_files, param, action_param = common_test_setup(ctx, exec_env, firmware)

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
            test_harness = test_harness.executable.short_path,
            args = args,
            test_cmd = test_cmd,
            data_files = " ".join([f.path for f in data_files]),
        ),
        is_executable = True,
    )
    return script, data_files

def _sim_dv(ctx):
    fields = exec_env_as_dict(ctx)
    return ExecEnvInfo(
        provider = SimDvBinaryInfo,
        test_dispatch = _test_dispatch,
        transform = _transform,
        **fields
    )

sim_dv = rule(
    implementation = _sim_dv,
    attrs = exec_env_common_attrs(),
    toolchains = [LOCALTOOLS_TOOLCHAIN],
)

def dv_params(
        tags = [],
        timeout = "short",
        local = False,
        test_harness = None,
        binaries = None,
        rom = None,
        rom_ext = None,
        otp = None,
        test_cmd = "",
        data = [],
        **kwargs):
    """A macro to create dv parameters for OpenTitan tests.

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
        tags = ["dv"] + tags,
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
