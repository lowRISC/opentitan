# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@lowrisc_opentitan//rules/opentitan:providers.bzl", "SimDvBinaryInfo", "get_one_binary_file")
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
    "extract_software_logs",
    "scramble_flash",
)

_TEST_SCRIPT = """#!/bin/bash
set -e

readonly DVSIM="util/dvsim/dvsim.py"
echo "At this time, dvsim.py must be run manually (after building SW) via:
${{DVSIM}} {args} {test_cmd}"
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

def _test_dispatch(ctx, exec_env, provider):
    """Dispatch a test for the sim_dv environment.

    Args:
      ctx: The rule context.
      exec_env: The ExecEnvInfo for this environment.
      provider: A label with a SimDvBinaryInfo provider attached.
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
        rom = get_one_binary_file(rom, field = "rom", providers = [exec_env.provider])
        data_files.append(rom)
    if otp:
        data_files.append(otp)
    data_files.append(provider.default)
    data_files.extend(provider.logs)
    data_files.append(test_harness)

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
)

def dv_params(
        tags = [],
        timeout = "short",
        local = False,
        test_harness = None,
        rom = None,
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
      rom: Use an alternate ROM for this test.
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
        rom = rom,
        otp = otp,
        bitstream = None,
        test_cmd = test_cmd,
        data = data,
        param = kwargs,
    )
