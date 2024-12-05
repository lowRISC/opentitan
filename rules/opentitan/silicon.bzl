# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "@lowrisc_opentitan//rules/opentitan:providers.bzl",
    "SiliconBinaryInfo",
)
load(
    "@lowrisc_opentitan//rules/opentitan:transform.bzl",
    "convert_to_scrambled_rom_vmem",
    "convert_to_vmem",
    "extract_software_logs",
    "scramble_flash",
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
load("//rules/opentitan:toolchain.bzl", "LOCALTOOLS_TOOLCHAIN")

_TEST_SCRIPT = """#!/bin/bash
set -e

TEST_CMD=({test_cmd})
echo Invoking test: {test_harness} {args} "$@" "${{TEST_CMD[@]}}"
RUST_BACKTRACE=1 {test_harness} {args} "$@" "${{TEST_CMD[@]}}"
"""

def _transform(ctx, exec_env, name, elf, binary, signed_bin, disassembly, mapfile):
    """Transform binaries into the preferred forms for silicon.

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
        default = rom
        vmem = rom
    elif ctx.attr.kind == "ram":
        default = elf
        rom = None
        vmem = None
    elif ctx.attr.kind == "flash":
        default = signed_bin if signed_bin else binary
        rom = None

        # Build VMEM images to enable GLS testing.
        vmem_base = convert_to_vmem(
            ctx,
            name = name,
            src = default,
            word_size = 64,
        )
        vmem = scramble_flash(
            ctx,
            name = name,
            suffix = "64.scr.vmem",
            src = vmem_base,
            otp = get_fallback(ctx, "file.otp", exec_env),
            otp_mmap = exec_env.otp_mmap,
            otp_seed = exec_env.otp_seed,
            otp_data_perm = exec_env.otp_data_perm,
            _tool = exec_env.flash_scramble_tool.files_to_run,
        )
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
        "mapfile": mapfile,
        "hashfile": hashfile,
        "vmem": vmem,
        "logs": logs,
    }

def _test_dispatch(ctx, exec_env, firmware):
    """Dispatch a test for the silicon environment.

    Args:
      ctx: The rule context.
      exec_env: The ExecEnvInfo for this environment.
      firmware: A label with a SiliconBinaryInfo provider attached.
    Returns:
      (File, List[File]) The test script and needed runfiles.
    """
    if ctx.attr.kind == "rom":
        fail("Silicon is not capable of executing ROM tests")

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
        ),
        is_executable = True,
    )
    return script, data_files

def _silicon(ctx):
    fields = exec_env_as_dict(ctx)
    return ExecEnvInfo(
        provider = SiliconBinaryInfo,
        test_dispatch = _test_dispatch,
        transform = _transform,
        **fields
    )

silicon = rule(
    implementation = _silicon,
    attrs = exec_env_common_attrs(),
    toolchains = [LOCALTOOLS_TOOLCHAIN],
)

def silicon_params(
        tags = [],
        timeout = "short",
        local = True,
        rom_ext = None,
        test_harness = None,
        binaries = {},
        changes_otp = False,
        needs_jtag = False,
        test_cmd = "",
        data = [],
        defines = [],
        **kwargs):
    """A macro to create Silicon parameters for OpenTitan tests.

    Args:
      tags: The test tags to apply to the test rule.
      timeout: The timeout to apply to the test rule.
      local: Whether to set the `local` flag on this test.
      test_harness: Use an alternative test harness for this test.
      binaries: Dict of binary labels to substitution parameter names.
      rom_ext: Use an alternate ROM_EXT for this test.
      changes_otp: Whether this test may change the OTP.
      needs_jtag: If this test requires JTAG access, set this to True.
      test_cmd: Use an alternate test_cmd for this test.
      data: Additional files needed by this test.
      kwargs: Additional key-value pairs to override in the test `param` dict.
    Returns:
      struct of test parameters.
    """
    return struct(
        tags = ["silicon", "exclusive"] + (["changes_otp"] if changes_otp else []) + tags,
        timeout = timeout,
        local = local,
        test_harness = test_harness,
        binaries = binaries,
        rom = None,
        rom_ext = rom_ext,
        otp = None,
        bitstream = None,
        changes_otp = None,
        needs_jtag = needs_jtag,
        test_cmd = ("""
            {jtag_test_cmd}
        """ if needs_jtag else "") + test_cmd,
        data = data,
        param = kwargs,
        defines = defines,
    )
