# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//rules:common_settings.bzl", "BuildSettingInfo")
load("@rules_cc//cc:find_cc_toolchain.bzl", "find_cc_toolchain")
load("@bazel_skylib//lib:paths.bzl", "paths")
load("@lowrisc_opentitan//rules/opentitan:util.bzl", "get_override")

def obj_transform(ctx, **kwargs):
    """Transform an object file via objcopy.

    Args:
      ctx: The context object for this rule.
      kwargs: Overrides of values normally retrived from the context object.
        output: The name of the output file.  Constructed from `name` and `suffix`
                 if not specified.
        src: The src File object.
        format: The objcopy output-format.
    Returns:
      The transformed File.
    """
    cc_toolchain = find_cc_toolchain(ctx).cc
    output = kwargs.get("output")
    if not output:
        name = get_override(ctx, "attr.name", kwargs)
        suffix = get_override(ctx, "attr.suffix", kwargs)
        output = "{}.{}".format(name, suffix)

    output = ctx.actions.declare_file(output)
    src = get_override(ctx, "attr.src", kwargs)
    out_format = get_override(ctx, "attr.format", kwargs)

    ctx.actions.run(
        outputs = [output],
        inputs = [src] + cc_toolchain.all_files.to_list(),
        arguments = [
            "--output-target",
            out_format,
            src.path,
            output.path,
        ],
        executable = cc_toolchain.objcopy_executable,
    )
    return output

def obj_disassemble(ctx, **kwargs):
    """Disassemble an input file.

    Args:
      ctx: The context object for this rule.
      kwargs: Overrides of values normally retrived from the context object.
        output: The name of the output file.  Constructed from `name` if not
                specified.
        src: The src File object.
    Returns:
      The disassembled File.
    """
    cc_toolchain = find_cc_toolchain(ctx).cc
    output = kwargs.get("output")
    if not output:
        name = get_override(ctx, "attr.name", kwargs)
        output = "{}.dis".format(name)

    output = ctx.actions.declare_file(output)
    src = get_override(ctx, "attr.src", kwargs)

    ctx.actions.run_shell(
        outputs = [output],
        inputs = [src] + cc_toolchain.all_files.to_list(),
        arguments = [
            cc_toolchain.objdump_executable,
            src.path,
            output.path,
        ],
        execution_requirements = {
            "no-sandbox": "",
        },
        command = "$1 -wx --disassemble --line-numbers --disassemble-zeroes --source --visualize-jumps $2 | expand > $3",
    )
    return output

def convert_to_vmem(ctx, **kwargs):
    """Transform a binary to a VMEM file.

    Args:
      ctx: The context object for this rule.
      kwargs: Overrides of values normally retrived from the context object.
        output: The name of the output file.  Constructed from `name` and `suffix`
                 if not specified.
        src: The src File object.
        format: The objcopy output-format.
    Returns:
      The transformed File.
    """
    output = kwargs.get("output")
    word_size = get_override(ctx, "attr.word_size", kwargs)
    if not output:
        name = get_override(ctx, "attr.name", kwargs)
        output = "{}.{}.vmem".format(name, word_size)

    output = ctx.actions.declare_file(output)
    src = get_override(ctx, "attr.src", kwargs)

    ctx.actions.run(
        outputs = [output],
        inputs = [src],
        arguments = [
            src.path,
            "--binary",
            # Reverse the endianness of every word.
            "--offset",
            "0x0",
            "--byte-swap",
            str(word_size // 8),
            # Pad to word alignment
            "--fill",
            "0xff",
            "-within",
            src.path,
            "-binary",
            "-range-pad",
            str(word_size // 8),
            # Output a VMEM file with specified word size
            "--output",
            output.path,
            "--vmem",
            str(word_size),
        ],
        # This this executable is expected to be installed (as required by the
        # srecord package in apt-requirements.txt).
        executable = "srec_cat",
        use_default_shell_env = True,
    )
    return output

def scramble_flash(ctx, **kwargs):
    """Scramble a VMEM file according to a flash scrambling configuration.

    Args:
      ctx: The context object for this rule.
      kwargs: Overrides of values normally retrived from the context object.
        output: The name of the output file.  Constructed from `name` and `suffix`
                 if not specified.
        suffix: The suffix to give the file if the ouput isn't specified.
        src: The src File object.
        otp: The OTP settings.
        otp_mmap: The OTP memory mapping file.
        otp_seed: The OTP seed.
        otp_data_perm: The OTP data permutation configuration.
        _tool: The flash scrambling script.

    Returns:
      The transformed File.
    """
    output = kwargs.get("output")
    if not output:
        name = get_override(ctx, "attr.name", kwargs)
        suffix = get_override(ctx, "attr.suffix", kwargs)
        output = "{}.{}".format(name, suffix)

    output = ctx.actions.declare_file(output)
    src = get_override(ctx, "attr.src", kwargs)
    otp = get_override(ctx, "file.otp", kwargs)

    inputs = [src]
    arguments = [
        "--in-flash-vmem",
        src.path,
        "--out-flash-vmem",
        output.path,
    ]
    if otp:
        otp_mmap = get_override(ctx, "file.otp_mmap", kwargs)
        otp_seed = get_override(ctx, "attr.otp_seed", kwargs)
        arguments.extend([
            "--in-otp-vmem",
            otp.path,
            "--in-otp-mmap",
            otp_mmap.path,
            "--otp-seed",
            str(otp_seed[BuildSettingInfo].value),
        ])
        inputs.extend([otp, otp_mmap])

        otp_data_perm = get_override(ctx, "attr.otp_data_perm", kwargs)
        if otp_data_perm:
            arguments.extend(["--otp-data-perm", str(otp_data_perm[BuildSettingInfo].value)])

    tool = get_override(ctx, "executable._tool", kwargs)
    ctx.actions.run(
        outputs = [output],
        inputs = inputs,
        arguments = arguments,
        executable = tool,
    )
    return output

def extract_software_logs(ctx, **kwargs):
    """Extract the software logs database from an ELF file.

    Args:
      ctx: The context object for this rule.
      kwargs: Overrides of values normally retrived from the context object.
        name: The basename of the logs output files.
        src: The src File object.
        _tool: The log extraction utility.

    Returns:
      (File, File): The logs and rodata text databases.
    """
    name = get_override(ctx, "attr.name", kwargs)
    output_logs = ctx.actions.declare_file(name + ".logs.txt")
    output_rodata = ctx.actions.declare_file(name + ".rodata.txt")
    src = get_override(ctx, "attr.src", kwargs)
    tool = get_override(ctx, "executable._tool", kwargs)
    ctx.actions.run(
        outputs = [output_logs, output_rodata],
        inputs = [src],
        arguments = [
            "--elf-file",
            src.path,
            "--logs-fields-section",
            ".logs.fields",
            "--name",
            name,
            "--outdir",
            output_logs.dirname,
        ],
        executable = tool,
    )
    return (output_logs, output_rodata)

def convert_to_scrambled_rom_vmem(ctx, **kwargs):
    """Transform a binary to a VMEM file.

    Args:
      ctx: The context object for this rule.
      kwargs: Overrides of values normally retrived from the context object.
        output: The name of the output file.  Constructed from `name` and `suffix`
                 if not specified.
        src: The src File object.
        rom_scramble_config: The scrambling config.
        rom_scramble_tool: The scrambling tool.
    Returns:
      The transformed File.
    """
    output = kwargs.get("output")
    if not output:
        name = get_override(ctx, "attr.name", kwargs)
        suffix = get_override(ctx, "attr.suffix", kwargs)
        output = "{}.{}".format(name, suffix)

    output = ctx.actions.declare_file(output)
    src = get_override(ctx, "attr.src", kwargs)

    config = get_override(ctx, "file.rom_scramble_config", kwargs)
    tool = get_override(ctx, "executable.rom_scramble_tool", kwargs)

    ctx.actions.run(
        outputs = [output],
        inputs = [src, tool, config],
        arguments = [
            config.path,
            src.path,
            output.path,
        ],
        executable = tool,
    )
    return output
