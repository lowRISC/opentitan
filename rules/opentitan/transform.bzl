# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//rules:common_settings.bzl", "BuildSettingInfo")
load("@rules_cc//cc:action_names.bzl", "OBJ_COPY_ACTION_NAME")
load("@rules_cc//cc:find_cc_toolchain.bzl", "find_cc_toolchain")
load("@bazel_skylib//lib:paths.bzl", "paths")
load("@lowrisc_opentitan//rules/opentitan:util.bzl", "get_override")
load("@lowrisc_opentitan//rules:actions.bzl", "OT_ACTION_OBJDUMP")

def obj_transform(ctx, strip_llvm_prf_cnts = False, **kwargs):
    """Transform an object file via objcopy.

    Args:
      ctx: The context object for this rule.
      kwargs: Overrides of values normally retrived from the context object.
        output: The name of the output file.  Constructed from `name` and `suffix`
                 if not specified.
        src: The src File object.
        format: The objcopy output-format.
        strip_llvm_prf_cnts: Whether to strip the llvm coverage counter section.
    Returns:
      The transformed File.
    """
    cc_toolchain = find_cc_toolchain(ctx)
    feature_config = cc_common.configure_features(
        ctx = ctx,
        cc_toolchain = cc_toolchain,
        requested_features = ctx.features,
        unsupported_features = ctx.disabled_features,
    )
    objcopy = cc_common.get_tool_for_action(
        feature_configuration = feature_config,
        action_name = OBJ_COPY_ACTION_NAME,
    )

    output = kwargs.get("output")
    if not output:
        name = get_override(ctx, "attr.name", kwargs)
        suffix = get_override(ctx, "attr.suffix", kwargs)
        output = "{}.{}".format(name, suffix)

    output = ctx.actions.declare_file(output)
    src = get_override(ctx, "file.src", kwargs)
    out_format = get_override(ctx, "attr.format", kwargs)

    transform_inputs = [src]
    transform_flags = ["--output-target", out_format]

    if strip_llvm_prf_cnts:
        # Extract the initial contents of the `__llvm_prf_cnts` section.
        prf_cnts = ctx.actions.declare_file("{}.prf_cnts".format(output))
        ctx.actions.run(
            outputs = [prf_cnts],
            inputs = [src] + cc_toolchain.all_files.to_list(),
            arguments = [
                "--output-target",
                out_format,
                "--only-section",
                "__llvm_prf_cnts",
                "--gap-fill",
                "0xa5",
                src.path,
                prf_cnts.path,
            ],
            executable = objcopy,
        )

        # Checks the initial contents of the `__llvm_prf_cnts` section.
        prf_cnts_res = ctx.actions.declare_file("{}.prf_cnts_res".format(output))
        ctx.actions.run(
            outputs = [prf_cnts_res],
            inputs = [prf_cnts],
            arguments = [prf_cnts.path, prf_cnts_res.path],
            executable = ctx.executable._check_initial_coverage,
        )

        transform_inputs.append(prf_cnts_res)
        transform_flags.extend(["--remove-section", "__llvm_prf_cnts"])

    # Transforms the firmware format.
    ctx.actions.run(
        outputs = [output],
        inputs = transform_inputs + cc_toolchain.all_files.to_list(),
        arguments = transform_flags + [
            src.path,
            output.path,
        ],
        executable = objcopy,
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
    cc_toolchain = find_cc_toolchain(ctx)
    feature_config = cc_common.configure_features(
        ctx = ctx,
        cc_toolchain = cc_toolchain,
        requested_features = ctx.features,
        unsupported_features = ctx.disabled_features,
    )
    objdump = cc_common.get_tool_for_action(
        feature_configuration = feature_config,
        action_name = OT_ACTION_OBJDUMP,
    )

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
            objdump,
            src.path,
            output.path,
        ],
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
    src = get_override(ctx, "file.src", kwargs)

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
        suffix: The suffix to give the file if the output isn't specified.
        src: The src File object.
        otp: The OTP settings.
        otp_mmap: The OTP memory mapping file.

        top_secret_cfg: The secret configuration file.
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
    src = get_override(ctx, "file.src", kwargs)
    otp = get_override(ctx, "file.otp", kwargs)

    inputs = [src]
    arguments = [
        "--in-flash-vmem",
        src.path,
        "--out-flash-vmem",
        output.path,
    ]

    # Always get top_secret_cfg since the tool requires it
    top_secret_cfg = get_override(ctx, "file.top_secret_cfg", kwargs)
    arguments.extend(["--top-secret-cfg", top_secret_cfg.path])
    inputs.append(top_secret_cfg)

    if otp:
        arguments.extend([
            "--in-otp-vmem",
            otp.path,
        ])
        inputs.extend([otp])

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
        rom_scramble_tool: The scrambling tool.
        rom_scramble_mode: The scrambling mode.
        top_secret_cfg: The secrets configuration of the top.
    Returns:
      (The transformed File, The hashfile)
    """
    output = kwargs.get("output")
    if not output:
        name = get_override(ctx, "attr.name", kwargs)
        suffix = get_override(ctx, "attr.suffix", kwargs)
        output = "{}.{}".format(name, suffix)

    output = ctx.actions.declare_file(output)

    hashfile = ctx.actions.declare_file("{}.hash.c".format(output.basename))

    src = get_override(ctx, "attr.src", kwargs)

    top_config = get_override(ctx, "file.top_gen_hjson", kwargs)
    secrets = get_override(ctx, "file.top_secret_cfg", kwargs)
    tool = get_override(ctx, "executable.rom_scramble_tool", kwargs)
    mode = get_override(ctx, "attr.rom_scramble_mode", kwargs)

    ctx.actions.run(
        outputs = [output, hashfile],
        inputs = [src, tool, top_config, secrets],
        arguments = [
            top_config.path,
            secrets.path,
            mode,
            src.path,
            output.path,
            hashfile.path,
        ],
        executable = tool,
    )
    return (output, hashfile)
