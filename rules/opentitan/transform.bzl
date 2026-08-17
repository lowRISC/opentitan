# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//rules:common_settings.bzl", "BuildSettingInfo")
load("@rules_cc//cc:action_names.bzl", "OBJ_COPY_ACTION_NAME")
load("@rules_cc//cc:find_cc_toolchain.bzl", "find_cc_toolchain")
load("@bazel_skylib//lib:paths.bzl", "paths")
load("@lowrisc_opentitan//rules/opentitan:util.bzl", "get_override")
load("//rules:actions.bzl", "OT_ACTION_NM", "OT_ACTION_OBJDUMP")

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

def obj_list_symbols(ctx, **kwargs):
    """Use nm to list all symbols.

    Args:
      ctx: The context object for this rule.
      kwargs: Overrides of values normally retrived from the context object.
        output: The name of the output file.  Constructed from `name` if not
                specified.
        src: The src File object.
    Returns:
      The output File.
    """
    cc_toolchain = find_cc_toolchain(ctx)
    feature_config = cc_common.configure_features(
        ctx = ctx,
        cc_toolchain = cc_toolchain,
        requested_features = ctx.features,
        unsupported_features = ctx.disabled_features,
    )
    nm = cc_common.get_tool_for_action(
        feature_configuration = feature_config,
        action_name = OT_ACTION_NM,
    )

    output = kwargs.get("output")
    if not output:
        name = get_override(ctx, "attr.name", kwargs)
        output = "{}.nm".format(name)

    output = ctx.actions.declare_file(output)
    src = get_override(ctx, "attr.src", kwargs)

    ctx.actions.run_shell(
        outputs = [output],
        inputs = [src] + cc_toolchain.all_files.to_list(),
        arguments = [
            nm,
            src.path,
            output.path,
        ],
        command = "$1 $2 > $3",
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
        fill: The byte value used to pad to word alignment, e.g. "0xff".
              Defaults to "0xff" (flash's unprogrammed state); callers
              producing RRAM images should pass "0x00" (RRAM's unprogrammed
              state).
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

    fill_str = kwargs.get("fill", "0xff")

    ctx.actions.run(
        outputs = [output],
        inputs = [src],
        arguments = [
            src.path,
            "--binary",
            # Reverse the endianness of every word. srec_cat's --byte-swap
            # width is in bits, matching word_size directly.
            "--offset",
            "0x0",
            "--byte-swap",
            str(word_size),
            # Pad to word alignment
            "--fill",
            fill_str,
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

def scramble_rram(ctx, **kwargs):
    """Scramble a VMEM file according to a RRAM scrambling configuration.

    Args:
      ctx: The context object for this rule.
      kwargs: Overrides of values normally retrived from the context object.
        output: The name of the output file.  Constructed from `name` and `suffix`
                 if not specified.
        suffix: The suffix to give the file if the output isn't specified.
        src: The src File object.
        otp: The OTP settings.
        otp_mmap: The OTP memory mapping file.
        slot: Which firmware slot `src` was linked for ("a" or "b"). This matters for bkdr loading
        the NVM content to the RRAM because RRAM's address-infection and scrambling depend on the
        absolute RRAM address.

        top_secret_cfg: The secret configuration file.
        otp_data_perm: The OTP data permutation configuration.
        _tool: The rram scrambling script.

    Returns:
      The transformed File.
    """
    output = kwargs.get("output")
    if not output:
        name = get_override(ctx, "attr.name", kwargs)
        suffix = get_override(ctx, "attr.suffix", kwargs)
        output = "{}.{}".format(name, suffix)

    src = get_override(ctx, "file.src", kwargs)
    otp = get_override(ctx, "file.otp", kwargs)
    slot = get_override(ctx, "attr.slot", kwargs)
    if slot == "virtual":
        fail("Cannot scramble an RRAM image for the \"virtual\" slot.")

    output = ctx.actions.declare_file(output)

    inputs = [src]
    arguments = [
        "--in-rram-vmem",
        src.path,
        "--out-rram-vmem",
        output.path,
        "--slot",
        slot,
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

def rram_otp_image(ctx, exec_env, otp_attr):
    """Reformats an exec_env's `otp` attribute into the RRAM-native layout that backdoor-loading
    OTP into the RRAM data array expects (OTP lives in the tail pages of the RRAM data array now,
    see rram_ctrl_pkg.sv - there's no standalone OTP array to backdoor-load into any more).

    If `otp_attr` is an otp_image() target, it already carries this reformatted output in its
    `rram_otp` output group (see rules/otp.bzl) - reuse that instead of reformatting again, so
    this is a single gen-rram-img.py invocation per otp_image() target rather than one per
    consumer, and backdoor loading uses the exact same OTP content the rest of this exec_env is
    configured for (e.g. for scrambling-key derivation). Falls back to reformatting `otp_attr`
    itself only if it isn't an otp_image() output (e.g. some other override).

    Args:
      ctx: The rule context.
      exec_env: The ExecEnvInfo for this environment.
      otp_attr: The unresolved `otp` attribute (a File, or a Target with DefaultInfo).
    Returns:
      File: the reformatted OTP image, or None if there's nothing to reformat (no `otp_attr`,
      or this exec_env has no rram_scramble_tool configured).
    """
    if not otp_attr:
        return None
    if type(otp_attr) == "File":
        otp_file = otp_attr
    else:
        if OutputGroupInfo in otp_attr and "rram_otp" in otp_attr[OutputGroupInfo]:
            existing = otp_attr[OutputGroupInfo].rram_otp.to_list()
            if existing:
                return existing[0]
        files = otp_attr[DefaultInfo].files.to_list()
        if len(files) != 1:
            fail("Expected exactly one file in", otp_attr, ", but got", files)
        otp_file = files[0]

    if not exec_env.rram_scramble_tool:
        return None

    output = ctx.actions.declare_file(ctx.attr.name + ".otp.rram.vmem")
    args = ctx.actions.args()
    args.add("--in-otp-vmem", otp_file)
    args.add("--out-otp-vmem", output)
    args.add("--top-secret-cfg", exec_env.top_secret_cfg)
    if exec_env.otp_data_perm:
        args.add("--otp-data-perm", str(exec_env.otp_data_perm[BuildSettingInfo].value))
    ctx.actions.run(
        outputs = [output],
        inputs = [otp_file, exec_env.top_secret_cfg],
        arguments = [args],
        executable = exec_env.rram_scramble_tool.files_to_run,
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
