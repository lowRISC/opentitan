# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//rules:common_settings.bzl", "BuildSettingInfo")
load("@rules_cc//cc:action_names.bzl", "OBJ_COPY_ACTION_NAME")
load("@rules_cc//cc:find_cc_toolchain.bzl", "find_cc_toolchain")
load("@bazel_skylib//lib:paths.bzl", "paths")
load("@lowrisc_opentitan//rules/opentitan:util.bzl", "get_override")
load("//rules:actions.bzl", "OT_ACTION_NM", "OT_ACTION_OBJDUMP")

TransformInfo = provider(
    doc = "A provider holding a transform function used by `dispatch_transform`. See `dispatch_transform` for documentation.",
    fields = ["transform"],
)

DISPATCH_KIND_TRANSFORM_ATTR = {
    "kind_transform": attr.string_keyed_label_dict(
        providers = [TransformInfo],
        doc = "Mapping from kind to the transform functions, used by dispatch_transform.",
    ),
    "transform_hook": attr.label(
        providers = [TransformInfo],
        doc = "Transform hook applied after `kind_transform`, used by dispatch_transform.",
    ),
}

def dispatch_transform(ctx, exec_env, name, elf, binary, signed_bin, disassembly, mapfile):
    """Transform binaries into the preferred forms. This function uses the `kind` attribute
    of the binary and the `kind_transform`` of `exec_env` to dispatch the relevant transform function.
    Use `DISPATCH_KIND_TRANSFORM_ATTR` when adding it to the execution environment attributes.
    This function expects each dictionary entry in the `kind_transform` attribute to be a target
    with a `TransformInfo` provider. In addition, if present, this function will also apply the
    transform defined in the `transform_hook` attribute which applies to all kinds, and is applied after
    the one in `kind_transform`.

    The `TransformInfo` provider must contain a `transform` field whose prototype is
    as follows:
    ```py
    def transform(ctx, exec_env, name, inputs)
    ```
    The `ctx` attribute is the context of the binary/test rule when running the transform.
    The `exec_env` attribute is the execution environment for which the transform is done.
    The `name` attribute is the name of the target (build/test).
    The `inputs` attribute is a dictionary mapping strings to files or list of files.
    The function must return a dictionary in a similar form to `inputs`. Usually, the function
    will take the `inputs` dictionary and return the same dictionary with some additional entries
    added to it (see `merge_outputs`). The resulting dictionary will be returned by `dispatch_transform` and typically
    end up in the execution environment-specific provider (e.g. Cw340BinaryInfo) and in the output groups
    of the build/test rules.

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
    if not ctx.attr.kind in exec_env.kind_transform:
        fail("kind '{}' is not supported by execution environment {}".format(ctx.attr.kind, exec_env.exec_env))
    inputs = {
        "elf": elf,
        "binary": binary,
        "signed_bin": signed_bin,
        "disassembly": disassembly,
        "mapfile": mapfile,
    }
    output = exec_env.kind_transform[ctx.attr.kind][TransformInfo].transform(
        ctx,
        exec_env,
        name,
        inputs,
    )
    if exec_env.transform_hook:
        output = exec_env.transform_hook[TransformInfo].transform(
            ctx,
            exec_env,
            name,
            output,
        )
    return output

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
    flags = cc_common.get_memory_inefficient_command_line(
        feature_configuration = feature_config,
        action_name = OT_ACTION_OBJDUMP,
        variables = cc_common.empty_variables(),
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
        command = "$1 {} $2 | expand > $3".format(" ".join(flags)),
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
        slot: Which physical slot ("a" or "b") the output will be loaded into, required because
        RRAM's address-infection and scrambling depend on the absolute RRAM address.

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
    if slot not in ("a", "b"):
        fail("RRAM images can only be scrambled for physical slot 'a' or 'b', but asked for:", slot)

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

def scramble_nvm(ctx, kind, word_size, **kwargs):
    """Scramble a VMEM file for loading into some non-volatile memory (flash or RRAM).

    This dispatches to the relevant `scramble_flash` or `scramble_rram` helper. RRAM scrambling
    is dependent on the absolute address, and so in that case we always build an image for
    both physical slots, where tooling can then decide which image to load.

    Outputs:
      - flash: <name>.<word_size>.scr.vmem
      - rram: <name>.slot_a.<word_size>.scr.vmem
          and <name>.slot_b.<word_size>.scr.vmem

    Args:
      ctx: The context object for this rule.
      kind: The kind of the binary ("flash" or "rram").
      word_size: The word size of the VMEM.
      kwargs: Overrides passed through to `scramble_flash` or `scramble_rram`.

    Returns:
      (File, File): The scrambled image for flash or RRAM slot A, and then the scrambled image
      for RRAM slot B, or `None` for flash.
    """
    for arg in ("output", "suffix", "slot"):
        if arg in kwargs:
            fail("Overriding '{}' is not allowed since this is implemented by `scramble_nvm`".format(arg))

    if kind == "flash":
        vmem = scramble_flash(ctx, suffix = "{}.scr.vmem".format(word_size), **kwargs)
        return vmem, None

    if kind == "rram":
        vmem_slot_a = scramble_rram(
            ctx,
            suffix = "slot_a.{}.scr.vmem".format(word_size),
            slot = "a",
            **kwargs
        )
        vmem_slot_b = scramble_rram(
            ctx,
            suffix = "slot_b.{}.scr.vmem".format(word_size),
            slot = "b",
            **kwargs
        )
        return vmem_slot_a, vmem_slot_b

    fail("Unknown kind '{}' for NVM images".format(kind))

def rram_otp_image(ctx, exec_env, otp_attr):
    """Reformats an exec_env's `otp` attribute into the RRAM-native layout that backdoor-loading
    OTP into the RRAM data array expects.
    OTP lives in the tail pages of the RRAM data array now, see rram_ctrl_pkg.sv.
    There is no standalone OTP array to backdoor-load into any more.

    If `otp_attr` is an otp_image() target, it already carries this reformatted output in its
    `rram_otp` output group (see rules/otp.bzl).
    Reuse that instead of reformatting again.
    This keeps it to a single gen-rram-img.py invocation per otp_image() target rather than one
    per consumer, and backdoor loading uses the exact same OTP content the rest of this exec_env
    is configured for (e.g. for scrambling-key derivation).
    Falls back to reformatting `otp_attr` itself only if it isn't an otp_image() output (e.g. some
    other override).

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
      [File, File]: The logs and rodata text databases.
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
    return [output_logs, output_rodata]

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

# Transform function wrapping.
def merge_outputs(*inputs):
    """
    Merge the inputs/outputs from several transforms. If the same key exists in two
    or more dictionaries, their contents will be merged and de-duplicated. This function
    preserves files/list of files, i.e. if a entry is a file, it will not become a list unless
    it needs to be merged with other distinct files.
    """
    outs = {}
    for dict in inputs:
        for (key, val) in dict.items():
            cur_set = outs.setdefault(key, set())

            # If the value is just a list, add all the elements.
            if type(val) != "list":
                val = [val]
            for v in val:
                cur_set.add(v)
    return {
        key: val.pop() if len(val) == 1 else list(val)
        for (key, val) in outs.items()
    }

def _transform_extract_logs(rule_ctx):
    # We can't access rule_ctx once we exit this function, we need to reference its
    # attribute so that we can capture them in a closure.
    input = rule_ctx.attr.input
    outputs = rule_ctx.attr.outputs
    extract_sw_logs = rule_ctx.attr.extract_sw_logs

    def transform(ctx, exec_env, name, inputs):
        if input not in inputs:
            fail("The transform has not input '{}'".format(input))
        logs = extract_software_logs(
            ctx,
            name = name,
            src = inputs[input],
            _tool = extract_sw_logs[DefaultInfo].files_to_run,
        )
        return merge_outputs(inputs, {out: logs for out in outputs})

    return [TransformInfo(transform = transform)]

transform_extract_logs = rule(
    doc = """
        Transform function which extracts the software logs.
        This transform processes input file specified by `input` and puts the logs file in the `outputs`.
""",
    implementation = _transform_extract_logs,
    attrs = {
        "input": attr.string(
            doc = "Name of the input file to convert (in the `inputs` argument). By default, convert the `elf` input.",
            default = "elf",
        ),
        "outputs": attr.string_list(
            doc = "List of outputs name to which the logs are added. By default, add to `logs`.",
            default = ["logs"],
        ),
        "extract_sw_logs": attr.label(
            doc = "Tool used to extract the software logs. By default uses the standard tool.",
            default = "//util/device_sw_utils:extract_sw_logs_db",
            executable = True,
            cfg = "exec",
        ),
    },
)

def _transform_to_vmem(rule_ctx):
    # We can't access rule_ctx once we exit this function, we need to reference its
    # attribute so that we can capture them in a closure.
    input = rule_ctx.attr.input
    outputs = rule_ctx.attr.outputs
    word_size = rule_ctx.attr.word_size
    fill = rule_ctx.attr.fill

    def transform(ctx, exec_env, name, inputs):
        if input not in inputs:
            fail("The transform has not input '{}'".format(input))
        vmem = convert_to_vmem(
            ctx,
            name = name,
            src = inputs[input],
            word_size = word_size,
            fill = fill,
        )
        return merge_outputs(inputs, {out: vmem for out in outputs})

    return [TransformInfo(transform = transform)]

transform_to_vmem = rule(
    doc = """
        Transform function which converts a binary into a VMEM file.
        This transform the input file specified by `input` and puts the VMEM file in the `outputs`.
""",
    implementation = _transform_to_vmem,
    attrs = {
        "input": attr.string(
            doc = "Name of the input file to convert (in the `inputs` argument). By default, convert the `binary` input.",
            default = "binary",
        ),
        "outputs": attr.string_list(
            doc = "List of outputs name to which the VMEM is added. By default, add to `default` and `vmem`.",
            default = ["default", "vmem"],
        ),
        "word_size": attr.int(
            doc = "Word size",
            mandatory = True,
        ),
        "fill": attr.string(
            doc = "byte value used to pad to word alignment",
            default = "0xff",
        ),
    },
)

def _transform_to_scrambled_rom_vmem(rule_ctx):
    # We can't access rule_ctx once we exit this function, we need to reference its
    # attribute so that we can capture them in a closure.
    input = rule_ctx.attr.input
    outputs = rule_ctx.attr.outputs
    suffix = rule_ctx.attr.suffix
    rom_scramble_tool = rule_ctx.executable.rom_scramble_tool
    rom_scramble_mode = rule_ctx.attr.rom_scramble_mode
    outputs = rule_ctx.attr.outputs

    def transform(ctx, exec_env, name, inputs):
        if input not in inputs:
            fail("The transform has not input '{}'".format(input))
        (rom_vmem, hashfile) = convert_to_scrambled_rom_vmem(
            ctx,
            name = name,
            src = inputs[input],
            suffix = suffix,
            rom_scramble_tool = rom_scramble_tool,
            rom_scramble_mode = rom_scramble_mode,
            top_gen_hjson = exec_env.top_gen_hjson,
            top_secret_cfg = exec_env.top_secret_cfg,
        )
        return merge_outputs(inputs, {
            "hashfile": hashfile,
        } | {out: rom_vmem for out in outputs})

    return [TransformInfo(transform = transform)]

transform_to_scrambled_rom_vmem = rule(
    doc = """
        Transform function which converts a binary into a VMEM file scrambled for the ROM.
        This transform uses the top hjson and top secret configuration file from the execution environment.
        This transform the input file specified by `input` and puts the VMEM file in the `outputs`.
        In addition, the created C hashfile will be put in the `hashfile` output.
""",
    implementation = _transform_to_scrambled_rom_vmem,
    attrs = {
        "rom_scramble_tool": attr.label(
            doc = "ROM scrambling tool. By default uses the standard rom_ctrl tool.",
            default = "//hw/ip/rom_ctrl/util:scramble_image",
            executable = True,
            cfg = "exec",
        ),
        "rom_scramble_mode": attr.string(
            doc = "ROM scrambling mode. By default, scramble for the base ROM.",
            default = "base-rom",
        ),
        "suffix": attr.string(
            doc = "Suffix of the VMEM file",
            default = "39.scr.vmem",
        ),
        "input": attr.string(
            doc = "Name of the input file to scramble (in the `inputs` argument). By default, scramble the `elf` input.",
            default = "elf",
        ),
        "outputs": attr.string_list(
            doc = "List of outputs name to which the VMEM is added. By default, add to `default` and `vmem`.",
            default = ["default", "vmem"],
        ),
    },
)

def _transform_copy(rule_ctx):
    input = rule_ctx.attr.input
    outputs = rule_ctx.attr.outputs

    def transform(ctx, exec_env, name, inputs):
        if input not in inputs:
            fail("The transform has not input '{}'".format(input))
        return merge_outputs(inputs, {out: inputs[input] for out in outputs})

    return [TransformInfo(transform = transform)]

transform_copy = rule(
    doc = """
        Copy one of the input file directly to the output, without transformation.
""",
    implementation = _transform_copy,
    attrs = {
        "input": attr.string(
            doc = "Name of the input file to copy.",
            mandatory = True,
        ),
        "outputs": attr.string_list(
            doc = "List of outputs name to which the inpuy is added.",
            mandatory = True,
        ),
    },
)

def _transform_merge(rule_ctx):
    transforms = rule_ctx.attr.transforms

    def transform(ctx, exec_env, name, inputs):
        output = {}
        for xform in transforms:
            output = merge_outputs(output, xform[TransformInfo].transform(
                ctx,
                exec_env,
                name,
                inputs,
            ))
        return output

    return [TransformInfo(transform = transform)]

transform_merge = rule(
    doc = """
        Apply several transform functions and merge their output. See merge_outputs
        for details on how merging is performed.
""",
    implementation = _transform_merge,
    attrs = {
        "transforms": attr.label_list(
            doc = "List of transforms to apply and merge, order is important.",
            mandatory = True,
            providers = [TransformInfo],
        ),
    },
)
