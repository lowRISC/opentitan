# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "@lowrisc_opentitan//rules/opentitan:transform.bzl",
    "convert_to_vmem",
    "obj_disassemble",
    "obj_transform",
)
load("@rules_cc//cc:action_names.bzl", "CPP_LINK_STATIC_LIBRARY_ACTION_NAME", "OBJ_COPY_ACTION_NAME")
load("@lowrisc_opentitan//rules:signing.bzl", "sign_binary")
load("@lowrisc_opentitan//rules/opentitan:exec_env.bzl", "ExecEnvInfo")
load("@lowrisc_opentitan//rules/opentitan:util.bzl", "get_fallback", "get_override")
load("@lowrisc_opentitan//rules:rv.bzl", "rv_rule")
load("@rules_cc//cc:find_cc_toolchain.bzl", "find_cc_toolchain")
load("//rules/coverage:info.bzl", "create_cc_instrumented_files_info")
load("//rules/opentitan:toolchain.bzl", "LOCALTOOLS_TOOLCHAIN")
load("//rules/opentitan:util.bzl", "assemble_for_test", "recursive_format")

def _expand(ctx, name, items):
    """Perform location and make_variable expansion on a list of items.

    Args:
      ctx: The rule context.
      name: The attribute name (used in error reporting).
      items: A list of strings on which to perform expansions.
    Returns:
      List[str]: The expanded string list.
    """
    return [ctx.expand_make_variables(name, ctx.expand_location(item), {}) for item in items]

def ot_binary(ctx, **kwargs):
    """Compile to a binary executable.

    Args:
      ctx: The rule context.
      kwargs: Overrides of values normally retrived from the context object.
        features: List of features to be enabled.
        disabled_features: List of disabled/unsupported features.
        name: Name of the output binary.
        srcs: Sources to compile this binary.
        copts: Compiler options.
        defines: Define values to pass to the compiler.
        local_defines: Define values to pass to the compiler.
        includes: Include directories to pass to the compiler.
        deps: Dependencies for this binary.
        linker_script: Linker script for this binary.
        linkopts: Extra linker options for this binary.
    Returns:
      (elf_file, map_file) File objects.
    """
    cc_toolchain = find_cc_toolchain(ctx)
    features = cc_common.configure_features(
        ctx = ctx,
        cc_toolchain = cc_toolchain,
        requested_features = get_override(ctx, "features", kwargs),
        unsupported_features = get_override(ctx, "disabled_features", kwargs),
    )

    compilation_contexts = [
        dep[CcInfo].compilation_context
        for dep in get_override(ctx, "attr.deps", kwargs)
    ]
    linker_script = get_override(ctx, "attr.linker_script", kwargs)
    if linker_script:
        compilation_contexts.append(linker_script[CcInfo].compilation_context)

    name = get_override(ctx, "attr.name", kwargs)
    all_srcs = get_override(ctx, "files.srcs", kwargs)

    # cc_common.compile crashes if a header file is passed to srcs, so filter
    # those out and passed them as private headers instead
    hdrs = [s for s in all_srcs if s.extension == "h"]
    srcs = [s for s in all_srcs if s.extension != "h"]
    cctx, cout = cc_common.compile(
        name = name,
        actions = ctx.actions,
        feature_configuration = features,
        cc_toolchain = cc_toolchain,
        compilation_contexts = compilation_contexts,
        srcs = srcs,
        private_hdrs = hdrs,
        user_compile_flags = ["-ffreestanding"] + _expand(ctx, "copts", get_override(ctx, "attr.copts", kwargs)),
        defines = _expand(ctx, "defines", get_override(ctx, "attr.defines", kwargs)),
        local_defines = _expand(ctx, "local_defines", get_override(ctx, "attr.local_defines", kwargs)),
        quote_includes = _expand(ctx, "includes", get_override(ctx, "attr.includes", kwargs)),
    )

    linking_contexts = [
        dep[CcInfo].linking_context
        for dep in get_override(ctx, "attr.deps", kwargs)
    ]
    if linker_script:
        linking_contexts.append(linker_script[CcInfo].linking_context)
    mapfile = kwargs.get("mapfile", "{}.map".format(name))
    mapfile = ctx.actions.declare_file(mapfile)

    extra_linkopts = (ctx.attr.linkopts or []) + kwargs.get("linkopts", [])

    linkopts = [
        "-Wl,-Map={}".format(mapfile.path),
        "-nostdlib",
    ] + _expand(ctx, "linkopts", extra_linkopts)

    if ctx.var.get("ot_coverage_enabled", "false") == "true":
        linkopts.append("-Wl,--defsym=_ot_coverage_enabled=1")

    lout = cc_common.link(
        name = name + ".elf",
        actions = ctx.actions,
        feature_configuration = features,
        cc_toolchain = cc_toolchain,
        compilation_outputs = cout,
        linking_contexts = linking_contexts,
        user_link_flags = linkopts,
        additional_outputs = [mapfile],
    )

    return lout.executable, mapfile

def _as_group_info(name, items):
    """Prepare a dict of files for OutputGroupInfo.

    This renames all of the items to have `name` as a prefix and
    transforms the values into a depset.

    Args:
      name: A prefix for each dictionary key.
      items: A dict str:File to prepare.
    Returns:
      dict
    """
    groups = {}
    for k, v in items.items():
        if not v:
            continue
        elif type(v) == "list":
            # Depset wants a list; nothing to do.
            pass
        elif type(v) == "tuple":
            v = list(v)
        else:
            v = [v]
        groups["{}_{}".format(name, k)] = depset(v)
    return groups

def _binary_name(ctx, exec_env):
    """Create a binary name according to a naming convention.

    Args:
      ctx: The rule context.
      exec_env: An ExecEnvInfo provider.
    Returns:
      str: The name.
    """
    return ctx.attr.naming_convention.format(
        name = ctx.attr.name,
        exec_env = exec_env.exec_env,
    )

def _build_binary(ctx, exec_env, name, deps, kind):
    """Build a binary, sign and perform output file transformations.

    This function is the core of the `opentitan_binary` and `opentitan_test`
    implementations.

    Args:
      ctx: The rule context.
      exec_env: An ExecEnvInfo provider.
      name: The name of the output artifacts.
      deps: Dependencies for this binary.
      kind: Kind of binary.
    Returns:
      (dict, dict): A dict of output artifacts and a dict of signing artifacts.
    """
    linker_script = get_fallback(ctx, "attr.linker_script", exec_env)

    slot_spec = dict(exec_env.slot_spec)
    slot_spec.update(ctx.attr.slot_spec)

    linkopts = ["-Wl,--defsym=_{}={}".format(key, value) for key, value in slot_spec.items()]

    elf, mapfile = ot_binary(
        ctx,
        name = name,
        deps = deps,
        linker_script = linker_script,
        linkopts = linkopts,
    )
    binary = obj_transform(
        ctx,
        name = name,
        strip_llvm_prf_cnts = True,
        suffix = "bin",
        format = "binary",
        src = elf,
    )

    manifest = get_fallback(ctx, "file.manifest", exec_env)
    if manifest and str(manifest.owner).endswith("@//hw/top_earlgrey:none_manifest"):
        manifest = None

    ecdsa_key = get_fallback(ctx, "attr.ecdsa_key", exec_env)
    rsa_key = get_fallback(ctx, "attr.rsa_key", exec_env)
    spx_key = get_fallback(ctx, "attr.spx_key", exec_env)
    if (manifest or rsa_key) and kind != "ram":
        if not (manifest and (rsa_key or ecdsa_key)):
            fail("Signing requires a manifest and an rsa_key or ecdsa_key, and optionally an spx_key")
        signed = sign_binary(
            ctx,
            opentitantool = exec_env._opentitantool,
            bin = binary,
            ecdsa_key = ecdsa_key,
            rsa_key = rsa_key,
            spx_key = spx_key,
            manifest = manifest,
            # FIXME: will need to supply hsmtool when we add NitroKey signing.
        )
    else:
        signed = {}

    disassembly = obj_disassemble(
        ctx,
        name = name,
        src = elf,
    )

    provides = exec_env.transform(
        ctx,
        exec_env,
        name = name,
        elf = elf,
        binary = binary,
        signed_bin = signed.get("signed"),
        disassembly = disassembly,
        mapfile = mapfile,
    )
    return provides, signed

def _opentitan_binary_blob(ctx):
    """
    Creates a position-independent relocatable static library.

    This rule combines RISC-V linker relaxation with a Python-driven symbol extraction
    pipeline to seal the FIPS boundary and preserve hardware crypto (.otbn) sections.

    The following steps are performed to create the final library:
    1. Generate a linker script to pack the required functions and configure GC roots.
    2. Partial link (ld -r) dependencies into a single relocatable.o. Linker relaxation
       is intentionally permitted to maximize code size compression.
    3. Perform a dry-run link into an .elf to finalize PC-relative math and relaxations.
    4. Extract the raw binary from the .elf, hollow out the trailing 48 bytes,
       compute the SHA-384 hash, and fuse it back onto the blob.
    5. Extract the relaxed memory offsets of the public API functions from the .elf
       using a Python script.
    6. Repair the original relocatable.o file using objcopy:
       - Overwrite the original code section with the hashed binary (--update-section)
         to safely preserve adjacent hardware .otbn sections.
       - Localize internal dependencies (e.g., memcpy) to seal the FIPS boundary
         and prevent downstream linker clashes (--keep-global-symbol).
       - Inject the new, relaxed public function offsets as global ELF symbols.
    7. Archive the final, repaired object file into a static library (.a).
    """
    name_relocatable_o = ctx.attr.name + "_relocatable.o"
    name_elf = ctx.attr.name + ".elf"
    name_bin = ctx.attr.name + ".bin"
    name_sha = ctx.attr.name + ".sha384"
    name_bin_sha = ctx.attr.name + "_sha384.bin"
    name_sym_args = ctx.attr.name + "_sym_args.txt"
    name_blob_o = ctx.attr.name + "_blob.o"
    name_library = ctx.attr.name + ".a"

    deps_blob = ctx.attr.deps_blob
    cc_toolchain = find_cc_toolchain(ctx)

    features = cc_common.configure_features(
        ctx = ctx,
        cc_toolchain = cc_toolchain,
        requested_features = ctx.features,
        unsupported_features = ctx.disabled_features,
    )

    ar_tool = cc_common.get_tool_for_action(
        feature_configuration = features,
        action_name = CPP_LINK_STATIC_LIBRARY_ACTION_NAME,
    )
    objcopy_tool = cc_common.get_tool_for_action(
        feature_configuration = features,
        action_name = OBJ_COPY_ACTION_NAME,
    )

    # Generate partial linker script
    #
    # If `.text.libotcrypto` and `.srodata` are left as separate, floating sections,
    # the application linker has the freedom to insert external data between them.
    # If the physical distance between the code and the data increases, the linker will silently
    # rewrite the `auipc` instruction bytes to point to the new, longer distance which corrupts the FIPS hash.
    #
    # We deal with this by forcing `*(.text*)`, `*(.rodata*)`, and `*(.srodata*)` into a single,
    # contiguous section.
    template_file = ctx.file._linker_script_template
    linker_script = ctx.actions.declare_file(ctx.attr.name + "_linker_script.ld")

    # Generate garbage collection roots
    if len(ctx.files.config) == 1:
        ctx.actions.run_shell(
            inputs = [template_file, ctx.files.config[0]],
            outputs = [linker_script],
            # Tell the linker not to remove the functions present in the config file by claiming each function as undefined (-u).
            command = "cat {template} > {out} && awk 'NF {{print \"EXTERN(\" $1 \")\"}}' < {config} >> {out}".format(
                template = template_file.path,
                config = ctx.files.config[0].path,
                out = linker_script.path,
            ),
        )
    else:
        ctx.actions.run_shell(
            inputs = [template_file],
            outputs = [linker_script],
            command = "cp {template} {out}".format(
                template = template_file.path,
                out = linker_script.path,
            ),
        )

    # Partial link (ld -r)
    linking_contexts = [dep[CcInfo].linking_context for dep in deps_blob]
    linking_input = cc_common.create_linker_input(
        owner = ctx.label,
        additional_inputs = depset([linker_script]),
    )
    linking_contexts.append(cc_common.create_linking_context(
        linker_inputs = depset([linking_input]),
    ))

    linkopts = [
        "-nostdlib",
        "-Wl,-r",
        "-Wl,-T,{}".format(linker_script.path),
        "-Wl,-u,_libotcrypto_start_",
    ] + _expand(ctx, "linkopts", ctx.attr.linkopts or [])

    if len(ctx.files.config) == 1:
        linkopts.append("-Wl,--gc-sections")
    else:
        linkopts.extend(["-Wl,--whole-archive", "-Wl,--no-gc-sections"])

    partial_linking_outputs = cc_common.link(
        name = name_relocatable_o,
        actions = ctx.actions,
        output_type = "executable",
        feature_configuration = features,
        cc_toolchain = cc_toolchain,
        linking_contexts = linking_contexts,
        user_link_flags = linkopts,
    )
    relocatable_o = partial_linking_outputs.executable

    # Dry run link (.o -> .elf) using the static script for exact memory layout
    elf_file = ctx.actions.declare_file(name_elf)
    elf_linker_input = cc_common.create_linker_input(
        owner = ctx.label,
        additional_inputs = depset([relocatable_o, template_file]),
    )

    elf_linkopts = [
        "-static",
        "-nostdlib",
        relocatable_o.path,
        "-Wl,--defsym=_rom_origin={}".format(ctx.attr.rom_origin),
        "-Wl,-T,{}".format(template_file.path),
        "-Wl,--no-gc-sections",
    ]

    elf_linking_outputs = cc_common.link(
        name = name_elf,
        actions = ctx.actions,
        output_type = "executable",
        feature_configuration = features,
        cc_toolchain = cc_toolchain,
        linking_contexts = [cc_common.create_linking_context(linker_inputs = depset([elf_linker_input]))],
        user_link_flags = elf_linkopts,
    )
    elf_file = elf_linking_outputs.executable

    # Extract binary (.elf -> .bin), hash it, and fuse them together
    binary_file = ctx.actions.declare_file(name_bin)
    ctx.actions.run(
        outputs = [binary_file],
        inputs = [elf_file],
        executable = objcopy_tool,
        arguments = ["-O", "binary", "--only-section=.text.libotcrypto", elf_file.path, binary_file.path],
        use_default_shell_env = True,
        tools = cc_toolchain.all_files,
    )

    # Compute Hash (.bin -> .sha384)
    hash_file = ctx.actions.declare_file(name_sha)
    ctx.actions.run_shell(
        inputs = [binary_file],
        outputs = [hash_file],
        command = "head -c -48 {} | sha384sum | awk '{{print $1}}' | xxd -r -p > {}".format(binary_file.path, hash_file.path),
    )

    binary_hash_file = ctx.actions.declare_file(name_bin_sha)
    ctx.actions.run_shell(
        inputs = [binary_file, hash_file],
        outputs = [binary_hash_file],
        command = "head -c -48 {} > {} && cat {} >> {}".format(binary_file.path, binary_hash_file.path, hash_file.path, binary_hash_file.path),
    )

    # Extract symbols using python script
    sym_args_file = ctx.actions.declare_file(name_sym_args)
    extract_args = [
        "--nm",
        ctx.executable._riscv32_nm.path,
        "--elf",
        elf_file.path,
        "--out",
        sym_args_file.path,
    ]
    if len(ctx.files.config) == 1:
        extract_args.append("--config=" + ctx.files.config[0].path)

    ctx.actions.run(
        outputs = [sym_args_file],
        inputs = [elf_file] + ctx.files.config,
        tools = [ctx.executable._riscv32_nm],
        executable = ctx.executable._extract_symbols,
        arguments = extract_args,
    )

    # Inject binary & symbols via objcopy
    blob_o_file = ctx.actions.declare_file(name_blob_o)

    # Build the objcopy command. We use --update-section to preserve hardware .otbn sections.
    # --keep-global-symbol localizes internal dependencies (memcpy, status_create) sealing the boundary.
    cmd_str = "{objcopy} --keep-global-symbol=_libotcrypto_start_ --strip-debug --discard-all --remove-section=.rela.text.libotcrypto --remove-section=.rela.text --update-section .text.libotcrypto={fused_bin}"
    if len(ctx.files.config) == 1:
        cmd_str += " @" + sym_args_file.path
    cmd_str += " {reloc_o} {final_o}"

    ctx.actions.run_shell(
        outputs = [blob_o_file],
        inputs = [relocatable_o, binary_hash_file, sym_args_file],
        command = cmd_str.format(
            objcopy = objcopy_tool,
            fused_bin = binary_hash_file.path,
            reloc_o = relocatable_o.path,
            final_o = blob_o_file.path,
        ),
        use_default_shell_env = True,
        tools = cc_toolchain.all_files,
    )

    # Create a library from it
    library_file = ctx.actions.declare_file(name_library)
    ctx.actions.run(
        inputs = [blob_o_file],
        outputs = [library_file],
        executable = ar_tool,
        arguments = ["rcs", library_file.path, blob_o_file.path],
        tools = cc_toolchain.all_files,
    )

    dis_file = obj_disassemble(ctx, name = ctx.attr.name, src = elf_file)

    return [
        DefaultInfo(files = depset([library_file, dis_file, elf_file])),
        OutputGroupInfo(
            elf_file = depset([elf_file]),
            dis_file = depset([dis_file]),
            linker_script = depset([linker_script, template_file]),
            sym_args = depset([sym_args_file]),
        ),
        CcInfo(
            linking_context = cc_common.create_linking_context(
                linker_inputs = depset([cc_common.create_linker_input(
                    owner = ctx.label,
                    libraries = depset([cc_common.create_library_to_link(
                        actions = ctx.actions,
                        feature_configuration = features,
                        cc_toolchain = cc_toolchain,
                        static_library = library_file,
                        alwayslink = True,
                    )]),
                )]),
            ),
        ),
    ]

def _opentitan_binary(ctx):
    providers = []
    default_info = []
    groups = {}
    runfiles = ctx.runfiles()
    for exec_env_target in ctx.attr.exec_env:
        exec_env = exec_env_target[ExecEnvInfo]
        name = _binary_name(ctx, exec_env)
        deps = ctx.attr.deps + exec_env.libs
        for dep in deps:
            runfiles = runfiles.merge(dep[DefaultInfo].default_runfiles)

        kind = ctx.attr.kind
        provides, signed = _build_binary(ctx, exec_env, name, deps, kind)
        providers.append(exec_env.provider(kind = kind, **provides))
        default_info.append(provides["default"])
        default_info.append(provides["elf"])
        default_info.append(provides["disassembly"])

        # FIXME(cfrantz): logs are a special case and get added into
        # the DefaultInfo provider.
        if "logs" in provides:
            default_info.extend(provides["logs"])

        # FIXME: vmem is a special case for ram targets used in ROM e2e test
        # cases.
        if provides.get("vmem"):
            default_info.append(provides["vmem"])

        # FIXME(cfrantz): Special case: The englishbreakfast verilator model
        # requires a non-scrambled ROM image.
        if provides.get("rom32"):
            default_info.append(provides["rom32"])

        groups.update(_as_group_info(exec_env.exec_env, signed))
        groups.update(_as_group_info(exec_env.exec_env, provides))

    providers.append(DefaultInfo(files = depset(default_info), runfiles = runfiles))
    providers.append(OutputGroupInfo(**groups))
    providers.append(create_cc_instrumented_files_info(
        ctx = ctx,
        metadata_files = [],
    ))
    return providers

common_binary_attrs = {
    "srcs": attr.label_list(
        allow_files = True,
        doc = "The list of C and C++ files that are processed to create the target.",
    ),
    "deps": attr.label_list(
        providers = [CcInfo],
        doc = "The list of other libraries to be linked in to the binary target.",
    ),
    "linker_script": attr.label(
        providers = [CcInfo],
        doc = "Linker script for linking this binary",
    ),
    "ecdsa_key": attr.label_keyed_string_dict(
        allow_files = True,
        doc = "ECDSA key to sign images",
    ),
    "rsa_key": attr.label_keyed_string_dict(
        allow_files = True,
        doc = "RSA key to sign images",
    ),
    "spx_key": attr.label_keyed_string_dict(
        allow_files = True,
        doc = "SPX key to sign images",
    ),
    "manifest": attr.label(
        allow_single_file = True,
        doc = "Manifest used when signing images",
    ),
    "copts": attr.string_list(
        doc = "Add these options to the C++ compilation command.",
    ),
    "defines": attr.string_list(
        doc = "List of defines to add to the compile line.",
    ),
    "local_defines": attr.string_list(
        doc = "List of defines to add to the compile line.",
    ),
    "includes": attr.string_list(
        doc = "List of include dirs to be added to the compile line.",
    ),
    "linkopts": attr.string_list(
        doc = "Add these flags to the C++ linker command.",
    ),
    "naming_convention": attr.string(
        doc = "Naming convention for binary artifacts.",
        default = "{name}_{exec_env}",
    ),
    "kind": attr.string(
        doc = "Binary kind: flash, ram or rom",
        default = "flash",
        values = ["flash", "ram", "rom"],
    ),
    # FIXME(cfrantz): This should come from the ExecEnvInfo provider, but
    # I was unable to make that work.  See the comment in `exec_env.bzl`.
    "extract_sw_logs": attr.label(
        doc = "Software logs extraction script.",
        default = "//util/device_sw_utils:extract_sw_logs_db",
        executable = True,
        cfg = "exec",
    ),
    "rom_scramble_tool": attr.label(
        doc = "ROM scrambling tool.",
        default = "//hw/ip/rom_ctrl/util:scramble_image",
        executable = True,
        cfg = "exec",
    ),
    "slot_spec": attr.string_dict(
        default = {},
        doc = "Firmware slot spec to use in this environment",
    ),
    "_check_initial_coverage": attr.label(
        doc = "Tool to check the coverage counter initialization.",
        default = "//util/coverage:check_initial_coverage",
        executable = True,
        cfg = "exec",
    ),
}

def _transitive_feature_transition_impl(settings, attr):
    features = settings["//command_line_option:features"] + attr.transitive_features
    return {
        "//command_line_option:features": features,
    }

_transitive_feature_transition = transition(
    implementation = _transitive_feature_transition_impl,
    inputs = [
        "//command_line_option:features",
    ],
    outputs = [
        "//command_line_option:features",
    ],
)

opentitan_binary_blob = rv_rule(
    implementation = _opentitan_binary_blob,
    attrs = dict(common_binary_attrs.items() + {
        "rom_origin": attr.string(
            default = "0",
            doc = "Base address for the dry-run link.",
        ),
        "hdrs": attr.label_list(
            allow_files = True,
            doc = "The list of header file requires for the creation of the library.",
        ),
        "config": attr.label(
            default = None,
            allow_single_file = True,
            doc = "File containing the functions to be included into the blob",
        ),
        "deps_blob": attr.label_list(
            providers = [CcInfo],
            cfg = _transitive_feature_transition,
            doc = "The list of other libraries to be for the creation of the binary blob.",
        ),
        "transitive_features": attr.string_list(
            default = [],
            doc = "Features to apply transitively to all dependencies.",
        ),
        "_linker_script_template": attr.label(
            default = Label("//sw/device/lib/crypto/configs:otcrypto_blob.ld"),
            allow_single_file = True,
            doc = "Base linker script template used for appending EXTERN anchors.",
        ),
        "_riscv32_nm": attr.label(
            default = Label("@lowrisc_rv32imcb_toolchain//:bin/riscv32-unknown-elf-nm"),
            allow_single_file = True,
            executable = True,
            cfg = "exec",
        ),
        "_cc_toolchain": attr.label(default = Label("@bazel_tools//tools/cpp:current_cc_toolchain")),
        "_extract_symbols": attr.label(
            default = "//sw/device/lib/crypto/configs:extract_symbols",
            executable = True,
            cfg = "exec",
        ),
    }.items()),
    fragments = ["cpp"],
    toolchains = ["@rules_cc//cc:toolchain_type"],
)

opentitan_binary = rv_rule(
    implementation = _opentitan_binary,
    attrs = dict(common_binary_attrs.items() + {
        "exec_env": attr.label_list(
            providers = [ExecEnvInfo],
            doc = "List of execution environments for this target.",
        ),
        "_cc_toolchain": attr.label(default = Label("@bazel_tools//tools/cpp:current_cc_toolchain")),
    }.items()),
    fragments = ["cpp"],
    toolchains = ["@rules_cc//cc:toolchain_type"],
)

def _testing_bitstream_impl(settings, attr):
    rom = attr.rom if attr.rom else "//hw/bitstream/universal:none"
    otp = attr.otp if attr.otp else "//hw/bitstream/universal:none"
    return {
        "//hw/bitstream/universal:rom": rom,
        "//hw/bitstream/universal:otp": otp,
        "//hw/bitstream/universal:env": attr.exec_env,
    }

_testing_bitstream = transition(
    implementation = _testing_bitstream_impl,
    inputs = [],
    outputs = [
        "//hw/bitstream/universal:rom",
        "//hw/bitstream/universal:otp",
        "//hw/bitstream/universal:env",
    ],
)

def _opentitan_test(ctx):
    exec_env = ctx.attr.exec_env[ExecEnvInfo]

    if ctx.attr.srcs or ctx.attr.deps:
        name = _binary_name(ctx, exec_env)
        deps = ctx.attr.deps + exec_env.libs
        kind = ctx.attr.kind
        provides, signed = _build_binary(ctx, exec_env, name, deps, kind)
        p = exec_env.provider(**provides)
    else:
        p = None

    executable, runfiles = exec_env.test_dispatch(ctx, exec_env, p)
    if ctx.attr.test_harness != None:
        harness_runfiles = ctx.attr.test_harness[DefaultInfo].default_runfiles
    else:
        harness_runfiles = ctx.runfiles()

    if ctx.var.get("ot_coverage_enabled", "false") == "true":
        coverage_runfiles = ctx.attr._collect_cc_coverage[DefaultInfo].default_runfiles
    else:
        coverage_runfiles = ctx.runfiles()

    return DefaultInfo(
        executable = executable,
        runfiles = ctx.runfiles(files = runfiles).merge_all([harness_runfiles, coverage_runfiles]),
    )

opentitan_test = rv_rule(
    implementation = _opentitan_test,
    attrs = dict(common_binary_attrs.items() + {
        "exec_env": attr.label(
            providers = [ExecEnvInfo],
            doc = "List of exeuction environments for this target.",
        ),
        "test_harness": attr.label(
            executable = True,
            cfg = "exec",
            allow_files = True,
        ),
        "binaries": attr.label_keyed_string_dict(
            allow_files = True,
            doc = "Opentitan binaries to use with this test (keys are labels, values are the string to use as a subsitution parameter in test_cmd)",
        ),
        "rom": attr.label(
            allow_files = True,
            doc = "ROM image override for this test",
        ),
        "rom_ext": attr.label(
            allow_files = True,
            doc = "ROM_EXT image override for this test",
        ),
        "otp": attr.label(
            allow_single_file = True,
            doc = "OTP image override for this test",
        ),
        "bitstream": attr.label(
            allow_single_file = True,
            cfg = _testing_bitstream,
            doc = "Bitstream override for this test",
        ),
        "post_test_harness": attr.label(
            executable = True,
            cfg = "exec",
            doc = "Executable to run after the test (e.g. cleanup, clear bitstream, ...)",
        ),
        "post_test_cmd": attr.string(
            doc = "Arguments to the post_test_harness",
        ),
        # Note: an `args` attr exists as an override for exec_env.args.  It is
        # not listed here because all test rules have an implicit `args`
        # attribute which is a list of strings subject to location and make
        # variable substitution.
        "test_cmd": attr.string(
            doc = "Test command override for this test",
        ),
        "param": attr.string_dict(
            doc = "Additional parameters for this test",
        ),
        "data": attr.label_list(
            doc = "Additonal dependencies for this test",
            allow_files = True,
            cfg = "exec",
        ),
        "needs_jtag": attr.bool(
            default = False,
            doc = "JTAG is required for this test",
        ),
        "openocd_adapter_config": attr.label(
            allow_single_file = True,
            doc = "OpenOCD adapter configuration override for this test",
        ),
        "_cc_toolchain": attr.label(default = Label("@bazel_tools//tools/cpp:current_cc_toolchain")),
        "_lcov_merger": attr.label(
            default = configuration_field(fragment = "coverage", name = "output_generator"),
            executable = True,
            cfg = "exec",
        ),
        "_collect_cc_coverage": attr.label(
            default = "//util/coverage/collect_cc_coverage",
            executable = True,
            cfg = "exec",
        ),
    }.items()),
    fragments = ["cpp"],
    toolchains = ["@rules_cc//cc:toolchain_type"],
    test = True,
)

def _opentitan_binary_assemble_impl(ctx):
    assembled_bins = []
    result = []
    tc = ctx.toolchains[LOCALTOOLS_TOOLCHAIN]
    for env in ctx.attr.exec_env:
        exec_env = env[ExecEnvInfo]
        exec_env_name = exec_env.exec_env
        exec_env_provider = exec_env.provider
        name = "{}_{}".format(ctx.attr.name, exec_env_name)
        spec = []
        input_bins = []
        for binary, offset in ctx.attr.bins.items():
            if binary[exec_env_provider].kind != "flash":
                fail("Only flash binaries can be assembled.")
            input_bins.append(binary[exec_env_provider].default)
            spec.append("{}@{}".format(binary[exec_env_provider].default.path, offset))

        action_param = {}
        action_param.update(exec_env.slot_spec)

        spec = " ".join(spec)
        spec = recursive_format(spec, action_param)
        spec = spec.split(" ")

        # Generate the multislot bin.
        bin = assemble_for_test(ctx, name, spec, input_bins, tc.tools.opentitantool)

        # Generate unscrambled VMEM files.
        #
        # Multi-slot binaries are currently only used for bootstrap operations,
        # i.e., non-backdoor loaded sim environments and FPGA/silicon
        # environments. Therefore we only need unscrambled VMEM files.
        vmem = convert_to_vmem(
            ctx,
            name = name,
            src = bin,
            word_size = 64,
        )
        result.append(exec_env_provider(default = bin, kind = "flash", vmem = vmem))
        assembled_bins.append(bin)
        assembled_bins.append(vmem)

    # Propagate runfiles
    runfiles = ctx.runfiles()
    for binary in ctx.attr.bins.keys():
        runfiles = runfiles.merge(binary[DefaultInfo].default_runfiles)
        if ctx.var.get("ot_coverage_enabled", "false") == "true":
            # Add elf files to runfiles for coverage
            runfiles = runfiles.merge(ctx.runfiles(binary.files.to_list()))

    return result + [DefaultInfo(files = depset(assembled_bins), runfiles = runfiles)]

opentitan_binary_assemble = rule(
    implementation = _opentitan_binary_assemble_impl,
    attrs = {
        "bins": attr.label_keyed_string_dict(
            allow_files = True,
            mandatory = True,
            doc = "Dictionary of binaries and the offsets they should be placed.",
        ),
        "exec_env": attr.label_list(
            providers = [ExecEnvInfo],
            doc = "List of execution environments for this target.",
        ),
    },
    toolchains = [LOCALTOOLS_TOOLCHAIN],
)

def _exec_env_filegroup(ctx):
    files = {v: k for k, v in ctx.attr.files.items()}
    exec_env = {v: k for k, v in ctx.attr.exec_env.items()}

    fset = {k: 1 for k in files.keys()}
    eset = {k: 1 for k in exec_env.keys()}

    if fset != eset:
        fail("The set of files and exec_envs must be matched: files =", fset.keys(), ", exec_env =", eset.keys())

    result = []
    default_files = []
    for k in files.keys():
        provider = exec_env[k][ExecEnvInfo].provider
        f = files[k].files.to_list()
        if len(f) != 1:
            fail("files[{}] must supply exactly one file".format(k))

        # Return the exec_env's provider so this rule can be consumed by
        # opentitan_test rules.
        result.append(provider(default = f[0], kind = ctx.attr.kind))
        default_files.append(f[0])

    # Also return a DefaultInfo provider so this rule can be consumed by other
    # filegroup or packaging rules.
    result.append(DefaultInfo(files = depset(default_files)))
    return result

exec_env_filegroup = rule(
    implementation = _exec_env_filegroup,
    attrs = {
        "files": attr.label_keyed_string_dict(
            allow_files = True,
            mandatory = True,
            doc = "Dictionary of files to exec_envs.",
        ),
        "exec_env": attr.label_keyed_string_dict(
            providers = [ExecEnvInfo],
            mandatory = True,
            doc = "Dictionary of execution environments for this target.",
        ),
        "kind": attr.string(default = "flash", doc = "The kind of binary"),
    },
)
