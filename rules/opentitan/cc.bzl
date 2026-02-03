# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "@lowrisc_opentitan//rules:rv.bzl",
    "rv_rule",
    _OPENTITAN_CPU = "OPENTITAN_CPU",
    _OPENTITAN_PLATFORM = "OPENTITAN_PLATFORM",
    _opentitan_transition = "opentitan_transition",
)
load(
    "@lowrisc_opentitan//rules/opentitan:transform.bzl",
    "convert_to_vmem",
    "obj_disassemble",
    "obj_transform",
)
load("@lowrisc_opentitan//rules:signing.bzl", "sign_binary")
load("@lowrisc_opentitan//rules/opentitan:exec_env.bzl", "ExecEnvInfo")
load("@lowrisc_opentitan//rules/opentitan:util.bzl", "get_fallback", "get_override")
load("@rules_cc//cc:find_cc_toolchain.bzl", "find_cc_toolchain")
load("@lowrisc_opentitan//rules/opentitan:toolchain.bzl", "LOCALTOOLS_TOOLCHAIN")
load("@lowrisc_opentitan//rules/opentitan:util.bzl", "assemble_for_test", "recursive_format")
load("@lowrisc_opentitan//rules/opentitan:providers.bzl", "OpenTitanBinaryInfo")

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
    transitive_features = [f for f in ctx.attr.transitive_features if not f.startswith("-")]
    transitive_disabled_features = [f.removeprefix("-") for f in ctx.attr.transitive_features if f.startswith("-")]
    features = cc_common.configure_features(
        ctx = ctx,
        cc_toolchain = cc_toolchain,
        requested_features = get_override(ctx, "features", kwargs) + transitive_features,
        unsupported_features = get_override(ctx, "disabled_features", kwargs) + transitive_disabled_features,
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
    if manifest and str(manifest.owner).endswith("@lowrisc_opentitan//hw/top_earlgrey:none_manifest"):
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

def _opentitan_binary(ctx):
    tc = ctx.toolchains[LOCALTOOLS_TOOLCHAIN]

    providers = []
    default_info = []
    groups = {}
    ot_bin_env_info = {}
    validations = []
    for exec_env_target in ctx.attr.exec_env:
        exec_env = exec_env_target[ExecEnvInfo]
        name = _binary_name(ctx, exec_env)
        deps = ctx.attr.deps + exec_env.libs

        kind = ctx.attr.kind
        provides, signed = _build_binary(ctx, exec_env, name, deps, kind)
        providers.append(exec_env.provider(kind = kind, **provides))
        default_info.append(provides["default"])
        default_info.append(provides["elf"])
        default_info.append(provides["disassembly"])
        default_info.append(provides["mapfile"])

        # FIXME(cfrantz): logs are a special case and get added into
        # the DefaultInfo provider.
        if "logs" in provides:
            default_info.extend(provides["logs"])

        # FIXME: vmem is a special case for ram targets used in ROM e2e test
        # cases. Some tops like Darjeeling expect a different word size than
        # Earlgrey.
        if provides.get("vmem"):
            default_info.append(provides["vmem"])
        if provides.get("vmem32"):
            default_info.append(provides["vmem32"])

        # FIXME(cfrantz): Special case: The englishbreakfast verilator model
        # requires a non-scrambled ROM image.
        #
        # DV simulation might also need non-scrambled ROM to reduce simulation
        # run times.
        if provides.get("rom32"):
            default_info.append(provides["rom32"])

        groups.update(_as_group_info(exec_env.exec_env, signed))
        groups.update(_as_group_info(exec_env.exec_env, provides))
        ot_bin_env_info[exec_env.provider] = exec_env

        # Module ID checks:
        #
        # We create a file that will not contain anything: this is just to create a "link"
        # between the run action and validation group.
        generated_file = ctx.actions.declare_file("{}.mod-id".format(name))

        # Call bash script that will run opentitantool and capture the output. We want to avoid
        # printing anything if the test is successful but by default opentitantool prints
        # unnecessary information that pollutes the output.
        ctx.actions.run(
            executable = ctx.executable._modid_check,
            arguments = [
                tc.tools.opentitantool.executable.path,
                generated_file.path,
                provides["elf"].path,
            ],
            inputs = [provides["elf"]],
            tools = [tc.tools.opentitantool],
            outputs = [generated_file],
            progress_message = "Checking module IDs for %{label}",
        )
        validations.append(generated_file)

    # Validation group.
    groups["_validation"] = depset(validations)

    providers.append(DefaultInfo(files = depset(default_info)))
    providers.append(OutputGroupInfo(**groups))
    providers.append(OpenTitanBinaryInfo(exec_env = ot_bin_env_info))
    return providers

def _transitive_feature_transition_impl(settings, attr):
    features = settings["@lowrisc_opentitan//command_line_option:features"] + attr.transitive_features
    return {
        "@lowrisc_opentitan//command_line_option:features": features,
    }

_transitive_feature_transition = transition(
    implementation = _transitive_feature_transition_impl,
    inputs = [
        "@lowrisc_opentitan//command_line_option:features",
    ],
    outputs = [
        "@lowrisc_opentitan//command_line_option:features",
    ],
)

common_binary_attrs = {
    "srcs": attr.label_list(
        allow_files = True,
        doc = "The list of C and C++ files that are processed to create the target.",
    ),
    "deps": attr.label_list(
        providers = [CcInfo],
        cfg = _transitive_feature_transition,
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
        default = "@lowrisc_opentitan//util/device_sw_utils:extract_sw_logs_db",
        executable = True,
        cfg = "exec",
    ),
    "rom_scramble_tool": attr.label(
        doc = "ROM scrambling tool.",
        default = "@lowrisc_opentitan//hw/ip/rom_ctrl/util:scramble_image",
        executable = True,
        cfg = "exec",
    ),
    "rom_scramble_mode": attr.string(
        doc = "ROM scrambling mode.",
        default = "base-rom",
    ),
    "transitive_features": attr.string_list(
        default = [],
        doc = "List of features that will apply to this binary, and transitively to all `deps`.",
    ),
    "slot_spec": attr.string_dict(
        default = {},
        doc = "Firmware slot spec to use in this environment",
    ),
    "_check_initial_coverage": attr.label(
        doc = "Tool to check the coverage counter initialization.",
        default = "@lowrisc_opentitan//util/coverage:check_initial_coverage",
        executable = True,
        cfg = "exec",
    ),
}

opentitan_binary = rv_rule(
    implementation = _opentitan_binary,
    attrs = dict(common_binary_attrs.items() + {
        "exec_env": attr.label_list(
            providers = [ExecEnvInfo],
            doc = "List of execution environments for this target.",
        ),
        "_cc_toolchain": attr.label(default = Label("@bazel_tools//tools/cpp:current_cc_toolchain")),
        "_modid_check": attr.label(
            default = "@lowrisc_opentitan//rules/scripts:modid_check",
            executable = True,
            cfg = "exec",
        ),
    }.items()),
    fragments = ["cpp"],
    toolchains = ["@rules_cc//cc:toolchain_type", LOCALTOOLS_TOOLCHAIN],
)

def _testing_bitstream_impl(settings, attr):
    rom = attr.rom if attr.rom else "@lowrisc_opentitan//hw/bitstream/universal:none"
    otp = attr.otp if attr.otp else "@lowrisc_opentitan//hw/bitstream/universal:none"
    return {
        "@lowrisc_opentitan//hw/bitstream/universal:rom": rom,
        "@lowrisc_opentitan//hw/bitstream/universal:otp": otp,
        "@lowrisc_opentitan//hw/bitstream/universal:env": attr.exec_env,
    }

_testing_bitstream = transition(
    implementation = _testing_bitstream_impl,
    inputs = [],
    outputs = [
        "@lowrisc_opentitan//hw/bitstream/universal:rom",
        "@lowrisc_opentitan//hw/bitstream/universal:otp",
        "@lowrisc_opentitan//hw/bitstream/universal:env",
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
        "_modid_check": attr.label(
            default = "@lowrisc_opentitan//rules/scripts:modid_check",
            executable = True,
            cfg = "exec",
        ),
        "_lcov_merger": attr.label(
            default = configuration_field(fragment = "coverage", name = "output_generator"),
            executable = True,
            cfg = "exec",
        ),
        "_collect_cc_coverage": attr.label(
            default = "@lowrisc_opentitan//util/coverage/collect_cc_coverage",
            executable = True,
            cfg = "exec",
        ),
    }.items()),
    fragments = ["cpp"],
    toolchains = ["@rules_cc//cc:toolchain_type", LOCALTOOLS_TOOLCHAIN],
    test = True,
)

def _opentitan_binary_assemble_impl(ctx):
    assembled_bins = []
    result = []
    ot_bin_env_info = {}
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
        ot_bin_env_info[exec_env_provider] = env
    result.append(OpenTitanBinaryInfo(exec_env = ot_bin_env_info))
    return result + [DefaultInfo(files = depset(assembled_bins))]

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
    ot_bin_env_info = {}
    for k in files.keys():
        provider = exec_env[k][ExecEnvInfo].provider
        f = files[k].files.to_list()
        if len(f) != 1:
            fail("files[{}] must supply exactly one file".format(k))

        # Return the exec_env's provider so this rule can be consumed by
        # opentitan_test rules.
        result.append(provider(default = f[0], kind = ctx.attr.kind))
        ot_bin_env_info[provider] = exec_env[k][ExecEnvInfo]
        default_files.append(f[0])

    result.append(OpenTitanBinaryInfo(exec_env = ot_bin_env_info))

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
