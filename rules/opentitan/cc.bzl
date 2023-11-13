# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_cc//cc:find_cc_toolchain.bzl", "find_cc_toolchain")
load(
    "@lowrisc_opentitan//rules:rv.bzl",
    "rv_rule",
    _OPENTITAN_CPU = "OPENTITAN_CPU",
    _OPENTITAN_PLATFORM = "OPENTITAN_PLATFORM",
    _opentitan_transition = "opentitan_transition",
)
load("@lowrisc_opentitan//rules:signing.bzl", "sign_binary")
load("@lowrisc_opentitan//rules/opentitan:exec_env.bzl", "ExecEnvInfo")
load("@lowrisc_opentitan//rules/opentitan:util.bzl", "get_fallback", "get_override")
load(
    "@lowrisc_opentitan//rules/opentitan:transform.bzl",
    "obj_disassemble",
    "obj_transform",
)

# Re-exports of names from transition.bzl; many files in the repo use opentitan.bzl
# to get to them.
OPENTITAN_CPU = _OPENTITAN_CPU
OPENTITAN_PLATFORM = _OPENTITAN_PLATFORM
opentitan_transition = _opentitan_transition

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
        linkopts: Linker options for this binary.
    Returns:
      (elf_file, map_file) File objects.
    """
    cc_toolchain = find_cc_toolchain(ctx).cc
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
    linkopts = [
        "-Wl,-Map={}".format(mapfile.path),
        "-nostdlib",
    ] + _expand(ctx, "linkopts", get_override(ctx, "attr.linkopts", kwargs))

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
    elf, mapfile = ot_binary(
        ctx,
        name = name,
        deps = deps,
        linker_script = linker_script,
    )
    binary = obj_transform(
        ctx,
        name = name,
        suffix = "bin",
        format = "binary",
        src = elf,
    )

    manifest = get_fallback(ctx, "file.manifest", exec_env)
    rsa_key = get_fallback(ctx, "attr.rsa_key", exec_env)
    spx_key = get_fallback(ctx, "attr.spx_key", exec_env)
    if manifest and kind != "ram":
        if not rsa_key:
            fail("Signing requires a manifest and an rsa_key, and optionally an spx_key")
        signed = sign_binary(
            ctx,
            bin = binary,
            rsa_key = rsa_key,
            spx_key = spx_key,
            manifest = manifest,
            # FIXME: will need to supply hsmtool when we add NitroKey signing.
            _tool = exec_env._opentitantool,
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
    providers = []
    default_info = []
    groups = {}
    for exec_env in ctx.attr.exec_env:
        exec_env = exec_env[ExecEnvInfo]
        name = _binary_name(ctx, exec_env)
        deps = ctx.attr.deps + [exec_env.lib]
        kind = ctx.attr.kind
        provides, signed = _build_binary(ctx, exec_env, name, deps, kind)
        providers.append(exec_env.provider(**provides))
        default_info.append(provides["default"])

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

    providers.append(DefaultInfo(files = depset(default_info)))
    providers.append(OutputGroupInfo(**groups))
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
}

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

def _opentitan_test(ctx):
    exec_env = ctx.attr.exec_env[ExecEnvInfo]

    if ctx.attr.srcs or ctx.attr.deps:
        name = _binary_name(ctx, exec_env)
        deps = ctx.attr.deps + [exec_env.lib]
        kind = ctx.attr.kind
        provides, signed = _build_binary(ctx, exec_env, name, deps, kind)
        p = exec_env.provider(**provides)
    else:
        p = None

    executable, runfiles = exec_env.test_dispatch(ctx, exec_env, p)
    return DefaultInfo(
        executable = executable,
        runfiles = ctx.runfiles(files = runfiles),
    )

opentitan_test = rv_rule(
    implementation = _opentitan_test,
    attrs = dict(common_binary_attrs.items() + {
        "exec_env": attr.label(
            providers = [ExecEnvInfo],
            doc = "List of exeuction environments for this target.",
        ),
        "test_harness": attr.label(
            default = "//sw/host/opentitantool:opentitantool",
            executable = True,
            cfg = "exec",
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
            doc = "Bitstream override for this test",
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
        "_cc_toolchain": attr.label(default = Label("@bazel_tools//tools/cpp:current_cc_toolchain")),
    }.items()),
    fragments = ["cpp"],
    toolchains = ["@rules_cc//cc:toolchain_type"],
    test = True,
)
