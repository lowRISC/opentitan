# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Aspects and rules for making cc_* libraries emit more outputs."""

load("@rules_cc//cc:action_names.bzl", "ACTION_NAMES", "C_COMPILE_ACTION_NAME")
load("//rules:bugfix.bzl", "find_cc_toolchain")
load("//rules:rv.bzl", "rv_rule")

CcSideProductInfo = provider(fields = ["files"])

def _is_c_or_cc(file):
    return file.extension in [
        "c",
        # We only use .cc, but to avoid nasty surprises we support all five
        # C++ file extensions.
        "cc",
        "cpp",
        "cxx",
        "c++",
        "C",
    ]

def _cc_compile_different_output(name, target, ctx, extension, flags, process_all_files = False):
    """
    Helper macro for implementing the .s and .ll outputting libraries.

    In addition to the usual target and ctx inputs for an aspect, it also
    takes an extension to add to each source file of the rule being analyzed,
    and flags to add to the compiler arguments to get the output we want.
    """
    if ctx.rule.kind not in ["cc_library", "cc_binary", "cc_test"]:
        return [CcSideProductInfo(files = depset([]))]

    # This filters out both headers and assembly source inputs, neither of which
    # make sense to generate an .s output for.
    translation_units = [
        src.files.to_list()[0]
        for src in ctx.rule.attr.srcs
        if process_all_files or _is_c_or_cc(src.files.to_list()[0])
    ]

    transitive = []
    for dep in ctx.rule.attr.deps:
        if CcSideProductInfo in dep:
            transitive.append(dep[CcSideProductInfo].files)

    # Libraries consisting of just headers or assembly files have nothing
    # useful to contribute to the output.
    if len(translation_units) == 0:
        return [CcSideProductInfo(files = depset(
            transitive = transitive,
        ))]

    if CcInfo in target:
        cc_info = target[CcInfo]
    else:
        # Some rules, like cc_binary, do NOT produce a CcInfo provider. Therefore,
        # we need to build one from its dependencies.
        cc_info = cc_common.merge_cc_infos(
            direct_cc_infos = [dep[CcInfo] for dep in ctx.rule.attr.deps if CcInfo in dep],
        )
    cc_compile_ctx = cc_info.compilation_context

    cc_toolchain = find_cc_toolchain(ctx)
    feature_configuration = cc_common.configure_features(
        ctx = ctx,
        cc_toolchain = cc_toolchain,
        requested_features = ctx.features,
        unsupported_features = ctx.disabled_features,
    )

    c_compiler_path = cc_common.get_tool_for_action(
        feature_configuration = feature_configuration,
        action_name = ACTION_NAMES.c_compile,
    )

    outputs = []
    for source_file in translation_units:
        output_file = ctx.actions.declare_file(
            # Some source files in the repo are currently pulled in by multiple
            # rules, and this is allowed in general, although not a good idea.
            #
            # Adding the rule name in front of the file name helps mitigate this
            # issue.
            "{}.{}.{}".format(target.label.name, source_file.basename, extension),
        )
        outputs.append(output_file)

        # C files are treated specially, and have different flags applied
        # (e.g. --std=c11).
        # 
        # Things that are neither C or C++ TU files don't get any flags.
        opts = ctx.fragments.cpp.copts + ctx.rule.attr.copts
        if source_file.extension == "c":
            opts += ctx.fragments.cpp.conlyopts
        elif _is_c_or_cc(source_file):
            opts += ctx.fragments.cpp.cxxopts + ctx.rule.attr.cxxopts

        c_compile_variables = cc_common.create_compile_variables(
            feature_configuration = feature_configuration,
            cc_toolchain = cc_toolchain,
            source_file = source_file.path,
            user_compile_flags = opts + flags,
            include_directories = depset(
                direct = [src.dirname for src in cc_compile_ctx.headers.to_list()],
                transitive = [cc_compile_ctx.includes],
            ),
            quote_include_directories = cc_compile_ctx.quote_includes,
            system_include_directories = cc_compile_ctx.system_includes,
            framework_include_directories = cc_compile_ctx.framework_includes,
            preprocessor_defines = depset(
                direct = ctx.rule.attr.local_defines,
                transitive = [cc_compile_ctx.defines],
            ),
        )

        command_line = cc_common.get_memory_inefficient_command_line(
            feature_configuration = feature_configuration,
            action_name = ACTION_NAMES.c_compile,
            variables = c_compile_variables,
        )
        env = cc_common.get_environment_variables(
            feature_configuration = feature_configuration,
            action_name = ACTION_NAMES.c_compile,
            variables = c_compile_variables,
        )

        if hasattr(ctx.file, "_clang_format") and source_file.extension != "S":
            oldenv = env
            env = {"CLANG_FORMAT": ctx.file._clang_format.path}
            for k, v in oldenv.items():
                env[k] = v

        ctx.actions.run_shell(
            mnemonic = name,
            tools = [
                ctx.file._cleanup_script,
            ],
            arguments = [
                c_compiler_path,
                ctx.file._cleanup_script.path,
                output_file.path,
            ] + command_line,
            env = env,
            inputs = depset(
                [source_file],
                transitive = [
                    cc_toolchain.all_files,
                    cc_compile_ctx.headers,
                ],
            ),
            outputs = [output_file],
            command = """
                CC=$1; shift
                CLEANUP=$1; shift
                OUT=$1; shift
                $CC -o - $@ 2> /dev/null | $CLEANUP > $OUT
            """,
        )

    return [CcSideProductInfo(files = depset(
        direct = outputs,
        transitive = transitive,
    ))]

def _cc_preprocess_aspect_impl(target, ctx):
    return _cc_compile_different_output("Preprocess", target, ctx, "i", ["-E"], process_all_files = True)

cc_preprocess_aspect = aspect(
    implementation = _cc_preprocess_aspect_impl,
    doc = """
        An aspect that provides a CcSideProductInfo containing the preprocessed outputs
        of every C/C++ translation unit in the sources of the rule it is applied to and
        all of its dependencies.
    """,
    attrs = {
        "_cleanup_script": attr.label(
            allow_single_file = True,
            default = Label("//rules/scripts:clean_up_cpp_output.sh"),
        ),
        "_clang_format": attr.label(
            default = "@com_lowrisc_toolchain_rv32imc_compiler//:bin/clang-format",
            allow_single_file = True,
            cfg = "host",
            executable = True,
        ),
        "_cc_toolchain": attr.label(
            default = Label("@bazel_tools//tools/cpp:current_cc_toolchain"),
        ),
    },
    attr_aspects = ["deps"],
    provides = [CcSideProductInfo],
    toolchains = ["@rules_cc//cc:toolchain_type"],
    incompatible_use_toolchain_transition = True,
    fragments = ["cpp"],
    host_fragments = ["cpp"],
)

def _cc_assembly_aspect_impl(target, ctx):
    return _cc_compile_different_output("AsmOutput", target, ctx, "s", ["-S"])

cc_asm_aspect = aspect(
    implementation = _cc_assembly_aspect_impl,
    doc = """
        An aspect that provides a CcSideProductInfo containing the assembly file outputs
        of every C/C++ translation unit in the sources of the rule it is applied to and
        all of its dependencies.
    """,
    attrs = {
        "_cleanup_script": attr.label(
            allow_single_file = True,
            default = Label("//rules/scripts:expand_tabs.sh"),
        ),
        "_cc_toolchain": attr.label(
            default = Label("@bazel_tools//tools/cpp:current_cc_toolchain"),
        ),
    },
    attr_aspects = ["deps"],
    provides = [CcSideProductInfo],
    toolchains = ["@rules_cc//cc:toolchain_type"],
    incompatible_use_toolchain_transition = True,
    fragments = ["cpp"],
    host_fragments = ["cpp"],
)

def _cc_llvm_aspect_impl(target, ctx):
    cc_toolchain = find_cc_toolchain(ctx)
    if cc_toolchain.compiler.find("clang") == -1:
        return CcSideProductInfo(files = depset())
    return _cc_compile_different_output("LLVMOutput", target, ctx, "ll", ["-S", "-emit-llvm"])

cc_llvm_aspect = aspect(
    implementation = _cc_llvm_aspect_impl,
    doc = """
        An aspect that provides a CcSideProductInfo containing the LLVM IR file outputs
        of every C/C++ translation unit in the sources of the rule it is applied to and
        all of its dependencies.

        If the current compiler does not appear to be clang, it outputs nothing instead.
    """,
    attrs = {
        "_cleanup_script": attr.label(
            allow_single_file = True,
            default = Label("//rules/scripts:expand_tabs.sh"),
        ),
        "_cc_toolchain": attr.label(
            default = Label("@bazel_tools//tools/cpp:current_cc_toolchain"),
        ),
    },
    attr_aspects = ["deps"],
    provides = [CcSideProductInfo],
    toolchains = ["@rules_cc//cc:toolchain_type"],
    incompatible_use_toolchain_transition = True,
    fragments = ["cpp"],
    host_fragments = ["cpp"],
)

MapFile = provider(fields = ["map_file"])

def _cc_relink_with_linkmap_aspect_impl(target, ctx):
    # As mentioned above, there is no CcInfo in a cc_binary, so we're forced
    # to rumage around the target's actions for its link action, and then
    # re-run it, but capturing the map file as a side-product.
    link_action = None
    for action in target.actions:
        if action.mnemonic == "CppLink":
            link_action = action
            break
    if not link_action:
        return [MapFile(map_file = None)]

    output_file = ctx.actions.declare_file(target.label.name + ".ldmap")

    cc_toolchain = find_cc_toolchain(ctx)
    feature_configuration = cc_common.configure_features(
        ctx = ctx,
        cc_toolchain = cc_toolchain,
        requested_features = ctx.features,
        unsupported_features = ctx.disabled_features,
    )
    linker_path = cc_common.get_tool_for_action(
        feature_configuration = feature_configuration,
        action_name = ACTION_NAMES.cpp_link_executable,
    )

    ctx.actions.run(
        mnemonic = "LinkMapFile",
        executable = linker_path,
        arguments = link_action.argv[1:] + ["-Wl,-Map=" + output_file.path],
        env = link_action.env,
        inputs = link_action.inputs,
        outputs = [output_file],
    )

    return [MapFile(map_file = output_file)]

cc_relink_with_linkmap_aspect = aspect(
    implementation = _cc_relink_with_linkmap_aspect_impl,
    doc = """
        An aspect to apply to a cc_binary rule that rebuilds its linker invocation and
        re-runs it, capturing the map file as an output.

        This needs to exist because cc_binary currently does not allow us to specify that
        it may emit multiple outputs.
    """,
    attrs = {
        "_cc_toolchain": attr.label(
            default = Label("@bazel_tools//tools/cpp:current_cc_toolchain"),
        ),
    },
    provides = [MapFile],
    toolchains = ["@rules_cc//cc:toolchain_type"],
    incompatible_use_toolchain_transition = True,
    fragments = ["cpp"],
    host_fragments = ["cpp"],
)

def _rv_preprocess_impl(ctx):
    return [DefaultInfo(
        files = ctx.attr.target[CcSideProductInfo].files,
        data_runfiles = ctx.runfiles(transitive_files = ctx.attr.target[CcSideProductInfo].files),
    )]

rv_preprocess = rv_rule(
    implementation = _rv_preprocess_impl,
    attrs = {"target": attr.label(aspects = [cc_preprocess_aspect])},
)

def _rv_asm_impl(ctx):
    return [DefaultInfo(
        files = ctx.attr.target[CcSideProductInfo].files,
        data_runfiles = ctx.runfiles(transitive_files = ctx.attr.target[CcSideProductInfo].files),
    )]

rv_asm = rv_rule(
    implementation = _rv_asm_impl,
    attrs = {"target": attr.label(aspects = [cc_asm_aspect])},
)

def _llvm_ir_impl(ctx):
    return [DefaultInfo(
        files = ctx.attr.target[CcSideProductInfo].files,
        data_runfiles = ctx.runfiles(transitive_files = ctx.attr.target[CcSideProductInfo].files),
    )]

rv_llvm_ir = rv_rule(
    implementation = _rv_asm_impl,
    attrs = {"target": attr.label(aspects = [cc_llvm_aspect])},
)

def _cc_relink_with_linkmap_impl(ctx):
    return [DefaultInfo(
        files = depset([ctx.attr.target[MapFile].map_file]),
        data_runfiles = ctx.runfiles(files = [ctx.attr.target[MapFile].map_file]),
    )]

rv_relink_with_linkmap = rv_rule(
    implementation = _cc_relink_with_linkmap_impl,
    attrs = {"target": attr.label(aspects = [cc_relink_with_linkmap_aspect])},
)
