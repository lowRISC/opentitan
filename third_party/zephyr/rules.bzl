# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_cc//cc:find_cc_toolchain.bzl", "find_cc_toolchain")

def _devicetree_library_impl(ctx):
    processed_dt_file = ctx.actions.declare_file(ctx.attr.name + ".cpp.dts")
    debug_dt_file = ctx.actions.declare_file(ctx.attr.name + ".h.dts")
    devicetree_generated = ctx.actions.declare_file(ctx.attr.name + "/devicetree_generated.h")
    outputs = [processed_dt_file]
    args = ctx.actions.args()
    args.add("-E")
    args.add("-nostdinc")
    args.add("-x")
    args.add("assembler-with-cpp")
    args.add(ctx.file.src.path)
    args.add("-o")
    args.add(processed_dt_file.path)

    cc_toolchain = find_cc_toolchain(ctx).cc
    cc_info = cc_common.merge_cc_infos(
        direct_cc_infos = [dep[CcInfo] for dep in ctx.attr.deps if CcInfo in dep],
    )

    cc_compile_ctx = cc_info.compilation_context
    for define in cc_compile_ctx.defines.to_list():
        args.add("-D{}".format(define))
    for include in cc_compile_ctx.includes.to_list():
        args.add("-I{}".format(include))
    for quote_include in cc_compile_ctx.quote_includes.to_list():
        args.add("-iquote")
        args.add(quote_include)
    for system_include in cc_compile_ctx.system_includes.to_list():
        args.add("-isystem")
        args.add(system_include)

    cpp_inputs = depset(
        [ctx.file.src],
        transitive = [
            cc_toolchain.all_files,
            cc_compile_ctx.headers,
        ],
    )

    ctx.actions.run(
        outputs = [processed_dt_file],
        inputs = cpp_inputs,
        executable = cc_toolchain.preprocessor_executable,
        arguments = [args],
        mnemonic = "DtsPreprocess",
    )

    # Try to get common substring for each group of paths.
    # This only works if the filegroups are disjoint and do not point to files
    # outside their package directories.
    bindings_dirs = {}
    for binding in ctx.attr.bindings:
        binding_dir = binding.files.to_list()[0].dirname
        for yaml_file in binding.files.to_list():
            if len(yaml_file.dirname) < len(binding_dir):
                binding_dir = yaml_file.dirname
        bindings_dirs[binding_dir] = 0

    gen_args = ctx.actions.args()
    gen_args.add("--dts")
    gen_args.add(processed_dt_file.path)
    gen_args.add("--dts-out")
    gen_args.add(debug_dt_file.path)
    gen_args.add("--dtc-flags=-Wno-simple_bus_reg")
    gen_args.add("--header-out")
    gen_args.add(devicetree_generated.path)
    gen_args.add("--bindings-dirs")
    for directory in bindings_dirs.keys():
        gen_args.add(directory)
    ctx.actions.run(
        outputs = [devicetree_generated, debug_dt_file],
        inputs = depset(
            direct = [processed_dt_file],
            transitive = [cpp_inputs, depset(ctx.files.bindings)],
        ),
        executable = ctx.executable._gen_defines_script,
        arguments = [gen_args],
    )

    return [
        DefaultInfo(
            files = depset([devicetree_generated]),
        ),
        CcInfo(
            compilation_context = cc_common.create_compilation_context(
                headers = depset(direct = [devicetree_generated]),
                system_includes = depset(direct = [devicetree_generated.dirname]),
            ),
        ),
    ]

devicetree_library = rule(
    implementation = _devicetree_library_impl,
    attrs = {
        "src": attr.label(
            doc = "Label for the top-level devicetree source",
            allow_single_file = True,
            mandatory = True,
        ),
        "deps": attr.label_list(
            doc = "Devicetree dependencies",
            allow_files = True,
        ),
        "bindings": attr.label_list(
            doc = "The labels for bindings files to be included",
            allow_empty = False,
            allow_files = True,
            mandatory = True,
        ),
        "_gen_defines_script": attr.label(
            doc = "Path to Zephyr's DT header generation script",
            executable = True,
            default = "@zephyr//:gen_defines",
            cfg = "exec",
        ),
    },
    toolchains = ["@rules_cc//cc:toolchain_type"],
)
