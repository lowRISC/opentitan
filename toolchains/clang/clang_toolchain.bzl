# MIT License
#
# Copyright (c) 2019 Nathaniel Brough
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

load("@rules_cc//cc:defs.bzl", "cc_toolchain")
load(
    "@bazel_tools//tools/cpp:cc_toolchain_config_lib.bzl",
    "tool_path",
)
load("@bazel_tools//tools/build_defs/cc:action_names.bzl", "ACTION_NAMES")
load("@com_llvm_compiler//:defs.bzl", "SYSTEM_INCLUDE_COMMAND_LINE", "SYSTEM_INCLUDE_PATHS", "SYSTEM_SYSROOT")
load("//toolchains/features/common:defs.bzl", "GetCommonFeatures")

_ARM_NONE_VERSION = "9.2.1"
_CPP_ALL_COMPILE_ACTIONS = [
    ACTION_NAMES.assemble,
    ACTION_NAMES.preprocess_assemble,
    ACTION_NAMES.linkstamp_compile,
    ACTION_NAMES.cpp_compile,
    ACTION_NAMES.cpp_header_parsing,
    ACTION_NAMES.cpp_module_compile,
    ACTION_NAMES.cpp_module_codegen,
    ACTION_NAMES.lto_backend,
    ACTION_NAMES.clif_match,
]

_C_ALL_COMPILE_ACTIONS = [
    ACTION_NAMES.assemble,
    ACTION_NAMES.c_compile,
]

_LD_ALL_ACTIONS = [
    ACTION_NAMES.cpp_link_executable,
]

def _get_injected_headers_command_line(ctx):
    command_line = []
    for hdr_lib in ctx.attr.injected_hdr_deps:
        cc_ctx = hdr_lib[CcInfo].compilation_context
        for hdr in cc_ctx.headers.to_list():
            command_line += ["-include", hdr.short_path]
    return command_line

def _get_additional_system_includes_command_line(ctx):
    command_line = []
    for hdr_lib in ctx.attr.system_hdr_deps:
        cc_ctx = hdr_lib[CcInfo].compilation_context
        for inc in cc_ctx.system_includes.to_list():
            command_line += ["-isystem", inc]
    return command_line

def _get_additional_system_include_paths(ctx):
    include_paths = []
    for hdr_lib in ctx.attr.system_hdr_deps:
        cc_ctx = hdr_lib[CcInfo].compilation_context
        for inc in cc_ctx.system_includes.to_list():
            if inc not in ".":
                include_paths.append(inc)
    return include_paths

def _clang_toolchain_config_info_impl(ctx):
    tool_paths = [
        tool_path(
            name = "gcc",
            path = "clang_wrappers/{os}/gcc",
        ),
        tool_path(
            name = "ld",
            path = "clang_wrappers/{os}/ld",
        ),
        tool_path(
            name = "ar",
            path = "clang_wrappers/{os}/ar",
        ),
        tool_path(
            name = "cpp",
            path = "clang_wrappers/{os}/cpp",
        ),
        tool_path(
            name = "gcov",
            path = "clang_wrappers/{os}/gcov",
        ),
        tool_path(
            name = "nm",
            path = "clang_wrappers/{os}/nm",
        ),
        tool_path(
            name = "objdump",
            path = "clang_wrappers/{os}/objdump",
        ),
        tool_path(
            name = "strip",
            path = "clang_wrappers/{os}/strip",
        ),
    ]
    os = "nix"
    postfix = ""
    if ctx.host_configuration.host_path_separator == ";":
        os = "windows"
        postfix = ".bat"
    tool_paths = [tool_path(name = t.name, path = t.path.format(os = os) + postfix) for t in tool_paths]

    common_features = GetCommonFeatures(
        compiler = "CLANG",
        architecture = "x86-64",
        float_abi = "auto",
        endian = "little",
        fpu = "auto",
        include_paths = _get_additional_system_includes_command_line(ctx) + SYSTEM_INCLUDE_COMMAND_LINE + _get_injected_headers_command_line(ctx),
        sysroot = SYSTEM_SYSROOT,
    )
    toolchain_config_info = cc_common.create_cc_toolchain_config_info(
        ctx = ctx,
        toolchain_identifier = ctx.attr.toolchain_identifier,
        cxx_builtin_include_directories = SYSTEM_INCLUDE_PATHS + _get_additional_system_include_paths(ctx),
        host_system_name = "i686-unknown-linux-gnu",
        target_system_name = "arm-none-eabi",
        target_cpu = "x86_64",
        target_libc = "unknown",
        compiler = "clang",
        abi_version = "unknown",
        abi_libc_version = "unknown",
        tool_paths = tool_paths,
        features = [
            common_features.all_warnings,
            common_features.all_warnings_as_errors,
            common_features.reproducible,
            common_features.includes,
            common_features.symbol_garbage_collection,
            common_features.architecture,
            common_features.dbg,
            common_features.opt,
            common_features.fastbuild,
            common_features.output_format,
            common_features.coverage,
            common_features.misc,
        ],
    )
    return toolchain_config_info

clang_toolchain_config = rule(
    implementation = _clang_toolchain_config_info_impl,
    attrs = {
        "toolchain_identifier": attr.string(
            mandatory = True,
            doc = "Identifier used by the toolchain, this should be consistent with the cc_toolchain rule attribute",
        ),
        "system_hdr_deps": attr.label_list(
            doc = "A set of additional system header libraries that are added as a dependency of every cc_<target>",
            default = ["@bazel_embedded_upstream_toolchain//:polyfill"],
            providers = [CcInfo],
        ),
        "injected_hdr_deps": attr.label_list(
            doc = "A set of headers that are injected into the toolchain e.g. by -include",
            default = ["@bazel_embedded_upstream_toolchain//:injected_headers"],
            providers = [CcInfo],
        ),
        "_clang_wrappers": attr.label(
            doc = "Passthrough gcc wrappers used for the compiler",
            default = "//toolchains/clang/clang_wrappers:all",
        ),
    },
    provides = [CcToolchainConfigInfo],
)

def compiler_components(system_hdr_deps, injected_hdr_deps):
    native.filegroup(
        name = "additional_headers",
        srcs = [
            system_hdr_deps,
            injected_hdr_deps,
        ],
        #output_group = "CcInfo",
    )
    native.filegroup(
        name = "compiler_components",
        srcs = [
            "//toolchains/clang/clang_wrappers:all",
            "@com_llvm_compiler//:all",
            ":additional_headers",
        ],
    )

def clang_toolchain(name):
    toolchain_config = name + "_config"

    compiler_components(
        system_hdr_deps = "@bazel_embedded_upstream_toolchain//:polyfill",
        injected_hdr_deps = "@bazel_embedded_upstream_toolchain//:injected_headers",
    )
    compiler_components_target = ":compiler_components"

    clang_toolchain_config(
        name = toolchain_config,
        toolchain_identifier = "clang",
    )

    cc_toolchain(
        name = name,
        all_files = compiler_components_target,
        compiler_files = compiler_components_target,
        dwp_files = compiler_components_target,
        linker_files = compiler_components_target,
        objcopy_files = compiler_components_target,
        strip_files = compiler_components_target,
        as_files = compiler_components_target,
        ar_files = compiler_components_target,
        supports_param_files = 0,
        toolchain_config = ":" + toolchain_config,
        toolchain_identifier = "clang",
    )

    native.toolchain(
        name = name + "_cc_toolchain",
        exec_compatible_with = [
            "@platforms//cpu:x86_64",
            "@platforms//os:linux",
        ],
        target_compatible_with = [
            "@platforms//cpu:x86_64",
            "@platforms//os:linux",
        ],
        toolchain = ":" + name,
        toolchain_type = "@bazel_tools//tools/cpp:toolchain_type",
    )

def register_clang_toolchain():
    native.register_toolchains("@bazel_embedded//toolchains/clang:all")
