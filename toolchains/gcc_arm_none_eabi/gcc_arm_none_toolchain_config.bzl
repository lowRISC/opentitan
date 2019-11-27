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
    "feature",
    "flag_group",
    "flag_set",
    "tool_path",
)
load("@bazel_tools//tools/build_defs/cc:action_names.bzl", "ACTION_NAMES")

_ARM_NONE_EABI_VERSION = "9.2.1"
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

def _gcc_include_paths(arm_none_eabi_version):
    # GCC version independant include directories
    include_path_templates = [
        "external/com_gcc_arm_none_eabi_compiler/arm-none-eabi/include/c++/{arm_none_eabi_gcc_ver}",
        "external/com_gcc_arm_none_eabi_compiler/arm-none-eabi/include/c++/{arm_none_eabi_gcc_ver}/arm-none-eabi",
        "external/com_gcc_arm_none_eabi_compiler/arm-none-eabi/include/c++/{arm_none_eabi_gcc_ver}/backward",
        "external/com_gcc_arm_none_eabi_compiler/lib/gcc/arm-none-eabi/{arm_none_eabi_gcc_ver}/include",
        "external/com_gcc_arm_none_eabi_compiler/lib/gcc/arm-none-eabi/{arm_none_eabi_gcc_ver}/include-fixed",
        "external/com_gcc_arm_none_eabi_compiler/arm-none-eabi/include",
    ]

    # Create version specific include paths
    include_paths = []
    for template in include_path_templates:
        include_paths += ["-I", template.format(arm_none_eabi_gcc_ver = arm_none_eabi_version)]
    return include_paths

def _gcc_arm_none_toolchain_config_info_impl(ctx):
    tool_paths = [
        tool_path(
            name = "gcc",
            path = "gcc_wrappers/gcc",
        ),
        tool_path(
            name = "ld",
            path = "gcc_wrappers/ld",
        ),
        tool_path(
            name = "ar",
            path = "gcc_wrappers/ar",
        ),
        tool_path(
            name = "cpp",
            path = "gcc_wrappers/cpp",
        ),
        tool_path(
            name = "gcov",
            path = "gcc_wrappers/gcov",
        ),
        tool_path(
            name = "nm",
            path = "gcc_wrappers/nm",
        ),
        tool_path(
            name = "objdump",
            path = "gcc_wrappers/objdump",
        ),
        tool_path(
            name = "strip",
            path = "gcc_wrappers/strip",
        ),
    ]

    toolchain_include_directories_feature = feature(
        name = "toolchain_include_directories",
        enabled = True,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS + _C_ALL_COMPILE_ACTIONS,
                flag_groups = [
                    flag_group(
                        # Disable system includes, then re-enable includes using -I flag
                        flags = ["-nostdinc"] + _gcc_include_paths(_ARM_NONE_EABI_VERSION),
                    ),
                ],
            ),
        ],
    )

    toolchain_architecture_feature = feature(
        name = "toolchain_architecture",
        enabled = True,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS + _C_ALL_COMPILE_ACTIONS +
                          _LD_ALL_ACTIONS,
                flag_groups = [
                    flag_group(
                        flags = [
                            # Set default architecture
                            "-mthumb",
                            # Set the system architecture/cpu
                            "-march={}".format(ctx.attr.arch),
                            # Set the floating point calculation mode hard/soft
                            "-mfloat-abi={}".format(ctx.attr.float_abi),
                            # Set the endianess of the architecture
                            "-m{}-endian".format(ctx.attr.endian),
                            # Set the fpu available on the chip
                            "-mfpu={}".format(ctx.attr.fpu),
                        ],
                    ),
                ],
            ),
        ],
    )

    toolchain_rtti_feature = feature(
        name = "toolchain_rtti",
        enabled = not ctx.attr.rtti,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [
                    flag_group(
                        flags = [
                            # Disable runtime type information
                            "-fno-rtti",
                        ],
                    ),
                ],
            ),
        ],
    )

    toolchain_exceptions_feature = feature(
        name = "toolchain_exceptions",
        enabled = not ctx.attr.exceptions,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [
                    flag_group(
                        flags = [
                            # Disable Exceptions
                            "-fno-exceptions",
                            "-fno-non-call-exceptions",
                        ],
                    ),
                ],
            ),
        ],
    )

    toolchain_optimisation_feature = feature(
        name = "toolchain_optimisation",
        enabled = True,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS + _C_ALL_COMPILE_ACTIONS,
                flag_groups = [
                    flag_group(
                        flags = [
                            # Indicate that this program may not neccesarily be able to use standard system calls
                            "-ffreestanding",
                            # Instantiate global variables only once
                            "-fno-common",
                            # Emits guards against functions that have references to local array definitions
                            "-fstack-protector-strong",
                            # Allow the linker to eliminate binary dead code by putting the function code in different sections to data
                            "-ffunction-sections",
                            "-fdata-sections",
                            "-Wl,--gc-sections",
                            # Optimise for flash size
                            "-Os",
                            # Inline small functions if less instructions are likely to be executed
                            "-finline-small-functions",
                            # Enable all warnings
                            "-Wall",
                            # Create Reproducible builds
                            "-Werror=date-time",
                        ],
                    ),
                ],
            ),
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [
                    flag_group(
                        flags = [
                            # Disable teardown/destructors for static variables
                            "-fno-use-cxa-atexit",
                        ],
                    ),
                ],
            ),
            flag_set(
                actions = _LD_ALL_ACTIONS,
                flag_groups = [
                    flag_group(
                        flags = [
                            # Remove dead sections of code at link time
                            "-Wl,--gc-sections",
                            # Use standalone spec
                            "-Wl,-lnosys",
                        ],
                    ),
                ],
            ),
        ],
    )

    toolchain_generate_debug_symbols = feature(
        name = "dbg",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS + _C_ALL_COMPILE_ACTIONS,
                flag_groups = [
                    flag_group(
                        flags = [
                            "-O",
                            "-g3",
                        ],
                    ),
                ],
            ),
            flag_set(
                actions = ["ACTION_NAMES.cpp_link_executable"],
                flag_groups = [
                    flag_group(
                        flags = ["-Wl", "--gdb-index"],
                    ),
                ],
            ),
        ],
    )

    toolchain_binary_format_output = feature(
        name = "toolchain_binary_output_format",
        enabled = True,
        flag_sets = [
            flag_set(
                actions = [ACTION_NAMES.strip],
                flag_groups = [
                    flag_group(
                        flags = [
                            # Strip all symbols
                            "--strip-all",
                            # Set binary format with compiler flag passthrough
                            "--input-target=elf32-{}".format(ctx.attr.endian),
                            "--output-target={}".format(ctx.attr.binary_format),
                        ],
                    ),
                ],
            ),
        ],
    )

    toolchain_config_info = cc_common.create_cc_toolchain_config_info(
        ctx = ctx,
        toolchain_identifier = ctx.attr.toolchain_identifier,
        host_system_name = "i686-unknown-linux-gnu",
        target_system_name = "arm-none-eabi",
        target_cpu = ctx.attr.arch,
        target_libc = "unknown",
        compiler = "arm-none-eabi-gcc-8.2.50",
        abi_version = "gcc-8.2.50",
        abi_libc_version = "unknown",
        tool_paths = tool_paths,
        features = [
            toolchain_include_directories_feature,
            toolchain_architecture_feature,
            toolchain_rtti_feature,
            toolchain_exceptions_feature,
            toolchain_optimisation_feature,
            toolchain_binary_format_output,
            toolchain_dynamic_memory_feature,
            toolchain_generate_debug_symbols,
        ],
    )
    return toolchain_config_info

gcc_arm_none_toolchain_config = rule(
    implementation = _gcc_arm_none_toolchain_config_info_impl,
    attrs = {
        "arch": attr.string(
            default = "armv4",
            doc = "System architecture",
            mandatory = False,
            values = [
                "armv4",
                "armv4t",
                "armv5t",
                "armv5te",
                "armv6",
                "armv6j",
                "armv6k",
                "armv6kz",
                "armv6t2",
                "armv6z",
                "armv6zk",
                "armv7",
                "armv7-a",
                "armv7ve",
                "armv8-a",
                "armv8.1-a",
                "armv8.2-a",
                "armv8.3-a",
                "armv8.4-a",
                "armv8.5-a",
                "armv7-r",
                "armv8-r",
                "armv6-m",
                "armv6s-m",
                "armv7-m",
                "armv7e-m",
                "armv8-m.base",
                "armv8-m.main",
                "iwmmxt",
                "iwmmxt2",
            ],
        ),
        "float_abi": attr.string(
            default = "soft",
            doc = "Application Binary Interface",
            mandatory = False,
            values = ["soft", "softfp", "hard"],
        ),
        "fpu": attr.string(
            default = "auto",
            doc = "Floating point unit",
            mandatory = False,
            values = [
                "none",
                "auto",
                "vfpv2",
                "vfpv3",
                "vfpv3-fp16",
                "vfpv3-d16",
                "vfpv3-d16-fp16",
                "vfpv3xd",
                "vfpv3xd-fp16",
                "neon-vfpv3",
                "neon-fp16",
                "vfpv4",
                "vfpv4-d16",
                "fpv4-sp-d16",
                "neon-vfpv4",
                "fpv5-d16",
                "fpv5-sp-d16",
                "fp-armv8",
                "neon-fp-armv8",
                "crypto-neon-fp-armv8",
            ],
        ),
        "endian": attr.string(
            default = "little",
            doc = "Endianess",
            mandatory = False,
            values = ["little", "big"],
        ),
        "rtti": attr.bool(
            default = True,
            doc = "Runtime type information enabled",
            mandatory = False,
        ),
        "exceptions": attr.bool(
            default = False,
            doc = "C++ exceptions (disabled by default)",
            mandatory = False,
        ),
        "dynamic_memory": attr.bool(
            default = False,
            doc = "Disable dynamic memory allocation",
            mandatory = False,
        ),
        "binary_format": attr.string(
            default = "binary",
            doc = "Binary output format",
            mandatory = False,
            values = [
                # List created from `arm-none-eabi-objdump -i`
                "elf32-littlearm",
                "elf32-littlearm-fdpic",
                "elf32-bigarm",
                "elf32-bigarm-fdpic",
                "elf32-little",
                "elf32-big",
                "srec",
                "symbolsrec",
                "verilog",
                "tekhex",
                "binary",
                "ihex",
            ],
        ),
        "toolchain_identifier": attr.string(
            mandatory = True,
            doc = "Indentifier used by the toolchain, this should be consistent with the cc_toolchain rule attribute",
        ),
        "_gcc_wrappers": attr.label(
            doc = "Passthrough gcc wrappers used for the compiler",
            default = "@com_gcc_arm_none_eabi//gcc_wrappers:all",
        ),
    },
    provides = [CcToolchainConfigInfo],
)

def _toolchain_components():
    native.filegroup(
        name = "compiler_components",
        srcs = [
            "@com_gcc_arm_none_eabi//gcc_wrappers:all",
            "@com_gcc_arm_none_eabi_compiler//:all",
        ],
    )

def gcc_arm_none_toolchain(name, toolchain_identifier, toolchain_config):
    """Create a gcc arm none eabi toolchain 

    Keyword arguments:
    name -- target name for the toolchain
    cpu -- cpu for the toolchain
    toolchain_identifier -- toolchain identifier should be consistent with toolchain identifier for toolchain_config
    toolchain_config -- toolchain configuration target
"""
    _toolchain_components()
    cc_toolchain(
        name = name,
        all_files = ":compiler_components",
        compiler_files = ":compiler_components",
        dwp_files = ":compiler_components",
        linker_files = ":compiler_components",
        objcopy_files = ":compiler_components",
        strip_files = ":compiler_components",
        as_files = ":compiler_components",
        ar_files = ":compiler_components",
        supports_param_files = 0,
        toolchain_config = toolchain_config,
        toolchain_identifier = toolchain_identifier,
    )

def gcc_arm_none_toolchain_preconfigured():
    """Create a preconfigured toolchain with target = ':arm_none_eabi_generic_toolchain', this should be compatible with all modern ARM cpus"""

    TOOLCHAIN_IDENTIFIER = "arm_none_eabi_generic"
    TOOLCHAIN_CONFIG_TARGET = "arm_none_eabi_generic_config"

    # Use arm4vt as it is the most cross-compatible instruction set still supported by ARM
    CPU = "armv4t"

    # Collect toolchain components
    _toolchain_components()

    # Create generic compiler config
    gcc_arm_none_toolchain_config(
        name = TOOLCHAIN_CONFIG_TARGET,
        arch = CPU,
        # Using soft floating abi is slow but should be supported on most targets
        float_abi = "soft",
        # Enable run time type information, this adds significantly to the binary size, however enables polymorphic types
        rtti = True,
        toolchain_identifier = TOOLCHAIN_IDENTIFIER,
    )

    # Create a compiler using the generic config
    gcc_arm_none_toolchain(
        name = "arm_none_eabi_generic_toolchain",
        cpu = CPU,
        toolchain_identifier = ":" + TOOLCHAIN_IDENTIFIER,
        toolchain_config = ":" + TOOLCHAIN_CONFIG_TARGET,
    )
