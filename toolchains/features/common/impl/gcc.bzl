load(
    "@bazel_tools//tools/cpp:cc_toolchain_config_lib.bzl",
    "feature",
    "flag_group",
    "flag_set",
)
load("//toolchains/features/common:types.bzl", "all_common_features")
load("@bazel_tools//tools/build_defs/cc:action_names.bzl", "ACTION_NAMES")

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

def GccIncludeFeature(include_paths):
    _INCLUDE_FEATURE = feature(
        name = "includes",
        enabled = True,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS + _C_ALL_COMPILE_ACTIONS,
                flag_groups = [
                    flag_group(
                        # Disable system includes, then re-enable includes using -I flag
                        flags = ["-nostdinc", "-no-canonical-prefixes", "-fno-canonical-system-headers"] + include_paths,
                    ),
                ],
            ),
        ],
    )
    return _INCLUDE_FEATURE

def GccAchitectureFeature(architecture, float_abi, endian, fpu):
    if fpu == "none":
        fpu = "auto"
    if architecture == 'riscv32':
        # TODO(cfrantz): why do I have to do this?  Seems the lowRISC gcc
        # doesn't support `-mfpu`, `-mfloat-abi` or `-mlittle-endian`.
        _ARCHITECTURE_FEATURE = feature(
            name = "architecture",
            enabled = True,
            flag_sets = [
                flag_set(
                    actions = _CPP_ALL_COMPILE_ACTIONS + _C_ALL_COMPILE_ACTIONS +
                              _LD_ALL_ACTIONS,
                    flag_groups = [
                        flag_group(
                            flags = [
                                # Set the system architecture/cpu
                                "-march=rv32imc",
                                "-mabi=ilp32",
                                "-mcmodel=medany",
                            ],
                        ),
                    ],
                ),
            ],
        )
    else:
        _ARCHITECTURE_FEATURE = feature(
            name = "architecture",
            enabled = True,
            flag_sets = [
                flag_set(
                    actions = _CPP_ALL_COMPILE_ACTIONS + _C_ALL_COMPILE_ACTIONS +
                              _LD_ALL_ACTIONS,
                    flag_groups = [
                        flag_group(
                            flags = [
                                # Set the system architecture/cpu
                                "-march=" + architecture,
                                # Set the fpu
                                "-mfpu=" + fpu,
                                # Set the floating point calculation mode hard/soft
                                "-mfloat-abi={}".format(float_abi),
                                # Set the endianess of the architecture
                                "-m{}-endian".format(endian),
                                # Set the fpu available on the chip
                            ],
                        ),
                    ],
                ),
            ],
        )

    return _ARCHITECTURE_FEATURE

_ALL_WARNINGS_FEATURE = feature(
    name = "all_warnings",
    enabled = True,
    flag_sets = [
        flag_set(
            actions = _CPP_ALL_COMPILE_ACTIONS + _C_ALL_COMPILE_ACTIONS,
            flag_groups = [
                flag_group(
                    flags = ["-Wall", "-Wpedantic"],
                ),
            ],
        ),
    ],
)
_ALL_WARNINGS_AS_ERRORS_FEATURE = feature(
    name = "all_warnings_as_errors",
    enabled = False,
    flag_sets = [
        flag_set(
            actions = _CPP_ALL_COMPILE_ACTIONS + _C_ALL_COMPILE_ACTIONS,
            flag_groups = [
                flag_group(
                    flags = ["-Werror"],
                ),
            ],
        ),
    ],
)

_REPRODUCIBLE_FEATURE = feature(
    name = "reproducible",
    enabled = True,
    flag_sets = [
        flag_set(
            actions = _CPP_ALL_COMPILE_ACTIONS + _C_ALL_COMPILE_ACTIONS,
            flag_groups = [
                flag_group(
                    flags = [
                        "-Werror=date-time",
                    ],
                ),
            ],
        ),
    ],
)

_EXCEPTIONS_FEATURE = feature(
    name = "exceptions",
    enabled = True,
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

_SYMBOL_GARBAGE_COLLECTION = feature(
    name = "symbol_garbage_collection",
    enabled = True,
    flag_sets = [
        flag_set(
            actions = _CPP_ALL_COMPILE_ACTIONS + _C_ALL_COMPILE_ACTIONS,
            flag_groups = [
                flag_group(
                    flags = [
                        # Prime sections for garbage collection during compilation
                        "-ffunction-sections",
                        "-fdata-sections",
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
                    ],
                ),
            ],
        ),
    ],
)

_DEBUG_FEATURE = feature(
    name = "dbg",
    enabled = False,
    flag_sets = [
        flag_set(
            actions = _CPP_ALL_COMPILE_ACTIONS + _C_ALL_COMPILE_ACTIONS,
            flag_groups = [
                flag_group(
                    flags = [
                        "-O0",
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
    provides = ["compilation_mode"],
)

_FASTBUILD_FEATURE = feature(
    name = "fastbuild",
    enabled = False,
    flag_sets = [
        flag_set(
            actions = _CPP_ALL_COMPILE_ACTIONS + _C_ALL_COMPILE_ACTIONS,
            flag_groups = [
                flag_group(
                    flags = [
                        "-O",
                    ],
                ),
            ],
        ),
    ],
    provides = ["compilation_mode"],
)

_OPT_FEATURE = feature(
    name = "opt",
    enabled = False,
    flag_sets = [
        flag_set(
            actions = _CPP_ALL_COMPILE_ACTIONS + _C_ALL_COMPILE_ACTIONS,
            flag_groups = [
                flag_group(
                    flags = [
                        # Optimise for space
                        "-Os",
                        # Inline small functions if less instructions are likely to be executed
                        "-finline-small-functions",
                        "-flto",
                    ],
                ),
            ],
        ),
        flag_set(
            actions = _LD_ALL_ACTIONS,
            flag_groups = [
                flag_group(
                    flags = [
                        # Link time optimisation
                        "-flto",
                    ],
                ),
            ],
        ),
    ],
    provides = ["compilation_mode"],
)

_OUTPUT_FORMAT_FEATURE = feature(
    name = "output_format",
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
                        "--input-target=elf32-little",
                        "--output-target=binary",
                    ],
                ),
            ],
        ),
    ],
)

_MISC_FEATURE = feature(
    name = "misc",
    enabled = True,
    flag_sets = [
        flag_set(
            actions = _CPP_ALL_COMPILE_ACTIONS,
            flag_groups = [
                flag_group(
                    flags = [
                        "-std=c++2a",
                    ],
                ),
            ],
        ),
    ],
)

# Here for interface compatibility
_COVERAGE_FEATURE = feature(
    name = "coverage",
    enabled = False,
)

def GetGccCommonFeatures(include_paths, sysroot = "", architecture = "native", float_abi = "soft", endian = "little", fpu = "nofp"):
    return all_common_features(
        all_warnings = _ALL_WARNINGS_FEATURE,
        all_warnings_as_errors = _ALL_WARNINGS_AS_ERRORS_FEATURE,
        reproducible = _REPRODUCIBLE_FEATURE,
        includes = GccIncludeFeature(include_paths),
        symbol_garbage_collection = _SYMBOL_GARBAGE_COLLECTION,
        architecture = GccAchitectureFeature(architecture = architecture, fpu = fpu, float_abi = float_abi, endian = endian),
        dbg = _DEBUG_FEATURE,
        opt = _OPT_FEATURE,
        fastbuild = _FASTBUILD_FEATURE,
        output_format = _OUTPUT_FORMAT_FEATURE,
        misc = _MISC_FEATURE,
        coverage = _COVERAGE_FEATURE,
    )
