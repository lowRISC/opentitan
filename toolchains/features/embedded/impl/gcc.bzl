load(
    "@bazel_tools//tools/cpp:cc_toolchain_config_lib.bzl",
    "feature",
    "flag_group",
    "flag_set",
)
load("//toolchains/features/embedded:type.bzl", "all_embedded_features")
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

# Run time type information is enabled by default
_RUNTIME_TYPE_INFORMATION_FEATURE = feature(
    name = "runtime_type_information",
    enabled = True,
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

def _GetSysSpecFeature(architecture, float_abi, endian, fpu):
    # FIXME(cfrantz): elevate this to device specs?
    if architecture == "riscv32":
        compiler_flags = [
            "-march=rv32imc",
            "-mabi=ilp32",
            "-mcmodel=medany",
        ]
    else:
        compiler_flags = [
            "-mabi=aapcs",
            "-mthumb",
            "-specs=nano.specs",
            "-specs=nosys.specs",
        ]

    return feature(
        name = "sys_spec",
        enabled = True,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [
                    flag_group(
                        flags = compiler_flags,
                    ),
                ],
            ),
            flag_set(
                actions = _LD_ALL_ACTIONS,
                flag_groups = [
                    flag_group(
                        flags = [
                            # Disable Exceptions
                            # FIXME(cfrantz): elevate this to device specs?
                            #"-lc",
                            "-lnosys",
                        ],
                    ),
                ],
            ),
        ],
    )

_CC_CONSTRUCTOR_DESTRUCTOR_FEATURE = feature(
    name = "cc_constructor_destructor",
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
                        # FIXME(cfrantz): elevate this to device specs?
                        #"-fstack-protector-strong",
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
                        # Disable threadsafe statics
                        "-fno-threadsafe-statics",
                    ],
                ),
            ],
        ),
    ],
)

def GetGccEmbeddedFeatures(architecture, float_abi, endian, fpu):
    """ GetGccEmbeddedFeatures returns features relevant to embedded developement
    """
    return all_embedded_features(
        exceptions = _EXCEPTIONS_FEATURE,
        runtime_type_information = _RUNTIME_TYPE_INFORMATION_FEATURE,
        sys_spec = _GetSysSpecFeature(architecture, float_abi, endian, fpu),
        cc_constructor_destructor = _CC_CONSTRUCTOR_DESTRUCTOR_FEATURE,
    )
