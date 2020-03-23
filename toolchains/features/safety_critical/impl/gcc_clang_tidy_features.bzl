load(
    "@bazel_tools//tools/cpp:cc_toolchain_config_lib.bzl",
    "feature",
    "flag_group",
    "flag_set",
)
load("@bazel_tools//tools/build_defs/cc:action_names.bzl", "ACTION_NAMES")
load("//toolchains/features/safety_critical:types.bzl", "language_features")

_C_ALL_COMPILE_ACTIONS = [
    ACTION_NAMES.assemble,
    ACTION_NAMES.c_compile,
]
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
] + _C_ALL_COMPILE_ACTIONS

_LD_ALL_ACTIONS = [
    ACTION_NAMES.cpp_link_executable,
]

def _complexity_features():
    """Implements the static analysis requirements for code complexity

    Returns:
        complexity_features: A struct of implemented static analysis features for safety crticial code
    """
    logical_line_limit = feature(
        name = "logical_line_limit",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    # TODO:Implement this
                ])],
            ),
        ],
    )
    cyclomatic_complexity = feature(
        name = "cyclomatic_complexity",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    # TODO:Implement this
                ])],
            ),
        ],
    )
    return complexity_features(logical_line_limit, cyclomatic_complexity)

def _language_features():
    """Returns a struct of features that implement the safety critical toolchain interface

    Returns:
        language_features: A struct containing a set of features for safety critical language constraints
    """
    cpp_standard = feature(
        name = "cpp_standard",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = ["-std=c++14"])],
            ),
        ],
    )
    no_special_characters = feature(
        name = "no_special_characters",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    "-Wnormalized=nfc",
                    "-Werror=normalized",
                ])],
            ),
        ],
    )
    no_trigraphs = feature(
        name = "no_trigraphs",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    "-Wtrigraphs",
                    "-Werror=trigraphs",
                ])],
            ),
        ],
    )
    no_multi_byte_characters = feature(
        name = "no_multi_byte_characters",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    # Defualts an error in gcc
                ])],
            ),
        ],
    )

    uppercase_suffixes = feature(
        name = "uppercase_suffixes",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    #TODO: Implement this
                ])],
            ),
        ],
    )

    return language_features(
        cpp_standard,
        no_special_characters,
        no_trigraphs,
        no_multi_byte_characters,
        uppercase_suffixes,
    )

def _library_features():
    """ Returns a struct of features to meet safety critical constraints on library usage for JSF++ 

    Returns:
        library_features: A set of features that enforce blacklisted libraries and functions
    """

    no_errno_indicator = feature(
        name = "no_errno_indicator",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    "-include toolchains/features/safety_critical/injected_include/forbid_errno.h",
                ])],
            ),
        ],
    )
    no_offsetof = feature(
        name = "no_offsetof",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    "-include toolchains/features/safety_critical/injected_include/forbid_offsetof.h",
                ])],
            ),
        ],
    )
    no_locale = feature(
        name = "no_locale",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    "-include toolchains/features/safety_critical/injected_include/forbid_locale.h",
                ])],
            ),
        ],
    )
    no_setjmp = feature(
        name = "no_setjmp",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    "-include toolchains/features/safety_critical/injected_include/forbid_offsetof.h",
                ])],
            ),
        ],
    )
    no_signal = feature(
        name = "no_signal",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    "-include toolchains/features/safety_critical/injected_include/forbid_signal.h",
                ])],
            ),
        ],
    )
    no_std_io = feature(
        name = "no_std_io",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    "-include toolchains/features/safety_critical/injected_include/forbid_stdio.h",
                ])],
            ),
        ],
    )
    no_atof_i_l = feature(
        name = "no_atof_i_l",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    "-include toolchains/features/safety_critical/injected_include/forbid_atof_i_l.h",
                ])],
            ),
        ],
    )
    no_system_abort_error = feature(
        name = "no_system_abort_error",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    "-include toolchains/features/safety_critical/injected_include/forbid_no_system_abort_error.h",
                ])],
            ),
        ],
    )
    no_time = feature(
        name = "no_time",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    "-include toolchains/features/safety_critical/injected_include/forbid_time.h",
                ])],
            ),
        ],
    )
    return library_features(
        no_errno_indicator,
        no_offsetof,
        no_locale,
        no_setjmp,
        no_signal,
        no_std_io,
        no_atof_i_l,
        no_system_abort_error,
        no_time,
    )

def _declarations_definition_features():
    """Returns a set of implemented features of enforcing safety critical constraints for declarations and definitions

    Returns:
        declarations_definition_features: A struct of features
    """
    no_shadow = feature(
        name = "no_shadow",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    "-Wshadow",
                    "-Werror=shadow",
                ])],
            ),
        ],
    )
    return declarations_definition_features(no_shadow)

def _operator_features():
    """Returns a struct of features for enforcing safety critical constraints for operators

    Returns:
        operator_features: Struct of features for operator analysis
    """
    sequence_side_effects = feature(
        name = "sequence_side_effects",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    "-Wsequence-point",
                    "-Werror=sequence-point",
                ])],
            ),
        ],
    )
    signed_unsigned_arithmetic_comparison = feature(
        name = "signed_unsigned_arithmetic_comparison",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    "-Wsign-compare",
                    "-Wconversion",
                    "-Werror=sign-compare,conversion",
                ])],
            ),
        ],
    )
    return operator_features(sequence_side_effects, signed_unsigned_arithmetic_comparison)

def _flow_control_features():
    """Returns a struct of features for enforcing safety critical constrains on flow control

    Returns:
        flow_control_features: A struct of features for enforcing safety critical constraints on flow control
    """
    no_unreachable_code = feature(
        name = "no_unreachable_code",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    "-ffunction-sections",
                    "-fdata-sections",
                    "-Wtype-limits",
                ])],
            ),
            flag_set(
                actions = _LD_ALL_ACTIONS,
                flag_groups = [flag_group(
                    "-Wl,--gc-sections",
                )],
            ),
        ],
    )
    no_labels = feature(
        name = "no_labels",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    "-Wunused-label",
                    "-Werror=unused-label",
                ])],
            ),
        ],
    )
    no_goto = feature(
        name = "no_goto",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    "-include toolchains/features/safety_critical/injected_include/forbid_goto_continue.h",
                ])],
            ),
        ],
    )
    no_break_except_switch = feature(
        name = "no_break_except_switch",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    # TODO
                ])],
            ),
        ],
    )
    no_unterminated_else_if = feature(
        name = "no_unterminated_else_if",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    # TODO
                ])],
            ),
        ],
    )
    no_unterminated_switch_case = feature(
        name = "no_unterminated_switch_case",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    "-Wimplicit-fallthrough",
                    "-Werror=implicit-fallthrough",
                ])],
            ),
        ],
    )
    default_on_non_complete_enum_switch = feature(
        name = "default_on_non_complete_enum_switch",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    "-Wswitch",
                    "-Werror=switch",
                ])],
            ),
        ],
    )
    no_bool_switch = feature(
        name = "no_bool_switch",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    "-Wswitch-bool",
                    "-Werror=switch-bool",
                ])],
            ),
        ],
    )
    min_cases_switch = feature(
        name = "min_cases_switch",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    # TODO: Implement this
                ])],
            ),
        ],
    )
    no_float_loop_iterator = feature(
        name = "no_float_loop_iterator",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    # TODO: Implement this
                ])],
            ),
        ],
    )
    for_loop_readibility = feature(
        name = "for_loop_readibility",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    # TODO: Implement this
                ])],
            ),
        ],
    )
    no_for_loop_iterator_body_modification = feature(
        name = "no_for_loop_iterator_body_modification",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    # TODO: Implement this
                ])],
            ),
        ],
    )

    return flow_control_features(no_unreachable_code, no_labels, no_goto, no_break_except_switch, no_unterminated_else_if, no_unterminated_switch_case, default_on_non_complete_enum_switch, no_bool_switch, min_cases_switch, no_float_loop_iterator, for_loop_readibility, no_for_loop_iterator_body_modification)

def _expression_features():
    """Returns a struct of features for safety critical constraints on expressions

    Returns:
        expression_features: a struct of features implementing
    """
    no_floating_equality = feature(
        name = "no_float_equality",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    "-Wfloat-equal",
                    "-Werror=float-equal",
                ])],
            ),
        ],
    )
    no_underflow_overflow = feature(
        name = "no_underflow_overflow",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    "-Wstrict-overflow=4",
                    "-Werror=strict-overflow",
                ])],
            ),
        ],
    )
    return expression_features(no_floating_equality, no_underflow_overflow)

def _memory_allocation_features():
    """Returns a struct of memory allocation features implenting safety critical constraints

    Returns:
        memory_allocation_features: features forbidding the usage of dynamic memory allocation
    """
    no_dynamic_allocation = feature(
        name = "no_dynamic_allocation",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    "-include toolchains/features/safety_critical/injected_include/forbid_dynamic_memory_allocation.h",
                ])],
            ),
        ],
    )
    return memory_allocation_features(no_dynamic_allocation)

def _pointer_arithmetic_features():
    """Implements the safety critical features for pointer arithmetic

    Returns:
        pointer_arithmetic_features: features limiting the use of pointer arithmetic
    """
    no_pointer_arithmetic = feature(
        name = "no_pointer_arithmetic",
        enabled = False,
        flag_sets = [
            flag_set(
                actions = _CPP_ALL_COMPILE_ACTIONS,
                flag_groups = [flag_group(flags = [
                    "-Wpointer-arith",
                    "-Werror=pointer-arith",
                ])],
            ),
        ],
    )
    return pointer_arithmetic_features(no_pointer_arithmetic)

def gcc_clang_safety_critical_injected_headers():
    """Returns the target filegroups containing injected headers required as part of the toolchain

    Returns:
        target: filegroup target containing all headers to be injected into the toolchain
    """
    return "//toolchains/features/safety_critical/injected_include:forbid_std_functionality"

def gcc_clang_safety_crticial_feature_set():
    """Implements a safety crticial feature set using clang and gcc

    Returns:
        safety_critical_feature_set: A struct containing an implementation of the safety critical requirements
    """
    return safety_crticial_feature_set(
        _complexity_features(),
        _language_features(),
        _library_features(),
        _declarations_definition_features(),
        _operator_features(),
        _flow_control_features(),
        _expression_features(),
        _memory_allocation_features(),
        _pointer_arithmetic_features(),
    )
