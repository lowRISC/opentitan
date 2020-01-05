def _fail_empty_element(list):
    for element in list:
        if not element:
            fail(msg = "empty element found in list")

def complexity_features(logical_line_limit, cyclomatic_complexity):
    """Constructs a struct of features for statically analysing the complexity of the code base 

    Args:
        logical_line_limit: This statical analysis feature should place a max limit of 200 lines of logical code and should meet JSF++ AV Rule 1.
        cyclomatic_complexity: This statical analysis feature should place a max limit of 20 for cyclomatic complexity and should meet JSF++ AV Rule 3.
    """
    _fail_empty_element([logical_line_limit, cyclomatic_complexity])
    return struct(
        logical_line_limit = logical_line_limit,
        cyclomatic_complexity = cyclomatic_complexity,
    )

def language_features(cpp_standard, no_special_characters, no_trigraphs, no_multi_byte_characters, uppercase_suffixes):
    """Constructs a struct of features for statically analysing the language features enabled

    Args:
        cpp_standard: This should enforce compliance with ISO/IEC 14882:2014 (C++14)
        no_special_characters: This shall enforce that only ascii style characters are used and shall also meet JSF++ AV Rule 9-10.
        no_trigraphs: No Trigraphs shall be used meeting JSF++ AV Rule 11
        no_multi_byte_characters: No multi-byte characters or wide-strings will be used meeting JSF++ AV Rule 13
        uppercase_suffixes: Uppercase literal suffixes should be used satisfying JSF++ AV Rule 14. e.g. use, (uint8_t i = 0U) instead of (uint8_t i = 0u)
    """
    _fail_empty_element([cpp_standard, no_special_characters, no_trigraphs, no_multi_byte_characters, uppercase_suffixes])
    return struct(
        cpp_standard = cpp_standard,
        no_special_characters = no_special_characters,
        no_trigraphs = no_trigraphs,
        no_multi_byte_characters = no_multi_byte_characters,
        uppercase_suffixes = uppercase_suffixes,
    )

def library_features(no_errno_indicator, no_offsetof, no_locale, no_setjmp, no_signal, no_std_io, no_atof_i_l, no_system_abort_error, no_time):
    """Constructs a struct forbidding usage of platform specific and error-prone standard libraries, according to the JSF++ standard

    Args:
        no_errno_indicator: Forbid usage of errno indicator enforcing JSF++ AV Rule 17.
        no_offsetof: Forbid usage of the macro offsetof in library stddef.h enforcing JSF++ Av Rule 18.
        no_locale: Forbid usage of the standard locale.h library enforcing JSF++ Av Rule 19
        no_setjmp: Forbid usage of setjmp longjmp enforcing JSF++ Av Rule 20
        no_signal: Forbid usage of signal.h library enforcing JSF++ Av Rule 21
        no_std_io: Forbid usage of stdio.h library enforcing JSF++ Av Rule 22
        no_atof_i_l: Forbid usage of atof, atoi, atol from stdlib.h enforcing JSF++ Av Rule 23
        no_system_abort_error: Forbid usage of functions, abort, exit, getenv, and system from stdlib.h enforcing JSF++ AV Rule 24
        no_time: Forbid usage of time.h enforcing JSF++ AV Rule 25
    """
    _fail_empty_element([no_errno_indicator, no_offsetof, no_locale, no_setjmp, no_signal, no_std_io, no_atof_i_l, no_system_abort_error, no_time])
    return struct(
        no_errno_indicator = no_errno_indicator,
        no_offsetof = no_offsetof,
        no_locale = no_locale,
        no_setjmp = no_setjmp,
        no_signal = no_signal,
        no_std_io = no_std_io,
        no_atof_i_l = no_atof_i_l,
        no_system_abort_error = no_system_abort_error,
        no_time = no_time,
    )

def declarations_definition_features(no_shadow):
    """Constructs a struct of features for statically analysing the declarations and definitions

        Args:
            no_shadow: Forbids identifiers in an inner scope shadowing an outer scope, enforcing JSF++ AV Rule 135.
    """
    _fail_empty_element([no_shadow])
    return struct(no_shadow = no_shadow)

def operator_features(sequence_side_effects):
    """A set of features for statically analysing the operators in code

    Args:
        sequence_side_effects: The right hand operation of a && or || operator shall not contain side effects enforcing JSF++ AV Rule 157
    """
    _fail_empty_element([equence_side_effects])
    return struct(sequence_side_effects = sequence_side_effects)

def flow_control_features(no_unreachable_code, no_labels, no_goto, no_break_except_switch, no_unterminated_else_if, no_unterminated_switch_case, default_on_non_complete_enum_switch, no_bool_switch, min_cases_switch, no_float_loop_iterator, for_loop_readibility, no_for_loop_iterator_body_modification):
    """Constructs a struct of features for statically analysing flow control in code

    Args:
        no_unreachable_code: No code shall be unreachable enforcing JSF++ AV Rule 186
        no_labels: No labels shall be used except in a switch statement enforcing JSF++ AV Rule 187
        no_goto: The goto command will not be used enforcing JSF++ AV Rule 188
        no_break_except_switch: The break keyword will not be used except in a switch statement enforcing JSF++ AV Rule 191
        no_unterminated_else_if: All else if statements should have a corresponding else enforcing JSF++ AV Ryle 192
        no_unterminated_switch_case: All non empty switch case shall have a corresponding break statement enforcing JSF++ AV Rule 193
        default_on_non_complete_enum_switch: All switch statements that do not test for every enumeration shall have a default value enforcing JSF++ AV RULE 195
        no_bool_switch: Bools shall not be used in a switch case statement enforcing JSF++ AV RULE 195
        min_cases_switch: Every switch statement shall have a minimum of 2 cases and potential default enforcing JSF++ AV Rule 196
        no_float_loop_iterator: No floats as loop counters enforcing JSF++ AV Rule 197
        for_loop_readibility: The initialisation expression of a for loop will be used for initialisation, the increment expression shall be used for iteration. This shall enforce JSF++ AV Rules 198-199
        no_for_loop_iterator_body_modification: The iteration variable in a for loop will not be modified in the body enforcing JSF++ AV Rule 201
    """
    _fail_empty_element([no_unreachable_code, no_labels, no_goto, no_break_except_switch, no_unterminated_else_if, no_unterminated_switch_case, default_on_non_complete_enum_switch, no_bool_switch, min_cases_switch, no_float_loop_iterator, for_loop_readibility, no_for_loop_iterator_body_modification])
    return struct(
        no_unreachable_code = no_unreachable_code,
        no_labels = no_labels,
        no_goto = no_goto,
        no_break_except_switch = no_break_except_switch,
        no_unterminated_else_if = no_unterminated_else_if,
        no_unterminated_switch_case = no_unterminated_switch_case,
        default_on_non_complete_enum_switch = default_on_non_complete_enum_switch,
        no_bool_switch = no_bool_switch,
        min_cases_switch = min_cases_switch,
        no_float_loop_iterator = no_float_loop_iterator,
        for_loop_readibility = for_loop_readibility,
        no_for_loop_iterator_body_modification = no_for_loop_iterator_body_modification,
    )

def expression_features(no_floating_equality, no_underflow_overflow):
    """ Constructs a struct of features that statically analyse expression features

    Args:
        no_floating_equality: Forbid floating point equality checks enforcing JSF++ AV Rule 202
        no_underflow_overflow: Check for underflow    """
    _fail_empty_element([no_floating_equality, no_underflow_overflow])
    struct(
        no_floating_equality = no_floating_equality,
        no_underflow_overflow = no_underflow_overflow,
    )

def memory_allocation_features(no_dynamic_allocation):
    """Constructs a struct of features that statically enforce memory allocation rules

    Args:
        no_dynamic_allocation: Forbids dynamic memory allocation enforcing JSF++ AV Rule 206
    """
    _fail_empty_element([no_dynamic_allocation])
    return struct(
        no_dynamic_allocation = no_dynamic_allocation,
    )

def pointer_arithmetic_features(no_pointer_arithmetic):
    """Constructs a struct of features that statically enforce the methods that pointers are handled

    Args:
        no_pointer_arithmetic: Forbids pointer arithmetic enforcing JSF++ AV Rule 215
    """
    _fail_empty_element([no_pointer_arithmetic])
    return struct(
        no_pointer_arithmetic = no_pointer_arithmetic,
    )

def safety_critcal_feature_set(
        complexity_features,
        language_features,
        library_features,
        declarations_definition_features,
        operator_features,
        flow_control_features,
        expression_features,
        memory_allocation_features,
        pointer_arithmetic_features):
    _fail_empty_element([
        complexity_features,
        language_features,
        library_features,
        declarations_definition_features,
        operator_features,
        flow_control_features,
        expression_features,
        memory_allocation_features,
        pointer_arithmetic_features,
    ])
    return struct(
        complexity_features = complexity_features,
        language_features = language_features,
        library_features = library_features,
        declarations_definition_features = declarations_definition_features,
        operator_features = operator_features,
        flow_control_features = flow_control_features,
        expression_features = expression_features,
        memory_allocation_features = memory_allocation_features,
        pointer_arithmetic_features = pointer_arithmetic_features,
    )

def get_compiler_specific_safety_critical_feature_set(compiler):
    return struct()
