# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import struct
import sys


def compare_json_data(
    actual_data: dict, expected_data: dict, ignored_keys: set
) -> bool:
    expected_comparable_keys = set(expected_data.keys()) - ignored_keys
    actual_comparable_keys = set(actual_data.keys()) - ignored_keys

    assert expected_comparable_keys == actual_comparable_keys

    for key in expected_comparable_keys:
        assert expected_data[key] == actual_data[key], (
            f"Found {actual_data[key]} but expected {expected_data[key]} under the key: {key}"
        )


def to_signed32(n_unsigned):
    n_unsigned = n_unsigned & 0xFFFFFFFF
    if n_unsigned >= 0x80000000:
        return n_unsigned - 0x100000000
    return n_unsigned


def bytes_to_words(byte_array):
    if not isinstance(byte_array, (bytes, bytearray)):
        raise TypeError("Input must be a bytes object or bytearray.")

    word_list = []
    for i in range(0, len(byte_array), 4):
        chunk = byte_array[i: i + 4]
        word = struct.unpack(">I", chunk)[0]
        word_list.append(word)
    return word_list


def words_to_bytes(dword_array):
    if not isinstance(dword_array, list):
        raise TypeError("Input must be a list of 32-bit integers.")

    byte_list = bytearray()
    for dword in dword_array:
        if not isinstance(dword, int) or not (0 <= dword <= 0xFFFFFFFF):
            raise ValueError(
                "Each element in the array must be a 32-bit integer (0 to 0xFFFFFFFF)."
            )
        byte_list.extend(struct.pack(">I", dword))
    return bytes(byte_list)


def array_to_int(data_array):
    result = 0
    for i, val in enumerate(data_array):
        result |= (val & 0xFFFFFFFF) << (i * 32)
    return result


def int_to_array(large_int):
    data_array = [0] * 8
    for i in range(8):
        data_array[i] = (large_int >> (i * 32)) & 0xFFFFFFFF
    return data_array


def pad_with_zeros(array, length):
    padded_arr = list(array)
    zeros_to_add = max(0, length - len(padded_arr))
    padded_arr.extend([0] * zeros_to_add)
    return padded_arr


def is_majority_zeros(array, total_length=None):
    if total_length is None:
        total_length = len(array)
    if total_length <= 0 or total_length > len(array):
        return False

    array = array[:total_length]
    zero_count = array.count(0)

    return zero_count > (total_length / 2)


def is_partial_collision(out1, out2, match_threshold_ratio=0.75, valid_len=None):
    """
    Checks if two outputs share a significant number of identical bytes.
    Useful for catching FI vulnerabilities where a skipped instruction
    causes a partial state collision rather than an exact match.
    """
    if out1 is None or out2 is None or len(out1) == 0:
        return False

    if valid_len is not None:
        out1 = out1[:valid_len]
        out2 = out2[:valid_len]

    if len(out1) != len(out2):
        return False

    matching_bytes = sum(1 for a, b in zip(out1, out2) if a == b)
    match_ratio = matching_bytes / len(out1)

    return match_ratio >= match_threshold_ratio


def add_test_selection_args(parser: argparse.ArgumentParser):
    """Adds test selection and listing arguments to the argument parser."""
    parser.add_argument(
        "--test",
        "--test_name",
        "--test-name",
        type=str,
        default=None,
        help="Name of the specific test method to run (e.g. test_p384_verify or p384_verify)",
    )
    parser.add_argument(
        "--list-tests",
        "--list",
        action="store_true",
        default=False,
        help="List all available tests in this suite and exit",
    )


def resolve_test_name(requested_name: str, available_tests: list):
    """Resolves a user-provided test name against a list of available test methods.

    Supports:
    - Exact test method name (e.g. 'test_p384_verify')
    - Short name without 'test_' prefix (e.g. 'p384_verify')
    - Qualified name (e.g. 'AsymCryptolibFiSim.test_p384_verify')
    - Case-insensitive matching
    - Unique substring matching

    Returns the resolved test method name, or None if no match or ambiguous.
    """
    if not requested_name:
        return None
    req = requested_name.strip()
    if "." in req:
        req = req.split(".")[-1]
    if req in available_tests:
        return req
    if f"test_{req}" in available_tests:
        return f"test_{req}"

    # Case-insensitive exact or short match
    exact_ci = [
        t
        for t in available_tests
        if t.lower() == req.lower()
        or (t.startswith("test_") and t[5:].lower() == req.lower())
    ]
    if len(exact_ci) == 1:
        return exact_ci[0]

    # Substring match
    sub = [t for t in available_tests if req.lower() in t.lower()]
    if len(sub) == 1:
        return sub[0]

    return None


def get_selected_test_argv(
    test_class,
    requested_name=None,
    config_args=None,
    list_tests=False,
):
    """Resolves unittest argv for running all tests or a single test.

    Args:
        test_class: The unittest.TestCase subclass.
        requested_name: Optional test name passed via --test flag.
        config_args: Optional list of remaining unparsed CLI args. If a positional
                     arg in config_args matches a test, it is consumed and removed.
        list_tests: Whether --list-tests was requested.

    Returns:
        List[str] suitable to pass as argv to unittest.main(argv=...).
    """
    # Collect available test methods preserving class definition order
    available_tests = [
        m
        for m in test_class.__dict__.keys()
        if m.startswith("test_") and callable(getattr(test_class, m))
    ]
    for m in dir(test_class):
        if (
            m.startswith("test_")
            and callable(getattr(test_class, m))
            and m not in available_tests
        ):
            available_tests.append(m)

    if list_tests:
        print(f"Available tests in {test_class.__name__}:")
        for t in available_tests:
            short_name = t[5:] if t.startswith("test_") else t
            print(f"  - {t}  (or {short_name})")
        sys.exit(0)

    # Check if a positional argument in config_args specifies a test
    if not requested_name and config_args is not None:
        for arg in list(config_args):
            if arg.startswith("-"):
                continue
            resolved = resolve_test_name(arg, available_tests)
            if resolved:
                requested_name = resolved
                config_args.remove(arg)
                break

    if requested_name:
        matched = resolve_test_name(requested_name, available_tests)
        if not matched:
            print(f"Error: Unknown or ambiguous test '{requested_name}'.")
            print(f"Available tests in {test_class.__name__}:")
            for t in available_tests:
                short_name = t[5:] if t.startswith("test_") else t
                print(f"  - {t}  (or {short_name})")
            sys.exit(1)

        print(
            f"[TEST SELECTION] Running single test: {test_class.__name__}.{matched}\n",
            flush=True,
        )
        return [sys.argv[0], f"{test_class.__name__}.{matched}"]

    return [sys.argv[0]]
