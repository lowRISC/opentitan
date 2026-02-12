# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import struct


def compare_json_data(
    actual_data: dict, expected_data: dict, ignored_keys: set
) -> bool:
    expected_comparable_keys = set(expected_data.keys()) - ignored_keys
    actual_comparable_keys = set(actual_data.keys()) - ignored_keys

    assert expected_comparable_keys == actual_comparable_keys

    for key in expected_comparable_keys:
        assert expected_data[key] == actual_data[key], \
            f"Found {actual_data[key]} but expected {expected_data[key]} under the key: {key}"


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
