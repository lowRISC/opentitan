# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Module for LLVM coverage mapping encodings."""

import hashlib
import zlib

from pathlib import Path
from typing import List, Optional

from util.coverage.asm.parser import Statement


# https://llvm.org/docs/CoverageMappingFormat.html#id3
# Special counter expression for uncovered code.
COUNTER_UNCOVERED: int = 0 << 3


def encode_counter(counter: Optional[int]) -> int:
    if counter is None:
        return COUNTER_UNCOVERED
    else:
        # https://llvm.org/docs/CoverageMappingFormat.html#id3
        # Tag 1 for references to the profile instrumentation counter.
        return (counter << 2) | 0x01


def encode_leb128(value: int) -> bytes:
    """Encodes an integer into LEB128 format.

    Args:
        value: The integer to encode.

    Returns:
        The LEB128 encoded bytes.
    """
    result = bytearray()
    while True:
        byte: int = value & 0x7f
        value >>= 7
        if value:
            byte |= 0x80
        result.append(byte)
        if not value:
            break
    return bytes(result)


def encode_leb128_array(values: List[int]) -> bytes:
    """Encodes a list of integers into a sequence of LEB128 encoded bytes.

    Args:
        values: A list of integers to encode.

    Returns:
        The concatenated LEB128 encoded bytes for all values.
    """
    return b''.join(map(encode_leb128, values))


def encode_regions(statements: List[Statement]) -> bytes:
    """Encodes a list of statements into LLVM coverage mapping regions format.

    Args:
        statements: A list of `Statements`.

    Returns:
        The encoded regions as bytes.
    """
    # Filter out comments
    statements = [s for s in statements if not s.is_comment]

    # https://llvm.org/docs/CoverageMappingFormat.html#encoding
    out: List[int] = [
        1,  # num_file_id
        1,  # file_id_0
        0,  # num_counter_expr
        len(statements),
    ]
    last_lineno: int = 0
    for stmt in statements:
        assert stmt.lineno >= last_lineno
        text = stmt.raw.rstrip()
        num_lines = text.rstrip().count('\n')
        col_end = 1 if num_lines else stmt.colno
        col_end += len(text.rsplit('\n', 1)[-1])
        out.extend([
            encode_counter(stmt.block_counter),
            stmt.lineno - last_lineno,  # delta stmt start
            stmt.colno,  # column start
            num_lines,  # delta lines
            col_end,  # column end
        ])
        last_lineno = stmt.lineno

    return encode_leb128_array(out)


def encode_filepath(path: Path) -> bytes:
    """Encodes a file path into LLVM coverage mapping file path format.

    Args:
        path: The `Path` object representing the file.

    Returns:
        The encoded file path as bytes.
    """

    # The first element is the compilation directory, which Bazel sets to
    # `/proc/self/cwd`.
    paths: List[bytes] = [b'/proc/self/cwd', str(path).encode()]
    encoded = b''.join(encode_leb128(len(s)) + s for s in paths)
    compressed = zlib.compress(encoded, level=9)
    headers: List[int] = [2, len(encoded), len(compressed)]
    return encode_leb128_array(headers) + compressed


def encode_prf_names(names: List[str]) -> bytes:
    """Encodes a list of profile names into LLVM profile names format.

    Args:
        names: A list of strings representing profile names.

    Returns:
        The encoded profile names as bytes.
    """
    encoded = '\x01'.join(names).encode()
    compressed = zlib.compress(encoded, level=9)
    headers: List[int] = [len(encoded), len(compressed)]
    return encode_leb128_array(headers) + compressed


def encode_oct(inp: bytes) -> str:
    """Encodes bytes into an octal string representation suitable for assembly.

    Args:
        inp: The input bytes.

    Returns:
        A string with octal escapes, enclosed in double quotes.
    """
    return '"' + ''.join(f'\\{b:03o}' for b in inp) + '"'


def get_hash(input_bytes: bytes) -> int:
    """Calculates the MD5 hash of input bytes and returns the first 8 bytes as an integer.

    Args:
        input_bytes: The bytes to hash.

    Returns:
        An integer representing the first 8 bytes of the MD5 hash (little-endian).
    """
    hash_digest = hashlib.md5(input_bytes).digest()
    return int.from_bytes(hash_digest[:8], 'little')
