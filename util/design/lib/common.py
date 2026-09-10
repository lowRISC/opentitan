# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r'''Common utilities used by various util/design scripts.'''
import os
import random
import re
import sys
import textwrap
from math import ceil, log2
from pathlib import Path

sys.path.append(os.path.join(os.path.dirname(__file__), '../../'))

from topgen.secure_prng import SecurePrng  # noqa : E402


def wrapped_docstring():
    '''Return a text-wrapped version of the module docstring.'''
    paras = []
    para = []
    for line in __doc__.strip().split('\n'):
        line = line.strip()
        if not line:
            if para:
                paras.append('\n'.join(para))
                para = []
        else:
            para.append(line)
    if para:
        paras.append('\n'.join(para))

    return '\n\n'.join(textwrap.fill(p) for p in paras)


def path_to_include_guard(filepath: str) -> str:
    '''Generates C header include guard from file path.

    Args:
        filepath: Input file path.
    Returns:
        String repesenting include guard encoded format.
    '''
    header = Path(filepath)
    dir = re.sub(r'[^\w]', '_', str(header.parent)).upper()
    stem = re.sub(r'[^\w]', '_', str(header.stem)).upper()
    return f'OPENTITAN_{dir}_{stem}_H_'


def check_bool(x):
    '''check_bool checks if input 'x' either a bool or one of the following
    strings: ["true", "false"]

    Returns:
        Value 'x' as Bool type.
    '''
    if isinstance(x, bool):
        return x
    if x.lower() not in ["true", "false"]:
        raise RuntimeError("{} is not a boolean value.".format(x))
    else:
        return (x.lower() == "true")


def check_int(x):
    '''check_int checks if input 'x' is decimal integer.

    Returns:
        Value 'x' as an int type.
    '''
    if isinstance(x, int):
        return x
    if not x.isdecimal():
        raise RuntimeError("{} is not a decimal number.".format(x))
    return int(x)


def as_snake_case_prefix(name):
    '''Convert PascalCase name into snake_case name.'''
    outname = ""
    for c in name:
        if c.isupper() and len(outname) > 0:
            outname += '_'
        outname += c.lower()
    return outname + ('_' if name else '')


def get_random_data_hex_literal(width):
    '''Fetch 'width' random bits and return them as hex literal.'''
    width = int(width)
    literal_str = hex(random.getrandbits(width))
    return blockify(literal_str, width, 64)


def _group_digits(digits: str, n: int) -> str:
    '''Right-align digits into groups of at most n characters, joined by "_".

    The leftmost group may be shorter than n if len(digits) isn't a multiple of n.
    '''
    first = len(digits) % n or n
    groups = [digits[:first]] + [digits[i:i + n] for i in range(first, len(digits), n)]
    return '_'.join(groups)


def blockify(s: str, size: int, limit: int) -> str:
    '''Split a hex constant in a string into multiple 32-bit hex literals.

     The input is expected to be in "C-style format", matching the regex
     0x[0-9a-f]+. The output isn't exactly a SystemVerilog expression: it is a
     string that can be placed inside "{}" to give the format of a packed
     vector.

     This expression is zero-extended, split into 32-bit chunks (for
     readability) and then separated by newlines (to avoid long lines in the
     generated source code).

     For example, an input constant (72 bits) of

       0x123456789abcdef01

     with limit = 16 would be returned as the following string:

       "8'h01,\n  64'h23456789_abcdef01"

    Arguments:

      s:      A string that contains a hexadecimal number (starting '0x')
      size:   The number of bits used to represent the constant
      limit:  The maximum number of nibbles to represent per line
    '''

    # Check that s really is in the expected format
    if not re.match(r'0x[0-9a-fA-F]+$', s):
        raise ValueError('s is not a hex string starting with 0x')

    # Check that size is a positive number.
    if size <= 0:
        msg = f'Unsupported size in bits: {size}. Should be positive.'
        raise ValueError(msg)

    # Check that the per-line nibble limit is positive.
    if limit <= 0:
        msg = f'Invalid limit: {limit}. Should be positive.'
        raise ValueError(msg)

    # How many digits should be used in the resulting literal after padding?
    num_digits = (size + 3) // 4

    # Strip the 0x prefix and left-pad to the right length with zeros
    digits = s[2:].zfill(num_digits)

    # The first line may be shorter than 'limit' digits, if 'size' isn't a whole multiple
    # of the per-line width.
    first_bits = size % (limit * 4) or limit * 4
    first_len = (first_bits + 3) // 4  # ceil(first_bits / 4)
    num_full_lines = (num_digits - first_len) // limit

    first_chunk, rest = digits[:first_len], digits[first_len:]
    s_list = ["{}'h{}".format(first_bits, _group_digits(first_chunk, 8))]

    # Every line after that is exactly 'limit' digits.
    for _ in range(num_full_lines):
        chunk, rest = rest[:limit], rest[limit:]
        s_list.append("{}'h{}".format(limit * 4, _group_digits(chunk, 8)))

    return (",\n  ".join(s_list))


def get_random_perm_hex_literal(numel):
    '''Compute a random permutation of 'numel' elements and
    return as packed hex literal.'''
    num_elements = int(numel)
    if num_elements < 2:
        msg = (f"Can't form a meaningful permutation with only "
               f"{num_elements} elements.")
        raise ValueError(msg)
    width = int(ceil(log2(num_elements)))
    idx = [x for x in range(num_elements)]
    random.shuffle(idx)
    literal_str = ""
    for k in idx:
        literal_str += format(k, '0' + str(width) + 'b')
    # convert to hex for space efficiency
    literal_str = hex(int(literal_str, 2))
    return blockify(literal_str, width * numel, 64)


def hist_to_bars(hist, m):
    '''Convert histogramm list into ASCII bar plot'''
    bars = []
    for i, j in enumerate(hist):
        bar_prefix = "{:2}: ".format(i)
        spaces = len(str(m)) - len(bar_prefix)
        hist_bar = bar_prefix + (" " * spaces)
        for k in range(j * 20 // max(hist)):
            hist_bar += "|"
        hist_bar += " ({:.2f}%)".format(100.0 * j / sum(hist)) if j else "--"
        bars += [hist_bar]
    return bars


def get_hd(word1: str, word2: str) -> int:
    '''Calculate Hamming distance between two words.'''
    if len(word1) != len(word2):
        raise RuntimeError('Words are not of equal size')
    # Python's int(n, 2) function will accept both strings of bits and
    # 0b-prefixed strings. This can lead to edge cases such as get_hd('1001',
    # '0b01'). We forbid the usage of "0b" with this function.
    if '0b' in word1 or '0b' in word2:
        raise ValueError('Words should not contain the "0b" prefix')
    return bin(int(word1, 2) ^ int(word2, 2)).count('1')


def hd_histogram(existing_words):
    '''Build Hamming distance histogram'''
    minimum_hd = len(existing_words[0])
    maximum_hd = 0
    minimum_hw = len(existing_words[0])
    maximum_hw = 0
    hist = [0] * (len(existing_words[0]) + 1)
    for i, j in enumerate(existing_words):
        minimum_hw = min(j.count('1'), minimum_hw)
        maximum_hw = max(j.count('1'), maximum_hw)
        if i < len(existing_words) - 1:
            for k in existing_words[i + 1:]:
                dist = get_hd(j, k)
                hist[dist] += 1
                minimum_hd = min(dist, minimum_hd)
                maximum_hd = max(dist, maximum_hd)

    stats = {}
    stats["hist"] = hist
    stats["bars"] = hist_to_bars(hist, len(existing_words))
    stats["min_hd"] = minimum_hd
    stats["max_hd"] = maximum_hd
    stats["min_hw"] = minimum_hw
    stats["max_hw"] = maximum_hw
    return stats


def is_valid_codeword(config, codeword):
    '''Checks whether the bitstring is a valid ECC codeword.'''

    data_width = config['secded']['data_width']
    ecc_width = config['secded']['ecc_width']
    if len(codeword) != (data_width + ecc_width):
        raise RuntimeError("Invalid codeword length {}".format(len(codeword)))

    # Build syndrome and check whether it is zero.
    syndrome = [0 for k in range(ecc_width)]

    # The bitstring must be formatted as "data bits[N-1:0]" + "ecc bits[M-1:0]".
    for j, fanin in enumerate(config['secded']['ecc_matrix']):
        syndrome[j] = int(codeword[ecc_width - 1 - j])
        for k in fanin:
            syndrome[j] ^= int(codeword[ecc_width + data_width - 1 - k])

    return sum(syndrome) == 0


def ecc_encode(config, dataword):
    '''Calculate and prepend ECC bits.'''
    if len(dataword) != config['secded']['data_width']:
        raise RuntimeError("Invalid codeword length {}".format(len(dataword)))

    # Note that certain codes like the Hamming code refer to previously
    # calculated parity bits. Hence, we incrementally build the codeword
    # and extend it such that previously calculated bits can be referenced.
    codeword = dataword
    for j, fanin in enumerate(config['secded']['ecc_matrix']):
        bit = 0
        for k in fanin:
            bit ^= int(codeword[config['secded']['data_width'] + j - 1 - k])
        codeword = str(bit) + codeword

    return codeword


def scatter_bits(mask, bits):
    '''Scatter the bits into unset positions of mask.'''
    j = 0
    scatterword = ''
    for b in mask:
        if b == '1':
            scatterword += '1'
        else:
            scatterword += bits[j]
            j += 1

    return scatterword


def validate_data_perm_option(word_bit_length, data_perm):
    '''Validate OTP data permutation option by checking for bijectivity.'''
    if len(data_perm) != word_bit_length:
        raise RuntimeError(
            'Data permutation "{}" is not bijective, since '
            'it does not have the same length ({}) as the data.'.format(
                data_perm, word_bit_length))
    for k in data_perm:
        if k >= word_bit_length:
            raise RuntimeError('Data permutation "{}" is not bijective, '
                               'since the index {} is out of bounds.'.format(
                                   data_perm, k))
    if len(set(data_perm)) != word_bit_length:
        raise RuntimeError(
            'Data permutation "{}" is not bijective, '
            'since it contains duplicated indices.'.format(data_perm))


def inverse_permute_bits(bit_str, permutation):
    '''Un-permute the bits in a bitstring (inverse of `permute_bits`).'''
    bit_str_len = len(bit_str)
    assert bit_str_len == len(permutation)
    bit_vector = ["0"] * bit_str_len
    for i, perm_idx in enumerate(permutation):
        bit_vector[bit_str_len - perm_idx - 1] = bit_str[bit_str_len - i - 1]
    return ''.join(bit_vector)


def permute_bits(bit_str, permutation):
    '''Permute the bits in a bitstring.'''
    bitlen = len(bit_str)
    assert bitlen == len(permutation)
    permword = ''
    for k in permutation:
        permword = bit_str[bitlen - k - 1] + permword
    return permword


def _parse_hex(value):
    '''Parse a hex value into an integer.

    Args:
      value: list[str] or str:
        If a `list[str]`, parse each element as a 32-bit integer.
        If a `str`, parse as a single hex string.
    Returns:
        int
    '''
    if isinstance(value, list):
        result = 0
        for (i, v) in enumerate(value):
            result |= int(v, 16) << (i * 32)
        return result
    else:
        value = value.translate(str.maketrans('', '', ' \r\n\t'))
        return int(value, 16)


def random_or_hexvalue(prng: SecurePrng, dict_obj: dict, key: str, num_bits: int) -> None:
    '''Convert hex value at "key" to an integer or draw a random number.'''

    # Initialize to default if this key does not exist.
    dict_obj.setdefault(key, '0x0')

    # Generate a random number of requested size in this case.
    if dict_obj[key] == '<random>':
        dict_obj[key] = prng.getrandbits(num_bits)
    # Otherwise attempt to convert this number to an int.
    # Check that the range is correct.
    else:
        try:
            dict_obj[key] = _parse_hex(dict_obj[key])
            if dict_obj[key] >= 2**num_bits:
                raise RuntimeError('Value "{}" is out of range.'.format(
                    dict_obj[key]))
        except ValueError:
            raise RuntimeError(
                'Invalid value "{}". Must be hex or "<random>".'.format(
                    dict_obj[key]))


def vmem_permutation_string(data_perm):
    '''Check VMEM permutation format and expand the ranges.'''

    if not isinstance(data_perm, str):
        raise TypeError()

    if not data_perm:
        return ""

    # Check the format first.
    pattern = r"^((?:\[[0-9]+:[0-9]+\])+(?:,\[[0-9]+:[0-9]+\])*)"
    match = re.fullmatch(pattern, data_perm)
    if match is None:
        raise ValueError()
    # Expand the ranges.
    expanded_perm = []
    groups = match.groups()
    for group in groups[0].split(","):
        k1, k0 = [int(x) for x in group[1:-1].split(":")]
        if k1 > k0:
            expanded_perm = list(range(k0, k1 + 1)) + expanded_perm
        else:
            expanded_perm = list(range(k0, k1 - 1, -1)) + expanded_perm

    return expanded_perm
