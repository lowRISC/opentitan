# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Shared subfunctions.
"""
import logging as log
import random
import textwrap
from math import ceil, log2


def wrapped_docstring():
    '''Return a text-wrapped version of the module docstring'''
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


def check_bool(x):
    """check_bool checks if input 'x' either a bool or
       one of the following strings: ["true", "false"]
        It returns value as Bool type.
    """
    if isinstance(x, bool):
        return x
    if not x.lower() in ["true", "false"]:
        raise RuntimeError("{} is not a boolean value.".format(x))
    else:
        return (x.lower() == "true")


def check_int(x):
    """check_int checks if input 'x' is decimal integer.
        It returns value as an int type.
    """
    if isinstance(x, int):
        return x
    if not x.isdecimal():
        raise RuntimeError("{} is not a decimal number".format(x))
    return int(x)


def as_snake_case_prefix(name):
    """ Convert PascalCase name into snake_case name"""
    outname = ""
    for c in name:
        if c.isupper() and len(outname) > 0:
            outname += '_'
        outname += c.lower()
    return outname + ('_' if name else '')


def get_random_data_hex_literal(width):
    """ Fetch 'width' random bits and return them as hex literal"""
    width = int(width)
    literal_str = hex(random.getrandbits(width))
    literal_str = str(width) + "'h" + literal_str[2:]
    return literal_str


def blockify(s, size, limit):
    """ Make sure the output does not exceed a certain size per line"""

    str_idx = 2
    remain = size % (limit * 4)
    numbits = remain if remain else limit * 4
    s_list = []

    remain = size
    while remain > 0:
        s_incr = int(numbits / 4)
        s_list.append("{}'h{}".format(numbits, s[str_idx:str_idx + s_incr]))
        str_idx += s_incr
        remain -= numbits
        numbits = limit * 4

    return (",\n  ".join(s_list))


def get_random_perm_hex_literal(numel):
    """ Compute a random permutation of 'numel' elements and
    return as packed hex literal"""
    num_elements = int(numel)
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


def get_hd(word1, word2):
    '''Calculate Hamming distance between two words.'''
    if len(word1) != len(word2):
        raise RuntimeError('Words are not of equal size')
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


def random_or_hexvalue(dict_obj, key, num_bits):
    '''Convert hex value at "key" to an integer or draw a random number.'''

    # Initialize to default if this key does not exist.
    dict_obj.setdefault(key, '0x0')

    # Generate a random number of requested size in this case.
    if dict_obj[key] == '<random>':
        dict_obj[key] = random.getrandbits(num_bits)
    # Otherwise attempt to convert this number to an int.
    # Check that the range is correct.
    else:
        try:
            dict_obj[key] = int(dict_obj[key], 16)
            if dict_obj[key] >= 2**num_bits:
                raise RuntimeError(
                    'Value "{}" is out of range.'
                    .format(dict_obj[key]))
        except ValueError:
            raise RuntimeError(
                'Invalid value "{}". Must be hex or "<random>".'
                .format(dict_obj[key]))
