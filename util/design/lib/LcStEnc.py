# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Contains life cycle state encoding class which is
used to generate new life cycle encodings.
"""
import itertools
import logging as log
from collections import OrderedDict

from Crypto.Hash import cSHAKE128
from design.lib.common import (check_int, ecc_encode, get_hd, hd_histogram,
                               is_valid_codeword, random_or_hexvalue, scatter_bits)
from topgen.secure_prng import SecurePrngFactory

# This seed is used to generate the non-secure life cycle state encodings.
# Use a common seed for all tops and selected seed types.
lc_ctrl_non_secure_seed = 0x517ecf3166f4323433e4ad760d6f8e2fdf45244002ce54be8ca3cb7747c21bb


# Top level of a multi-level state word: all data bits set.
ONE = 'ONE'

# State types and permissible format for entries
# The format is index dependent, e.g. ['0', 'A1', 'B1'] for index 1
LC_STATE_TYPES = {
    # 0 -> A -> B -> K -> L -> ONE. Every step only sets bits (data and ECC),
    # see _get_new_state_word_chain().
    'lc_state': ['0', 'A{}', 'B{}', 'K{}', 'L{}', ONE],
    'lc_cnt': ['0', 'C{}', 'D{}'],
    'soc_dbg_state': ['0', 'E{}', 'F{}'],
    'ownership_state': ['0', 'G{}', 'H{}'],
    'auth_state': ['0', 'I{}', 'J{}']
}

# Types whose state table is checked by _check_state_order().
ORDER_CHECKED_TYPES = ['lc_state']


def _is_chain_type(typ):
    '''Multi-level types use nested codeword chains below the all-ones word.'''
    return LC_STATE_TYPES[typ][-1] == ONE


def _is_incremental_codeword(word1, word2):
    '''Test whether word2 is incremental wrt word1.'''
    if len(word1) != len(word2):
        raise RuntimeError('Words are not of equal size')

    _word1 = int(word1, 2)
    _word2 = int(word2, 2)

    # This basically checks that the second word does not
    # clear any bits that are set to 1 in the first word.
    return ((_word1 & _word2) == _word1)


def _get_incremental_codewords(config, base_ecc, existing_words):
    '''Get all possible incremental codewords fulfilling the constraints.'''

    base_data = base_ecc[config['secded']['ecc_width']:]

    # We only need to spin through data bits that have not been set yet.
    # Hence, we first count how many bits are zero (and hence still
    # modifiable). Then, we enumerate all possible combinations and scatter
    # the bits of the enumerated values into the correct bit positions using
    # the scatter_bits() function.
    incr_cands = []
    free_bits = base_data.count('0')
    for k in range(1, 2**free_bits):
        # Get incremental dataword by scattering the enumeration bits
        # into the zero bit positions in base_data.
        incr_cand = scatter_bits(base_data,
                                 format(k, '0' + str(free_bits) + 'b'))
        incr_cand_ecc = ecc_encode(config, incr_cand)

        # Dataword is correct by construction, but we need to check whether
        # the ECC bits are incremental.
        if _is_incremental_codeword(base_ecc, incr_cand_ecc):
            # Check whether the candidate fulfills the maximum
            # Hamming weight constraint.
            if incr_cand_ecc.count('1') <= config['max_hw']:
                # Check Hamming distance wrt all existing words.
                for w in existing_words + [base_ecc]:
                    if get_hd(incr_cand_ecc, w) < config['min_hd']:
                        break
                else:
                    incr_cands.append(incr_cand_ecc)

    return incr_cands


def _get_new_state_word_pair(config, existing_words):
    '''Randomly generate a new incrementally writable word pair'''
    prng = SecurePrngFactory.get("lc_non_secure")
    while 1:
        # Draw a random number and check whether it is unique and whether
        # the Hamming weight is in range.
        width = config['secded']['data_width']
        ecc_width = config['secded']['ecc_width']
        base = prng.getrandbits(width)
        base = format(base, '0' + str(width) + 'b')
        base_cand_ecc = ecc_encode(config, base)
        # disallow all-zero and all-one states
        pop_cnt = base_cand_ecc.count('1')
        if pop_cnt >= config['min_hw'] and pop_cnt <= config['max_hw']:

            # Check Hamming distance wrt all existing words
            for w in existing_words:
                if get_hd(base_cand_ecc, w) < config['min_hd']:
                    break
            else:
                # Get encoded incremental candidates.
                incr_cands_ecc = _get_incremental_codewords(
                    config, base_cand_ecc, existing_words)
                # there are valid candidates, draw one at random.
                # otherwise we just start over.
                if incr_cands_ecc:
                    incr_cand_ecc = prng.choice(incr_cands_ecc)
                    log.info('word {}: {}|{} -> {}|{}'.format(
                        int(len(existing_words) / 2),
                        base_cand_ecc[ecc_width:], base_cand_ecc[0:ecc_width],
                        incr_cand_ecc[ecc_width:], incr_cand_ecc[0:ecc_width]))
                    existing_words.append(base_cand_ecc)
                    existing_words.append(incr_cand_ecc)
                    return (base_cand_ecc, incr_cand_ecc)


def _get_new_state_word_chain(config, existing_words, num_levels):
    '''Randomly generate codewords following those rules:
    - 1) Each value is a valid ECC codeword
    - 2) Each value contains all bits of the previous one (A in B in K in L).
    - 3) Each step (0->A, A->B, B->K, K->L, L->ONE) adds exactly 4 bits (for
         22-bit ECC codewords).
    - 4) Every value fits inside ONE.
    - 5) All values are different.
    - 6) Each step (including L->ONE) sets at least min_level_data_hd data
         bits, so any two levels differ in at least that many data bits.
    '''
    # Generate the ONES values for SCRAP. For the 6-bit ECC + 16-data bit
    # config this gives us 011110 1111111111111111.
    prng = SecurePrngFactory.get("lc_non_secure")
    ones = ecc_encode(config, '1' * config['secded']['data_width'])
    width = len(ones)
    set_pos = [i for i, b in enumerate(ones) if b == '1']
    if len(set_pos) % (num_levels + 1):
        raise RuntimeError(
            'Cannot split the all-ones codeword ({} set bits) into {} equal '
            'steps'.format(len(set_pos), num_levels + 1))
    step_hw = len(set_pos) // (num_levels + 1)

    # We need num_levels=4 values (A, B, K, L). In the 6-bit ECC + 16-data bit
    # config we can choose 20 out of the 22 bits (the two 0 bits in the ECC
    # need to stay). We need 5 4-bit pieces that form valid ECC codewords.
    # Compute them here.
    # The data bits are the lower data_width bits of each codeword.
    data_mask = (1 << config['secded']['data_width']) - 1
    min_data = config['min_level_data_hd']
    pieces = []
    for pos in itertools.combinations(set_pos, step_hw):
        cand = ''.join('1' if i in pos else '0' for i in range(width))
        if (is_valid_codeword(config, cand) and
                bin(int(cand, 2) & data_mask).count('1') >= min_data):
            pieces.append(int(cand, 2))
    if not pieces:
        raise RuntimeError('No codewords of weight {} below the all-ones '
                           'codeword'.format(step_hw))

    # Select num_levels pieces that then will be the values for (A, B, K, L).
    # The first one can be selected randomly. For the other ones we need to
    # make sure that only bits are set that haven't been set before.
    # Retry on a dead end or if a resulting value already exists.
    while True:
        acc, chain = 0, []
        for _ in range(num_levels):
            cands = [a for a in pieces if not (a & acc)]
            if not cands:
                break
            acc |= prng.choice(cands)
            chain.append(format(acc, '0{}b'.format(width)))
        rest_data = (int(ones, 2) ^ acc) & data_mask
        if (len(chain) == num_levels and
                not any(w in existing_words for w in chain) and
                bin(rest_data).count('1') >= min_data):
            break

    # The last piece (L -> ONE) consists of the leftover bits.
    rest = format(int(ones, 2) ^ acc, '0{}b'.format(width))
    if not is_valid_codeword(config, rest):
        raise RuntimeError('Remainder step {} is not a codeword'.format(rest))

    log.info('word {}: {}'.format(len(existing_words),
                                  ' -> '.join(chain)))
    existing_words.extend(chain)

    return tuple(chain)


def _validate_chain_words(config, chains, all_words):
    '''Validate generated codeword chains.
    - Each value is a valid ECC codeword.
    - Each step only adds bits, never removes any of them.
    - Each value is unique accross all generated words.
    - Each step sets at least min_level_data_hd data bits.
    '''
    ones = ecc_encode(config, '1' * config['secded']['data_width'])
    data_mask = (1 << config['secded']['data_width']) - 1
    for k, chain in enumerate(chains):
        prev = '0' * len(ones)
        for w in list(chain) + [ones]:
            if not is_valid_codeword(config, w):
                raise RuntimeError('Codeword {} in chain {} is not valid'.format(
                    w, k))
            if not _is_incremental_codeword(prev, w):
                raise RuntimeError(
                    'Codeword {} in chain {} is not incremental wrt {}'.format(
                        w, k, prev))
            step_data = (int(w, 2) ^ int(prev, 2)) & data_mask
            if bin(step_data).count('1') < config['min_level_data_hd']:
                raise RuntimeError(
                    'Codeword {} in chain {} sets less than {} data bits '
                    'wrt {}'.format(w, k, config['min_level_data_hd'], prev))
            prev = w
        for w in chain:
            if all_words.count(w) != 1:
                raise RuntimeError('Codeword {} in chain {} is not unique'.format(
                    w, k))


def _check_state_order(config, typ):
    '''Check the ordering rules of the state table (see lc_ctrl_state.hjson).

    Words are grouped into blocks of num_words_per_block consecutive words.
    '''
    num_words = config['num_' + typ + '_words']
    config.setdefault('num_words_per_block', 1)
    bw = check_int(config['num_words_per_block'])
    if bw < 1 or num_words % bw:
        raise RuntimeError(
            'num_words_per_block {} does not divide the {} words of {}'.format(
                bw, num_words, typ))
    config['num_words_per_block'] = bw

    fmts = LC_STATE_TYPES[typ]
    states = {
        name: [[f.format(j) for f in fmts].index(e) for j, e in enumerate(words)]
        for name, words in config[typ].items()
    }
    for u, U in states.items():
        for v, V in states.items():
            if u == v or any(a > b for a, b in zip(U, V)):
                continue
            for w, W in states.items():
                if w in (u, v):
                    continue
                if all(W[i] in (U[i], V[i]) for i in range(len(W))):
                    raise RuntimeError(
                        '{}: state {} violates the ordering rules wrt {} '
                        'and {}'.format(typ, w, u, v))
                for f in range(0, num_words, bw):
                    if (W[:f] == V[:f] and W[f + bw:] == U[f + bw:] and
                            all(U[i] <= W[i] <= V[i] for i in range(f, f + bw))):
                        raise RuntimeError(
                            '{}: state {} violates the ordering rules wrt {} '
                            'and {}'.format(typ, w, u, v))


def _validate_words(config, words):
    '''Validate generated words (base and incremental).'''
    for k, w in enumerate(words):
        # Check whether word is valid wrt to ECC polynomial.
        if not is_valid_codeword(config, w):
            raise RuntimeError('Codeword {} at index {} is not valid'.format(
                w, k))
        # Check that word fulfills the Hamming weight constraints.
        pop_cnt = w.count('1')
        if pop_cnt < config['min_hw'] or pop_cnt > config['max_hw']:
            raise RuntimeError(
                'Codeword {} at index {} has wrong Hamming weight'.format(
                    w, k))
        # Check Hamming distance wrt to all other existing words.
        # If the constraint is larger than 0 this implies uniqueness.
        if k < len(words) - 1:
            for k2, w2 in enumerate(words[k + 1:]):
                if get_hd(w, w2) < config['min_hd']:
                    raise RuntimeError(
                        'Hamming distance between codeword {} at index {} '
                        'and codeword {} at index {} is too low.'.format(
                            w, k, w2, k + 1 + k2))


def _validate_secded(config):
    '''Validate SECDED configuration'''
    config['secded'].setdefault('data_width', 0)
    config['secded'].setdefault('ecc_width', 0)
    config['secded'].setdefault('ecc_matrix', [[]])
    config['secded']['data_width'] = check_int(config['secded']['data_width'])
    config['secded']['ecc_width'] = check_int(config['secded']['ecc_width'])

    total_width = config['secded']['data_width'] + config['secded']['ecc_width']

    if config['secded']['data_width'] % 8:
        raise RuntimeError('SECDED data width must be a multiple of 8')

    if config['secded']['ecc_width'] != len(config['secded']['ecc_matrix']):
        raise RuntimeError('ECC matrix does not have correct number of rows')

    log.info('SECDED Matrix:')
    for i, fanin in enumerate(config['secded']['ecc_matrix']):
        log.info('ECC Bit {} Fanin: {}'.format(i, fanin))
        for j, element in enumerate(fanin):
            element = check_int(element)
            if element < 0 or element >= total_width:
                raise RuntimeError('ECC bit position is out of bounds')
            config['secded']['ecc_matrix'][i][j] = element


def _validate_constraints(config):
    '''Validates Hamming weight and distance constraints'''
    config.setdefault('min_hw', 0)
    config.setdefault('max_hw', 0)
    config.setdefault('min_hd', 0)
    # Minimum number of data bits (without ECC bits) by which two levels of
    # the same multi-level word differ.
    config.setdefault('min_level_data_hd', 2)
    config['min_hw'] = check_int(config['min_hw'])
    config['max_hw'] = check_int(config['max_hw'])
    config['min_hd'] = check_int(config['min_hd'])
    config['min_level_data_hd'] = check_int(config['min_level_data_hd'])

    total_width = config['secded']['data_width'] + config['secded']['ecc_width']

    if config['min_hw'] >= total_width or \
       config['max_hw'] > total_width or \
       config['min_hw'] >= config['max_hw']:
        raise RuntimeError('Hamming weight constraints are inconsistent.')

    if config['max_hw'] - config['min_hw'] + 1 < config['min_hd']:
        raise RuntimeError('Hamming distance constraint is inconsistent.')


def _validate_tokens(config):
    '''Validates and hashes the tokens'''
    config.setdefault('token_size', 128)
    config['token_size'] = check_int(config['token_size'])
    # This needs to be byte aligned
    if config['token_size'] % 8:
        raise ValueError('Size of token {} must be byte aligned'.format(
            config['token_size']))

    num_bytes = config['token_size'] // 8

    hashed_tokens = []
    prng = SecurePrngFactory.get("lc_secure")
    for token in config['tokens']:
        random_or_hexvalue(prng, token, 'value', config['token_size'])
        hashed_token = OrderedDict()
        hashed_token['name'] = token['name'] + 'Hashed'
        data = token['value'].to_bytes(num_bytes, byteorder='little')
        # Custom string chosen for life cycle KMAC App interface
        custom = 'LC_CTRL'.encode('UTF-8')
        hashobj = cSHAKE128.new(data=data, custom=custom)
        hashed_token['value'] = int.from_bytes(hashobj.read(num_bytes),
                                               byteorder='little')
        hashed_tokens.append(hashed_token)

    config['tokens'] += hashed_tokens


def _validate_state_declarations(config):
    '''Validates life cycle state and counter declarations'''
    for typ in LC_STATE_TYPES.keys():
        for k, state in enumerate(config[typ].keys()):
            if k == 0:
                config['num_' + typ + '_words'] = len(config[typ][state])
                log.info('Inferred {} = {}'.format(
                    'num_' + typ + '_words', config['num_' + typ + '_words']))
            if config['num_' + typ + '_words'] != len(config[typ][state]):
                raise RuntimeError(
                    '{} entry {} has incorrect length {}'.format(
                        typ, state, len(config[typ][state])))
            # Render the format templates above.
            for j, entry in enumerate(config[typ][state]):
                legal_values = [fmt.format(j) for fmt in LC_STATE_TYPES[typ]]
                if entry not in legal_values:
                    raise RuntimeError(
                        'Illegal entry "{}" found in {} of {}'.format(
                            entry, state, typ))


def _generate_words(config):
    '''Generate encoding words'''
    config['genwords'] = {}  # dict holding the word pairs for each state type
    existing_words = []  # temporary list of all words for uniqueness tests
    pair_words = []  # words subject to the min/max HW and min HD constraints
    chains = []  # multi-level chains, constrained by construction instead
    for typ in LC_STATE_TYPES.keys():
        config['genwords'][typ] = []
        for k in range(config['num_' + typ + '_words']):
            if _is_chain_type(typ):
                # Levels without '0' and ONE.
                num_levels = len(LC_STATE_TYPES[typ]) - 2
                new_word = _get_new_state_word_chain(config, existing_words,
                                                     num_levels)
                chains.append(new_word)
            else:
                new_word = _get_new_state_word_pair(config, existing_words)
                pair_words += list(new_word)
            config['genwords'][typ].append(new_word)

    # Validate words (this must not fail at this point).
    _validate_words(config, pair_words)
    _validate_chain_words(config, chains, existing_words)
    for typ in ORDER_CHECKED_TYPES:
        _check_state_order(config, typ)

    # Calculate and store statistics
    config['stats'] = hd_histogram(existing_words)
    log.info('')
    log.info('Hamming distance histogram:')
    log.info('')
    for bar in config['stats']["bars"]:
        log.info(bar)
    log.info('')
    log.info('Minimum HD: {}'.format(config['stats']['min_hd']))
    log.info('Maximum HD: {}'.format(config['stats']['max_hd']))
    log.info('Minimum HW: {}'.format(config['stats']['min_hw']))
    log.info('Maximum HW: {}'.format(config['stats']['max_hw']))


class LcStEnc():
    '''Life cycle state encoding generator class

    The constructor expects the parsed configuration
    hjson to be passed in.
    '''

    # This holds the config dict.
    config = {}

    def __init__(self, config, seed):
        '''The constructor validates the configuration dict.'''

        log.info('')
        log.info('Generate life cycle state')
        log.info('')

        if 'secded' not in config:
            raise RuntimeError('Missing secded configuration')
        if 'tokens' not in config:
            raise RuntimeError('Missing token configuration')

        for typ in LC_STATE_TYPES.keys():
            if typ not in config:
                raise RuntimeError('Missing {} definition'.format(typ))

        config['seed'] = seed
        log.info('Seed: {0:x}'.format(config['seed']))
        log.info('')

        SecurePrngFactory.create("lc_secure", int(config["seed"]))
        SecurePrngFactory.create("lc_non_secure", lc_ctrl_non_secure_seed)

        log.info('Checking SECDED.')
        _validate_secded(config)
        log.info('')
        log.info('Checking Hamming weight and distance constraints.')
        _validate_constraints(config)
        log.info('')
        log.info('Hashing tokens.')
        _validate_tokens(config)
        log.info('')
        log.info('Checking state declarations.')
        _validate_state_declarations(config)
        log.info('')
        log.info('Generate incremental word encodings.')
        _generate_words(config)

        self.config = config

        log.info('')
        log.info('Successfully generated life cycle state.')
        log.info('')

    def encode(self, name, state):
        '''Look up state encoding and return as integer value'''

        data_width = self.config['secded']['data_width']
        ecc_width = self.config['secded']['ecc_width']

        if name not in LC_STATE_TYPES:
            raise RuntimeError('Unknown state type {}'.format(name))

        if state not in self.config[name]:
            raise RuntimeError('Unknown state {} of type {}'.format(
                state, name))

        # Assemble list of state words
        words = []
        for j, entry in enumerate(self.config[name][state]):
            # This creates an index lookup table
            val_idx = {
                fmt.format(j): i
                for i, fmt in enumerate(LC_STATE_TYPES[name])
            }
            idx = val_idx[entry]
            if idx == 0:
                words.append(0)
            elif entry == ONE:
                words.append((1 << data_width) - 1)
            else:
                # Only extract data portion, discard ECC portion
                word = self.config['genwords'][name][j][idx - 1][ecc_width:]
                words.append(int(word, 2))

        # Convert words to one value
        outval = 0
        for k, word in enumerate(words):
            outval += word << (data_width * k)

        return outval
