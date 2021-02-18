# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Contains life cycle state encoding class which is
used to generate new life cycle encodings.
"""
import logging as log
import random
from collections import OrderedDict

from lib.common import (check_int, ecc_encode, get_hd, hd_histogram,
                        is_valid_codeword, random_or_hexvalue, scatter_bits)

# Seed diversification constant for LcStEnc (this enables to use
# the same seed for different classes)
LC_SEED_DIVERSIFIER = 1939944205722120255

# State types and permissible format for entries
# The format is index dependent, e.g. ['0', 'A1', 'B1'] for index 1
LC_STATE_TYPES = {
    'lc_state': ['0', 'A{}', 'B{}'],
    'lc_cnt': ['0', 'C{}', 'D{}'],
    'lc_id_state': ['0', 'E{}', 'F{}']
}


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
    # modifyable). Then, we enumerate all possible combinations and scatter
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
    while 1:
        # Draw a random number and check whether it is unique and whether
        # the Hamming weight is in range.
        width = config['secded']['data_width']
        ecc_width = config['secded']['ecc_width']
        base = random.getrandbits(width)
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
                    incr_cand_ecc = random.choice(incr_cands_ecc)
                    log.info('word {}: {}|{} -> {}|{}'.format(
                        int(len(existing_words) / 2),
                        base_cand_ecc[ecc_width:], base_cand_ecc[0:ecc_width],
                        incr_cand_ecc[ecc_width:], incr_cand_ecc[0:ecc_width]))
                    existing_words.append(base_cand_ecc)
                    existing_words.append(incr_cand_ecc)
                    return (base_cand_ecc, incr_cand_ecc)


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
    for i, l in enumerate(config['secded']['ecc_matrix']):
        log.info('ECC Bit {} Fanin: {}'.format(i, l))
        for j, e in enumerate(l):
            e = check_int(e)
            if e < 0 or e >= total_width:
                raise RuntimeError('ECC bit position is out of bounds')
            config['secded']['ecc_matrix'][i][j] = e


def _validate_constraints(config):
    '''Validates Hamming weight and distance constraints'''
    config.setdefault('min_hw', 0)
    config.setdefault('max_hw', 0)
    config.setdefault('min_hd', 0)
    config['min_hw'] = check_int(config['min_hw'])
    config['max_hw'] = check_int(config['max_hw'])
    config['min_hd'] = check_int(config['min_hd'])

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

    hashed_tokens = []
    for token in config['tokens']:
        random_or_hexvalue(token, 'value', config['token_size'])
        hashed_token = OrderedDict()
        hashed_token['name'] = token['name'] + 'Hashed'
        # TODO: plug in PRESENT-based hashing algo or KMAC
        hashed_token['value'] = token['value']
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
    for typ in LC_STATE_TYPES.keys():
        config['genwords'][typ] = []
        for k in range(config['num_' + typ + '_words']):
            new_word = _get_new_state_word_pair(config, existing_words)
            config['genwords'][typ].append(new_word)

    # Validate words (this must not fail at this point).
    _validate_words(config, existing_words)

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

    def __init__(self, config):
        '''The constructor validates the configuration dict.'''

        log.info('')
        log.info('Generate life cycle state')
        log.info('')

        if 'seed' not in config:
            raise RuntimeError('Missing seed in configuration')
        if 'secded' not in config:
            raise RuntimeError('Missing secded configuration')
        if 'tokens' not in config:
            raise RuntimeError('Missing token configuration')

        for typ in LC_STATE_TYPES.keys():
            if typ not in config:
                raise RuntimeError('Missing {} definition'.format(typ))

        config['seed'] = check_int(config['seed'])
        log.info('Seed: {0:x}'.format(config['seed']))
        log.info('')

        # Re-initialize with seed to make results reproducible.
        random.seed(LC_SEED_DIVERSIFIER + int(config['seed']))

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
            else:
                # Only extract data portion, discard ECC portion
                word = self.config['genwords'][name][j][idx - 1][ecc_width:]
                words.append(int(word, 2))

        # Convert words to one value
        outval = 0
        for k, word in enumerate(words):
            outval += word << (data_width * k)

        return outval
