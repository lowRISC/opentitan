# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Contains life cycle state encoding class which is
used to generate new life cycle encodings.
"""
import logging as log
import random

from common import check_int


def _is_valid_codeword(config, codeword):
    '''Checks whether the bitstring is a valid ECC codeword.'''

    data_width = config['secded']['data_width']
    ecc_width = config['secded']['ecc_width']
    if len(codeword) != (data_width + ecc_width):
        log.error("Invalid codeword length {}".format(len(codeword)))
        exit(1)

    # Build syndrome and check whether it is zero.
    syndrome = [0 for k in range(ecc_width)]

    # The bitstring must be formatted as "data bits[N-1:0]" + "ecc bits[M-1:0]".
    for j, fanin in enumerate(config['secded']['ecc_matrix']):
        syndrome[j] = int(codeword[ecc_width - 1 - j])
        for k in fanin:
            syndrome[j] ^= int(codeword[ecc_width + data_width - 1 - k])

    return sum(syndrome) == 0


def _ecc_encode(config, dataword):
    '''Calculate and prepend ECC bits.'''
    if len(dataword) != config['secded']['data_width']:
        log.error("Invalid codeword length {}".format(len(dataword)))
        exit(1)

    # Build syndrome
    eccbits = ""
    for fanin in config['secded']['ecc_matrix']:
        bit = 0
        for k in fanin:
            bit ^= int(dataword[config['secded']['data_width'] - 1 - k])
        eccbits += format(bit, '01b')

    return eccbits[::-1] + dataword


def _is_incremental_codeword(word1, word2):
    '''Test whether word2 is incremental wrt word1.'''
    if len(word1) != len(word2):
        log.error('Words are not of equal size')
        exit(1)

    _word1 = int(word1, 2)
    _word2 = int(word2, 2)

    # This basically checks that the second word does not
    # clear any bits that are set to 1 in the first word.
    return ((_word1 & _word2) == _word1)


def _scatter_bits(mask, bits):
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


def _get_hd(word1, word2):
    '''Calculate Hamming distance between two words.'''
    if len(word1) != len(word2):
        log.error('Words are not of equal size')
        exit(1)
    return bin(int(word1, 2) ^ int(word2, 2)).count('1')


def _get_incremental_codewords(config, base_ecc, existing_words):
    '''Get all possible incremental codewords fulfilling the constraints.'''

    base_data = base_ecc[config['secded']['ecc_width']:]

    # We only need to spin through data bits that have not been set yet.
    # Hence, we first count how many bits are zero (and hence still
    # modifyable). Then, we enumerate all possible combinations and scatter
    # the bits of the enumerated values into the correct bit positions using
    # the _scatter_bits() function.
    incr_cands = []
    free_bits = base_data.count('0')
    for k in range(1, 2**free_bits):
        # Get incremental dataword by scattering the enumeration bits
        # into the zero bit positions in base_data.
        incr_cand = _scatter_bits(base_data,
                                  format(k, '0' + str(free_bits) + 'b'))
        incr_cand_ecc = _ecc_encode(config, incr_cand)

        # Dataword is correct by construction, but we need to check whether
        # the ECC bits are incremental.
        if _is_incremental_codeword(base_ecc, incr_cand_ecc):
            # Check whether the candidate fulfills the maximum
            # Hamming weight constraint.
            if incr_cand_ecc.count('1') <= config['max_hw']:
                # Check Hamming distance wrt all existing words.
                for w in existing_words + [base_ecc]:
                    if _get_hd(incr_cand_ecc, w) < config['min_hd']:
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
        base_cand_ecc = _ecc_encode(config, base)
        # disallow all-zero and all-one states
        pop_cnt = base_cand_ecc.count('1')
        if pop_cnt >= config['min_hw'] and pop_cnt <= config['max_hw']:

            # Check Hamming distance wrt all existing words
            for w in existing_words:
                if _get_hd(base_cand_ecc, w) < config['min_hd']:
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
        if not _is_valid_codeword(config, w):
            log.error('Codeword {} at index {} is not valid'.format(w, k))
            exit(1)
        # Check that word fulfills the Hamming weight constraints.
        pop_cnt = w.count('1')
        if pop_cnt < config['min_hw'] or pop_cnt > config['max_hw']:
            log.error(
                'Codeword {} at index {} has wrong Hamming weight'.format(
                    w, k))
            exit(1)
        # Check Hamming distance wrt to all other existing words.
        # If the constraint is larger than 0 this implies uniqueness.
        if k < len(words) - 1:
            for k2, w2 in enumerate(words[k + 1:]):
                if _get_hd(w, w2) < config['min_hd']:
                    log.error(
                        'Hamming distance between codeword {} at index {} '
                        'and codeword {} at index {} is too low.'.format(
                            w, k, w2, k + 1 + k2))
                    exit(1)


def _hist_to_bars(hist, m):
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
                dist = _get_hd(j, k)
                hist[dist] += 1
                minimum_hd = min(dist, minimum_hd)
                maximum_hd = max(dist, maximum_hd)

    stats = {}
    stats["hist"] = hist
    stats["bars"] = _hist_to_bars(hist, len(existing_words))
    stats["min_hd"] = minimum_hd
    stats["max_hd"] = maximum_hd
    stats["min_hw"] = minimum_hw
    stats["max_hw"] = maximum_hw
    return stats


class LcStEnc():
    '''Life cycle state encoding generator class

    The constructor expects the parsed configuration
    hjson to be passed in.
    '''

    # This holds the config dict.
    config = {}
    # Holds generated life cycle words.
    gen = {
        'ab_words': [],
        'cd_words': [],
        'ef_words': [],
        'stats': [],
    }

    def __init__(self, config):
        '''The constructor validates the configuration dict.'''

        log.info('')
        log.info('Generate life cycle state')
        log.info('')

        if 'seed' not in config:
            log.error('Missing seed in configuration')
            exit(1)

        if 'secded' not in config:
            log.error('Missing secded configuration')
            exit(1)

        config['secded'].setdefault('data_width', 0)
        config['secded'].setdefault('ecc_width', 0)
        config['secded'].setdefault('ecc_matrix', [[]])
        config.setdefault('num_ab_words', 0)
        config.setdefault('num_cd_words', 0)
        config.setdefault('num_ef_words', 0)
        config.setdefault('min_hw', 0)
        config.setdefault('max_hw', 0)
        config.setdefault('min_hd', 0)

        config['seed'] = check_int(config['seed'])

        log.info('Seed: {0:x}'.format(config['seed']))
        log.info('')

        config['secded']['data_width'] = check_int(
            config['secded']['data_width'])
        config['secded']['ecc_width'] = check_int(
            config['secded']['ecc_width'])
        config['num_ab_words'] = check_int(config['num_ab_words'])
        config['num_cd_words'] = check_int(config['num_cd_words'])
        config['num_ef_words'] = check_int(config['num_ef_words'])
        config['min_hw'] = check_int(config['min_hw'])
        config['max_hw'] = check_int(config['max_hw'])
        config['min_hd'] = check_int(config['min_hd'])

        total_width = config['secded']['data_width'] + config['secded'][
            'ecc_width']

        if config['min_hw'] >= total_width or \
           config['max_hw'] > total_width or \
           config['min_hw'] >= config['max_hw']:
            log.error('Hamming weight constraints are inconsistent.')
            exit(1)

        if config['max_hw'] - config['min_hw'] + 1 < config['min_hd']:
            log.error('Hamming distance constraint is inconsistent.')
            exit(1)

        if config['secded']['ecc_width'] != len(
                config['secded']['ecc_matrix']):
            log.error('ECC matrix does not have correct number of rows')
            exit(1)

        log.info('SECDED Matrix:')
        for i, l in enumerate(config['secded']['ecc_matrix']):
            log.info('ECC Bit {} Fanin: {}'.format(i, l))
            for j, e in enumerate(l):
                e = check_int(e)
                config['secded']['ecc_matrix'][i][j] = e

        log.info('')

        self.config = config

        # Re-initialize with seed to make results reproducible.
        random.seed(int(self.config['seed']))

        # Generate new encoding words
        word_types = ['ab_words', 'cd_words', 'ef_words']
        existing_words = []
        for w in word_types:
            while len(self.gen[w]) < self.config['num_' + w]:
                new_word = _get_new_state_word_pair(self.config,
                                                    existing_words)
                self.gen[w].append(new_word)

        # Validate words (this must not fail at this point).
        _validate_words(self.config, existing_words)

        # Print out HD histogram
        self.gen['stats'] = hd_histogram(existing_words)

        log.info('')
        log.info('Hamming distance histogram:')
        log.info('')
        for bar in self.gen['stats']["bars"]:
            log.info(bar)
        log.info('')
        log.info('Minimum HD: {}'.format(self.gen['stats']['min_hd']))
        log.info('Maximum HD: {}'.format(self.gen['stats']['max_hd']))
        log.info('Minimum HW: {}'.format(self.gen['stats']['min_hw']))
        log.info('Maximum HW: {}'.format(self.gen['stats']['max_hw']))

        log.info('')
        log.info('Successfully generated life cycle state.')
        log.info('')
