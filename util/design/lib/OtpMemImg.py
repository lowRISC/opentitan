#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""OTP memory image class, used to create preload images for the OTP
memory for simulations and FPGA emulation.
"""

import copy
import logging as log
from pathlib import Path
from typing import List, Tuple

from lib import common
from lib.LcStEnc import LcStEnc
from lib.OtpMemMap import OtpMemMap
from lib.Present import Present
from mako.template import Template
from mubi.prim_mubi import mubi_value_as_int
from topgen import secure_prng as sp

# Seed diversification constant for OtpMemImg (this enables to use
# the same seed for different classes)
OTP_IMG_SEED_DIVERSIFIER = 1941661965323525198146

_OTP_SW_SKIP_FROM_HEADER = ('VENDOR_TEST', 'LIFE_CYCLE')
_OTP_SW_SKIP_DIGEST_FIELDS = ('HW_CFG_DIGEST', 'SECRET0_DIGEST',
                              'SECRET1_DIGEST', 'SECRET2_DIGEST')
_OTP_SW_WRITE_BYTE_ALIGNMENT = {
    'CREATOR_SW_CFG': 4,
    'OWNER_SW_CFG': 4,
    'HW_CFG': 4,
    'SECRET0': 8,
    'SECRET1': 8,
    'SECRET2': 8,
}

ENTROPY_BUFFER_SIZE_BYTES = 10000


def _present_64bit_encrypt(plain, key):
    '''Scramble a 64bit block with PRESENT cipher'''

    # Make sure data is within 64bit range
    assert (plain >= 0) and (plain < 2**64), \
        'Data block is out of 64bit range'

    # Make sure key is within 128bit range
    assert (key >= 0) and (key < 2**128), \
        'Key is out of 128bit range'

    # Make sure inputs are integers
    assert isinstance(plain, int) and isinstance(key, int), \
        'Data and key need to be of type int'

    cipher = Present(key, rounds=32, keylen=128)
    return cipher.encrypt(plain)


def _present_64bit_digest(data_blocks, iv, const):
    '''Compute digest over multiple 64bit data blocks'''

    # Make a deepcopy since we're going to modify and pad the list.
    data_blocks = copy.deepcopy(data_blocks)

    # We need to align the number of data blocks to 2x64bit
    # for the digest to work properly.
    if len(data_blocks) % 2 == 1:
        data_blocks.append(data_blocks[-1])

    # Append finalization constant.
    data_blocks.append(const & 0xFFFF_FFFF_FFFF_FFFF)
    data_blocks.append((const >> 64) & 0xFFFF_FFFF_FFFF_FFFF)

    # This computes a digest according to a Merkle-Damgard construction
    # that uses the Davies-Meyer scheme to turn the PRESENT cipher into
    # a one-way compression function. Digest finalization consists of
    # a final digest round with a 128bit constant.
    # See also: https://docs.opentitan.org/hw/ip/otp_ctrl/doc/index.html#scrambling-datapath
    state = iv
    last_b64 = None
    for b64 in data_blocks:
        if last_b64 is None:
            last_b64 = b64
            continue

        b128 = last_b64 + (b64 << 64)
        state ^= _present_64bit_encrypt(state, b128)
        last_b64 = None

    assert last_b64 is None
    return state


def _to_memfile_with_ecc(data, annotation, config,
                         data_perm) -> Tuple[str, int]:
    '''Compute ECC and convert into MEM file'''

    log.info('Convert to MEM file.')

    data_width = config['secded']['data_width']
    ecc_width = config['secded']['ecc_width']
    assert data_width % 8 == 0, \
        'OTP data width must be a multiple of 8'
    assert data_width <= 64, \
        'OTP data width cannot be larger than 64'

    num_words = len(data) * 8 // data_width
    bytes_per_word = data_width // 8
    # Byte aligned total width after adding ECC bits
    bytes_per_word_ecc = (data_width + ecc_width + 7) // 8
    bit_padding = bytes_per_word_ecc * 8 - data_width - ecc_width
    bin_format_str = '0' + str(data_width) + 'b'
    hex_format_str = '0' + str(bytes_per_word_ecc * 2) + 'x'
    bitness = bytes_per_word_ecc * 8
    mem_lines = [
        '// OTP MEM file with {} x {}bit layout'.format(num_words, bitness),
    ]

    log.info('Memory layout is {} x {}bit (with ECC)'.format(
        num_words, bitness))

    for i_word in range(num_words):
        # Assemble native OTP word and uniquify annotation for comments
        word_address = i_word * bytes_per_word
        word = 0
        word_annotations = set()
        for i_byte in range(bytes_per_word):
            byte_address = word_address + i_byte
            word += data[byte_address] << (i_byte * 8)
            word_annotations.add(annotation[byte_address])

        # ECC encode
        word_bin = format(word, bin_format_str)
        word_bin = common.ecc_encode(config, word_bin)
        # Pad to word boundary and permute data if needed
        word_bin = ('0' * bit_padding) + word_bin
        word_bin = common.permute_bits(word_bin, data_perm)
        word_hex = format(int(word_bin, 2), hex_format_str)

        # Build a MEM line containing this word's address in the memory map and
        # its value. Because this file will be read by Verilog's $readmemh, the
        # address is a *word* offset, not a byte offset. The address does not
        # count ECC bits. In a comment, we also include any annotations
        # associated with the word.
        line = '@{:06x} {} // {}'.format(i_word, word_hex,
                                         ', '.join(word_annotations))
        mem_lines.append(line)

    log.info('Done.')

    return ('\n'.join(mem_lines), bitness)


def _check_unused_keys(dict_to_check, msg_postfix=""):
    '''If there are unused keys, print their names and error out'''
    for key in dict_to_check.keys():
        log.info("Unused key {} in {}".format(key, msg_postfix))
    if dict_to_check:
        raise RuntimeError('Aborting due to unused keys in config dict')


def _int_to_hex_array(val: int, size: int, alignment: int) -> List[str]:
    '''Converts `val` long value into list of hex strings.

    Args:
        val: Input value.
        size: Target output size in number of bytes.
        alignment: Number of bytes to be bundled into a single hex value.
    Returns:
        A list of string hex values using little-endian encoding.
    '''
    fmt_str = '{:0' + str(size * 2) + 'x}'
    val_hex = fmt_str.format(val)

    bytes_hex = []
    for i in range(0, len(val_hex), 2):
        bytes_hex.append(val_hex[i:i + 2])

    if len(bytes_hex) % alignment != 0:
        raise ValueError(len(bytes_hex))

    word_list = []
    for i in range(0, len(bytes_hex), alignment):
        word_list.append("".join(bytes_hex[i:i + alignment]))

    word_list.reverse()
    return [f"0x{y}" for y in word_list]


class OtpMemImg(OtpMemMap):

    def __init__(self, lc_state_config, otp_mmap_config, img_config,
                 data_perm):
        # Initialize memory map
        super().__init__(otp_mmap_config)

        # Initialize the LC state and OTP memory map objects first, since
        # validation and image generation depends on them
        self.lc_state = LcStEnc(lc_state_config)

        # Validate memory image configuration
        log.info('')
        log.info('Parse OTP image specification.')

        # Encryption smoke test with known test vector
        enc_test = _present_64bit_encrypt(0x0123456789abcdef,
                                          0x0123456789abcdef0123456789abcdef)

        assert enc_test == 0x0e9d28685e671dd6, \
            'Encryption module test failed'

        otp_width = self.config['otp']['width'] * 8
        secded_width = self.lc_state.config['secded']['data_width']
        if otp_width != secded_width:
            raise RuntimeError('OTP width and SECDED data width must be equal')

        if 'seed' not in img_config:
            raise RuntimeError('Missing seed in configuration.')

        img_config['seed'] = common.check_int(img_config['seed'])
        log.info('Seed: {0:x}'.format(img_config['seed']))
        log.info('')

        # Re-initialize with seed to make results reproducible.
        sp.reseed(common.expand_seed(OTP_IMG_SEED_DIVERSIFIER + int(img_config['seed'])))

        if 'partitions' not in img_config:
            raise RuntimeError('Missing partitions key in configuration.')

        for part in img_config['partitions']:
            self.merge_part_data(part)
            log.info('Adding values to {} partition.'.format(part['name']))
            for item in part['items']:
                self.merge_item_data(part, item)

        # Key accounting
        img_config_check = img_config.copy()
        del img_config_check['seed']
        del img_config_check['partitions']
        _check_unused_keys(img_config_check, 'in image config')

        log.info('')
        log.info('Parsing OTP image successfully completed.')

        self.validate_data_perm(data_perm)

    def merge_part_data(self, part):
        '''This validates and merges the partition data into the memory map dict'''

        part.setdefault('items', [])
        if not isinstance(part['items'], list):
            raise RuntimeError('the "items" key must contain a list')

        # Check if partition name exists in memory map
        part.setdefault('name', 'unknown_name')
        mmap_part = self.get_part(part['name'])
        if mmap_part is None:
            raise RuntimeError('Partition {} does not exist'.format(
                part['name']))

        # Only partitions with a hardware digest can be locked.
        part.setdefault('lock', 'false')
        part['lock'] = common.check_bool(part['lock'])
        if part['lock'] and not \
           mmap_part['hw_digest']:
            raise RuntimeError(
                'Partition {} does not contain a hardware digest'.format(
                    part['name']))

        # Augment memory map datastructure with lock bit.
        mmap_part['lock'] = part['lock']

        if part['name'] == 'LIFE_CYCLE':
            part.setdefault('state', 'RAW')
            part.setdefault('count', 0)

            part['count'] = common.check_int(part['count'])
            if len(part['items']) > 0:
                raise RuntimeError(
                    'Life cycle items cannot directly be overridden')
            if part['lock']:
                raise RuntimeError('Life cycle partition cannot be locked')

            if part['count'] == 0 and part['state'] != "RAW":
                raise RuntimeError(
                    'Life cycle transition counter can only be zero in the RAW state'
                )

            # Augment life cycle partition with correct life cycle encoding
            state = self.lc_state.encode('lc_state', str(part['state']))
            count = self.lc_state.encode('lc_cnt', str(part['count']))
            part['items'] = [{
                'name': 'LC_STATE',
                'value': '0x{:X}'.format(state)
            }, {
                'name': 'LC_TRANSITION_CNT',
                'value': '0x{:X}'.format(count)
            }]

            # Key accounting
            part_check = part.copy()
            del part_check['state']
            del part_check['count']
        else:
            # Key accounting
            part_check = part.copy()
            if len(part['items']) == 0:
                log.warning("Partition does not contain any items.")

        # Key accounting
        del part_check['items']
        del part_check['name']
        del part_check['lock']
        _check_unused_keys(part_check, "in partition {}".format(part['name']))

    def merge_item_data(self, part, item):
        '''This validates and merges the item data into the memory map dict'''
        item.setdefault('name', 'unknown_name')

        mmap_item = self.get_item(part['name'], item['name'])
        if mmap_item is None:
            raise RuntimeError('Item {} does not exist'.format(item['name']))

        item_size = mmap_item['size']
        item_width = item_size * 8

        # if needed, resolve the mubi value first
        if mmap_item['ismubi']:
            mubi_str = "mubi "
            mubi_val_str = " kMultiBitBool{}".format(item_width)
            item.setdefault("value", "false")
            item["value"] = common.check_bool(item["value"])
            mubi_val_str += "True" if item["value"] else "False"
            item["value"] = mubi_value_as_int(item["value"], item_width)
        else:
            mubi_str = ""
            mubi_val_str = ""
            item.setdefault('value', '0x0')
            common.random_or_hexvalue(item, 'value', item_width)

        mmap_item['value'] = item['value']

        log.info('> Adding {}item {} with size {}B and value{}:'.format(
            mubi_str, item['name'], item_size, mubi_val_str))
        fmt_str = '{:0' + str(item_size * 2) + 'x}'
        value_str = fmt_str.format(item['value'])
        bytes_per_line = 8
        j = 0
        while value_str:
            # Print out max 64bit per line
            line_str = ''
            for k in range(bytes_per_line):
                num_chars = min(len(value_str), 2)
                line_str += value_str[-num_chars:]
                if k < bytes_per_line - 1:
                    line_str += ' '
                value_str = value_str[:len(value_str) - num_chars]
            log.info('  {:06x}: '.format(j) + line_str)
            j += bytes_per_line

        # Key accounting
        item_check = item.copy()
        del item_check['name']
        del item_check['value']
        _check_unused_keys(item_check, 'in item {}'.format(item['name']))

    def override_data(self, img_config):
        '''Override specific partition items'''

        if 'partitions' not in img_config:
            raise RuntimeError('Missing partitions key in configuration.')

        if not isinstance(img_config['partitions'], list):
            raise RuntimeError('the "partitions" key must contain a list')

        for part in img_config['partitions']:
            self.merge_part_data(part)
            log.info('Overriding values of {} partition.'.format(part['name']))
            for item in part['items']:
                self.merge_item_data(part, item)

        # Key accounting
        img_config_check = img_config.copy()
        del img_config_check['partitions']
        _check_unused_keys(img_config_check, 'in image config')

    def streamout_partition(self, part):
        '''Scramble and stream out partition data as a list of bytes'''

        part_name = part['name']
        log.info('Streamout of partition {}'.format(part_name))

        part_offset = part['offset']
        part_size = part['size']
        assert part_size % 8 == 0, 'Partition must be 64bit aligned'

        # First chop up all items into individual bytes.
        data_bytes = [0] * part_size
        # Annotation is propagated into the MEM file as comments
        annotation = ['unallocated'] * part_size
        # Need to keep track of defined items for the scrambling.
        # Undefined regions are left blank (0x0) in the memory.
        defined = [False] * part_size
        for item in part['items']:
            for k in range(item['size']):
                idx = item['offset'] - part_offset + k
                annotation[idx] = part_name + ': ' + item['name']
                if 'value' in item:
                    data_bytes[idx] = ((item['value'] >> (8 * k)) & 0xFF)
                    assert not defined[idx], "Unexpected item collision"
                    defined[idx] = True

        # Reshape this into 64bit blocks (this must be aligned at this point)
        assert len(data_bytes) % 8 == 0, 'data_bytes must be 64bit aligned'

        data_blocks = []
        data_block_defined = []
        for k, b in enumerate(data_bytes):
            if (k % 8) == 0:
                data_blocks.append(b)
                data_block_defined.append(defined[k])
            else:
                data_blocks[k // 8] += (b << 8 * (k % 8))
                # If any of the individual bytes are defined, the
                # whole block is considered defined.
                data_block_defined[k // 8] |= defined[k]

        # Check if scrambling is needed
        if part['secret']:
            part_name = part['name']
            key_sel = part['key_sel']
            log.info('> Scramble partition with key "{}"'.format(key_sel))

            for key in self.config['scrambling']['keys']:
                if key['name'] == key_sel:
                    break
            else:
                raise RuntimeError(
                    'Scrambling key cannot be found {}'.format(key_sel))

            for k in range(len(data_blocks)):
                if data_block_defined[k]:
                    data_blocks[k] = _present_64bit_encrypt(
                        data_blocks[k], key['value'])

        # Check if digest calculation is needed
        if part['hw_digest']:
            # Make sure that this HW-governed digest has not been
            # overridden manually
            if data_blocks[-1] != 0:
                raise RuntimeError(
                    'Digest of partition {} cannot be overridden manually'.
                    format(part_name))

            # Digest is stored in last block of a partition
            if part.setdefault('lock', False):
                log.info('> Lock partition by computing digest')
                # Digest constants at index 0 are used to compute the
                # consistency digest
                iv = self.config['scrambling']['digests'][0]['iv_value']
                const = self.config['scrambling']['digests'][0]['cnst_value']

                data_blocks[-1] = _present_64bit_digest(
                    data_blocks[0:-1], iv, const)
            else:
                log.info(
                    '> Partition is not locked, hence no digest is computed')

        # Convert to a list of bytes to make final packing into
        # OTP memory words independent of the cipher block size.
        data = []
        for block in data_blocks:
            for k in range(8):
                data.append((block >> (8 * k)) & 0xFF)

        # Make sure this has the right size
        assert len(data) == part['size'], 'Partition size mismatch'

        # The annotation list contains a string for each byte
        # that can be used to print out informative comments
        # in the memory hex file.
        return data, annotation

    def validate_data_perm(self, data_perm):
        '''Validate data permutation option'''
        # Byte aligned total width after adding ECC bits
        secded_cfg = self.lc_state.config['secded']
        raw_bitlen = secded_cfg['data_width'] + secded_cfg['ecc_width']
        total_bitlen = ((raw_bitlen + 7) // 8) * 8

        # If the permutation is undefined, use the default mapping.
        self.data_perm = list(
            range(total_bitlen)) if not data_perm else data_perm

        common.validate_data_perm_option(total_bitlen, self.data_perm)

    def streamout_memfile(self) -> Tuple[str, int]:
        '''Streamout of memory image in MEM file format

        Returns a tuple of the file contents and architecture bitness.
        '''

        log.info('Scramble and stream out partitions.')
        log.info('')
        otp_size = self.config['otp']['size']
        data = [0] * otp_size
        annotation = [''] * otp_size
        for part in self.config['partitions']:
            part_data, part_annotation = self.streamout_partition(part)
            assert part['offset'] <= otp_size, \
                'Partition offset out of bounds'
            idx_low = part['offset']
            idx_high = part['offset'] + part['size']
            data[idx_low:idx_high] = part_data
            annotation[idx_low:idx_high] = part_annotation

        log.info('')
        log.info('Streamout successfully completed.')

        # Smoke checks
        assert len(data) <= otp_size, 'Data size mismatch'
        assert len(annotation) <= otp_size, 'Annotation size mismatch'
        assert len(data) == len(annotation), 'Data/Annotation size mismatch'

        return _to_memfile_with_ecc(data, annotation, self.lc_state.config,
                                    self.data_perm)

    def generate_c_file(self, fileheader: str, templatefile: Path) -> str:
        '''Generates C file with provided `header` and `templatefile`.

        Args:
            fileheader: Header to be appended to autogenerated file.
            templatefile: Mako template used to generate header file.
        Returns:
            Generated file in string format.
        '''
        data = {}
        for part in self.config['partitions']:
            if part['name'] in _OTP_SW_SKIP_FROM_HEADER:
                continue
            items = []
            for item in part["items"]:
                if 'value' not in item.keys(
                ) or item['name'] in _OTP_SW_SKIP_DIGEST_FIELDS:
                    continue

                alignment = _OTP_SW_WRITE_BYTE_ALIGNMENT[part['name']]

                # TODO: Handle aggregation of fields to match write boundary.
                if item['size'] < alignment:
                    continue
                assert (item['size'] %
                        alignment) == 0, "invalid field alignment"

                items.append({
                    'name':
                    item['name'],
                    'values':
                    _int_to_hex_array(item['value'], item['size'], alignment),
                    'ismubi':
                    item['ismubi'],
                    'num_items':
                    item['size'] / alignment,
                })
            data[part['name']] = {
                'alignment': alignment,
                'items': items,
            }

        with open(templatefile, 'r') as tplfile:
            tpl = Template(tplfile.read())
            result = tpl.render(fileheader=fileheader, data=data)

        return result
