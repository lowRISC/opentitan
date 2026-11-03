# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import copy
import unittest

from reggen.ip_block import IpBlock

IP = {
    'name': 'foo',
    'cip_id': '1',
    'version': '1.0.0',
    'clocking': [{'clock': 'clk_i', 'reset': 'rst_ni'}],
    'bus_interfaces': [{'protocol': 'tlul', 'direction': 'device',
                        'name': 'a'}],
    'reinit_list': [{'name': 'init_i', 'desc': 'reinit'}],
    'registers': {'a': [{
        'name': 'REG',
        'desc': 'reg',
        'swaccess': 'rw',
        'hwaccess': 'hro',
        'reinit': 'init_i',
        'fields': [{'bits': '0', 'name': 'F', 'desc': 'f'}],
    }, {
        'name': 'LOCK_REGWEN',
        'desc': 'lock',
        'swaccess': 'rw0c',
        'hwaccess': 'none',
        'resval': '1',
        'fields': [{'bits': '0', 'name': 'EN', 'desc': 'en'}],
    }]},
}

ALIAS = {
    'alias_impl': 'impl',
    'alias_target': 'foo',
    'bus_interfaces': [{'protocol': 'tlul', 'direction': 'device',
                        'name': 'a'}],
    'registers': {'a': [{
        'name': 'REG_ALIAS',
        'alias_target': 'REG',
        'desc': 'reg',
        'swaccess': 'rw',
        'hwaccess': 'hro',
        'reinit': 'init_i',
        'fields': [{'bits': '0', 'name': 'F', 'desc': 'f',
                    'alias_target': 'F'}],
    }]},
}


def load(alias):
    ip = IpBlock.from_raw([], copy.deepcopy(IP), 'test')
    ip.alias_from_raw(False, alias, 'alias')
    return ip


class TestAliasReinit(unittest.TestCase):
    def test_first_block_keeps_reinit(self):
        ip = load(copy.deepcopy(ALIAS))
        self.assertEqual(ip.reg_blocks['a'].flat_regs[0].reinit, 'init_i')

    def test_reinit_mismatch(self):
        alias = copy.deepcopy(ALIAS)
        del alias['registers']['a'][0]['reinit']
        with self.assertRaisesRegex(ValueError, 'Value mismatch'):
            load(alias)

    def test_alias_adds_regwen(self):
        alias = copy.deepcopy(ALIAS)
        # reinit and regwen are exclusive per register, so adding a regwen
        # means dropping reinit, which the cross-check rejects.
        del alias['registers']['a'][0]['reinit']
        alias['registers']['a'][0]['regwen'] = 'LOCK_REGWEN'
        alias['registers']['a'].append(copy.deepcopy(IP['registers']['a'][1]))
        alias['registers']['a'][1]['alias_target'] = 'LOCK_REGWEN'
        alias['registers']['a'][1]['name'] = 'LOCK_ALIAS_REGWEN'
        alias['registers']['a'][0]['regwen'] = 'LOCK_ALIAS_REGWEN'
        alias['registers']['a'][1]['fields'][0]['alias_target'] = 'EN'
        with self.assertRaisesRegex(ValueError, 'Missing regwen define'):
            load(alias)
