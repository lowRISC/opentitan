# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import unittest
from typing import Dict

from reggen.clocking import Clocking
from reggen.params import ReggenParams
from reggen.register import Register


def _parse(**overrides: object) -> Register:
    '''Parse a 32-bit register with one 8-bit field.

    The keyword arguments are added to the register description. Use 'fields'
    to replace the default field.
    '''
    raw: Dict[str, object] = {
        'name': 'REG',
        'desc': 'A register.',
        'fields': [{'bits': '7:0', 'name': 'FLD', 'desc': 'A field.'}],
    }
    raw.update(overrides)
    clocks = Clocking.from_raw([{'clock': 'clk_i', 'reset': 'rst_ni'}],
                               'test clocking')
    return Register.from_raw(32, 0, ReggenParams(), raw, clocks, False, None)


def _fields(*hwaccess: str, swaccess: str = '') -> list[dict[str, str]]:
    '''Make a list of 8-bit fields, one for each hwaccess value.'''
    fields = []
    for idx, access in enumerate(hwaccess):
        field = {
            'bits': f'{8 * idx + 7}:{8 * idx}',
            'name': f'FLD{idx}',
            'desc': 'A field.',
            'hwaccess': access,
        }
        if swaccess:
            field['swaccess'] = swaccess
        fields.append(field)
    return fields


class TestReinit(unittest.TestCase):
    def test_reinit(self) -> None:
        reg = _parse(swaccess='rw', reinit='my_reinit_i')
        self.assertEqual(reg.reinit, 'my_reinit_i')
        self.assertEqual(reg.get_n_bits(['reinit']), 1)

    def test_hwext_register_hwaccess(self) -> None:
        '''The register-level hwaccess is the default for the fields.'''
        reg = _parse(swaccess='ro', hwext='true', hwaccess='hrw',
                     reinit='my_reinit_i')
        self.assertEqual(reg.reinit, 'my_reinit_i')

        with self.assertRaisesRegex(ValueError, 'supports hw reads'):
            _parse(swaccess='ro', hwext='true', hwaccess='hwo',
                   reinit='my_reinit_i')

    def test_hwext_no_readable_field(self) -> None:
        '''Fields that all override hwaccess to hwo leave no `q` output.'''
        with self.assertRaisesRegex(ValueError, 'supports hw reads'):
            _parse(swaccess='ro', hwext='true', reinit='my_reinit_i',
                   fields=_fields('hwo', 'hwo'))

    def test_hwext_one_readable_field(self) -> None:
        '''One hardware-readable field is enough to deliver the signal.'''
        reg = _parse(swaccess='ro', hwext='true', hwaccess='hwo',
                     reinit='my_reinit_i', fields=_fields('hwo', 'hrw'))
        self.assertEqual(reg.reinit, 'my_reinit_i')
        self.assertGreater(reg.get_n_bits(['q']), 0)

    def test_constant_register(self) -> None:
        '''A register that nothing can write always holds its reset value.'''
        with self.assertRaisesRegex(ValueError, 'reset value'):
            _parse(swaccess='ro', hwaccess='hro', reinit='my_reinit_i')
        with self.assertRaisesRegex(ValueError, 'reset value'):
            _parse(swaccess='ro', hwaccess='none', reinit='my_reinit_i')

        # Without reinit these registers are still accepted.
        self.assertIsNone(_parse(swaccess='ro', hwaccess='none').reinit)

    def test_writable_field(self) -> None:
        '''A write path through any one field is enough.'''
        reg = _parse(swaccess='ro', reinit='my_reinit_i',
                     fields=_fields('hro', 'hrw'))
        self.assertEqual(reg.reinit, 'my_reinit_i')

        reg = _parse(swaccess='ro', hwaccess='hro', reinit='my_reinit_i',
                     fields=[{'bits': '0', 'name': 'FLD', 'desc': 'A field.',
                              'swaccess': 'rc'}])
        self.assertEqual(reg.reinit, 'my_reinit_i')


if __name__ == '__main__':
    unittest.main()
