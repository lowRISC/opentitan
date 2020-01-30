# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import sys
import xml.etree.ElementTree as ET
from .lib import convert_top_to_svd


def test():
    """Run a series of self-tests to validate HJSON->SVD conversion."""

    top = {
        'name': 'earlgrey-test',
        'module': [
            {
                'name':      'uart0',
                'type':      'uart-test',
                'base_addr': '0x12345678',
            },
        ],
        'datawidth': 64,
    }

    ips = {
        'uart-test': {
            'name':     'uart-test',
            'regwidth': 64,
            'registers': [
                {
                    'name':      'CTRL',
                    'desc':      'UART control register',
                    'genoffset': 0,
                    'fields': [
                        {
                            'bitinfo':  [31, 6, 1],
                            'name':     'UART_IER',
                            'desc':     'UART interrupt enable',
                            'swaccess': 'rw',
                        },
                    ],
                },
                {
                    'window': {
                        'name':         'UART_FIFO',
                        'desc':         '16 byte UART FIFO buffer',
                        'genoffset':    16,
                        'items':        16,
                        'genvalidbits': 8,
                    },
                },
                { # Should be the first cluster
                    'multireg': {
                        'name': 'UART_CTRL_MULTI',
                        'desc': 'UART control multi',
                        'genregs': [
                            {
                                'name':      'UART_CTRL_0',
                                'desc':      'UART 0 control register',
                                'genoffset': 8,
                                'fields': [
                                    {
                                        'bitinfo':  [31, 4, 4],
                                        'name':     'UART_IER_0',
                                        'desc':     'UART 0 interrupt enable',
                                        'swaccess': 'ro',
                                    },
                                ],
                            },
                            {
                                'name':      'UART_CTRL_1',
                                'desc':      'UART 1 control register',
                                'genoffset': 12,
                                'fields': [
                                    {
                                        'bitinfo':  [31, 3, 8],
                                        'name':     'UART_IER_1',
                                        'desc':     'UART 1 interrupt enable',
                                        'swaccess': 'ro',
                                    },
                                ],
                            },
                        ],
                    },
                },
            ],
        },
    }

    tests = {
        # direct children of <device>
        '.name':    'earlgrey-test',
        '.version': 'g1234567-test',
        '.width':   '64',

        # <cpu> is currently hard-coded
        '.cpu/name':   'other',
        '.cpu/endian': 'little',

        '.peripherals/peripheral/name':        'uart0',
        '.peripherals/peripheral/baseAddress': '0x12345678',

        '.peripherals/peripheral/registers/register/name':          'CTRL',
        '.peripherals/peripheral/registers/register/description':   'UART control register',
        '.peripherals/peripheral/registers/register/addressOffset': '0x0',

        '.peripherals/peripheral/registers/register/dim':          '16',
        '.peripherals/peripheral/registers/register/dimIncrement': '0x1',

        '.peripherals/peripheral/registers/register/fields/field/name':        'UART_IER',
        '.peripherals/peripheral/registers/register/fields/field/description': 'UART interrupt enable',
        '.peripherals/peripheral/registers/register/fields/field/bitRange':    '[6:1]',
        '.peripherals/peripheral/registers/register/fields/field/access':      'read-write',

        '.peripherals/peripheral/registers/cluster/name':          'UART_CTRL_MULTI',
        '.peripherals/peripheral/registers/cluster/description':   'UART control multi',
        '.peripherals/peripheral/registers/cluster/addressOffset': '0x8',

        '.peripherals/peripheral/registers/cluster/register/name':          'UART_CTRL_0',
        '.peripherals/peripheral/registers/cluster/register/description':   'UART 0 control register',
        '.peripherals/peripheral/registers/cluster/register/addressOffset': '0x0',

        '.peripherals/peripheral/registers/cluster/register/fields/field/name':        'UART_IER_0',
        '.peripherals/peripheral/registers/cluster/register/fields/field/description': 'UART 0 interrupt enable',
        '.peripherals/peripheral/registers/cluster/register/fields/field/bitRange':    '[7:4]',
        '.peripherals/peripheral/registers/cluster/register/fields/field/access':      'read-only',
    }

    success = True

    svd = convert_top_to_svd(top, ips, 'g1234567-test', True)

    if not svd.tag == 'device':
        success = False
        print('root node should be "device": ', svd.tag)

    for (path, expect) in tests.items():
        found = svd.find(path)
        if found == None:
            print('missing node: /device/%s' % path[1:])
            success = False
        elif found.text.strip() != expect:
            print('node /device/%s text incorrect: %s' % (path[1:], found.text))
            success = False

    if not success:
        ET.ElementTree(svd).write(sys.stderr, encoding='unicode', xml_declaration=True)
        raise SystemExit('svdgen tests failed')


if __name__ == '__main__':
    test()
