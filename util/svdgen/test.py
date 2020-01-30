# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import io
import sys
import xml.etree.ElementTree as ET
from itertools import zip_longest
from .lib import convert_top_to_svd, write_svd


def check_xml_result(result_et, expect_xml):
    """Check a computed SVD ET.Element against an expected XML string."""

    def check_et_result(path, result, expect):
        if expect == None:
            yield 'extra element @ %s.%s' % (path, result.tag)
            return

        path = '%s.%s' % (path, expect.tag)
        if result == None:
            yield 'missing element @ %s' % path
            return

        if result.tag != expect.tag:
            yield 'incorrect tag @ %s: %s' % (path, result.tag)
            return

        if result.tail.strip() != '':
            yield 'invalid trailing text @ %s', path

        rtext = (result.text and result.text.strip()) or ''
        etext = (expect.text and expect.text.strip()) or ''
        if rtext != etext:
            yield 'incorrect text @%s: "%s" != "%s"' % (path, rtext, etext)

        for (rchild, echild) in zip_longest(result, expect):
            yield from check_et_result(path, rchild, echild)

    expect_et = ET.XML(expect_xml)
    yield from check_et_result('', result_et, expect_et)


def check_peripheral(name, top, ips, expect_xml):
    success = True
    svd = convert_top_to_svd(top, ips, '-', '-', False)

    # Round trip test through serialization, this drops comments.
    xml = io.StringIO()
    write_svd(svd, xml)
    svd = ET.XML(xml.getvalue())
    peripherals = svd.find('.peripherals/peripheral')

    for error in check_xml_result(peripherals, expect_xml):
        success = False
        sys.stderr.write('%s: %s\n' % (name, error))

    return success


def test_trees():
    top = {
        'name': 'tree-test',
        'module': [
            {
                'name':      'gpio0',
                'type':      'gpio',
                'base_addr': '0x20000000',
            },
        ],
        'datawidth': 32,
    }

    tests = [
      ( # Ensure that interrupts are enumerated correctly.
        'interrupts',
        {
          'name': 'gpio',
          'registers': [],
          'interrupt_list': [
            {
              'name':  'gpio_irq_1',
              'width': 32,
              'type':  'interrupt',
            },
            {
              'name':  'gpio_irq_2',
              'width': 16,
              'type':  'interrupt',
            },
          ],
        },
        '''
          <peripheral>
            <name>gpio0</name>
            <baseAddress>0x20000000</baseAddress>
            <interrupt>
              <name>gpio_irq_1</name>
              <value>0</value>
            </interrupt>
            <interrupt>
              <name>gpio_irq_2</name>
              <value>1</value>
            </interrupt>
            <registers />
          </peripheral>
        ''',
      ),

      ( # Ensure single-field registers are flattened.
        'flatten registers',
        {
          'registers': [
            {
              'name': 'CLASSA_ACCUM_CNT',
              'desc': 'Current accumulation count',
              'fields': [
                {
                  'name': 'classa_accum_cnt',
                  'bitinfo': [
                    65535,
                    16,
                    0
                  ],
                }
              ],
              'genbitsused': 65535,
              'genoffset': 56,
            },
          ],
        },
        '''
          <peripheral>
            <name>gpio0</name>
            <baseAddress>0x20000000</baseAddress>
            <registers>
              <register>
                <name>CLASSA_ACCUM_CNT</name>
                <description>Current accumulation count</description>
                <addressOffset>0x38</addressOffset>
                <size>16</size>
                <mask>0xffff</mask>
              </register>
            </registers>
          </peripheral>
        ''',
      ),

      ( # Check that SW read/write semantics are translated.
        'field read/write semantics',
        {
          'registers': [
            {
              'name': 'FIELD_RW',
              'desc': 'Bitfield r/w semantics',
              'fields': [
                {
                  'name': 'read_clears',
                  'desc': 'read clears this bit',
                  'bitinfo': [1, 1, 0],
                  'swaccess': 'rc',
                },
                {
                  'name': 'read_write',
                  'desc': 'normal read/write',
                  'bitinfo': [2, 1, 1],
                  'swaccess': 'rw',
                },
                {
                  'name': 'read_write_sets',
                  'desc': 'readable, write one sets',
                  'bitinfo': [4, 2, 2],
                  'swaccess': 'rw1s',
                },
              ],
              'genbitsused': 15,
              'genoffset': 4,
            },
          ],
        },
        '''
          <peripheral>
            <name>gpio0</name>
            <baseAddress>0x20000000</baseAddress>
            <registers>
              <register>
                <name>FIELD_RW</name>
                <description>Bitfield r/w semantics</description>
                <addressOffset>0x4</addressOffset>
                <mask>0xf</mask>
                <fields>
                  <field>
                    <name>read_clears</name>
                    <description>read clears this bit</description>
                    <bitRange>[0:0]</bitRange>
                    <access>read-only</access>
                    <readAction>clear</readAction>
                  </field>
                  <field>
                    <name>read_write</name>
                    <description>normal read/write</description>
                    <bitRange>[1:1]</bitRange>
                    <access>read-write</access>
                  </field>
                  <field>
                    <name>read_write_sets</name>
                    <description>readable, write one sets</description>
                    <bitRange>[3:2]</bitRange>
                    <access>read-write</access>
                    <modifiedWriteValues>oneToSet</modifiedWriteValues>
                  </field>
                </fields>
              </register>
            </registers>
          </peripheral>
        '''
      ),

      ( # Check sameaddr (currently unused in topearlgrey).
        'same address registers',
        {
          'registers': [
            {
              'sameaddr': [
                {
                  'name': 'SAME_0',
                  'desc': 'first identical address',
                  'genoffset': 4,
                },
                {
                  'name': 'SAME_1',
                  'desc': 'second identical address',
                  'genoffset': 4,
                },
              ],
            },
          ],
        },
        '''
          <peripheral>
            <name>gpio0</name>
            <baseAddress>0x20000000</baseAddress>
            <registers>
              <register>
                <name>SAME_0</name>
                <description>first identical address</description>
                <addressOffset>0x4</addressOffset>
              </register>
              <register>
                <name>SAME_1</name>
                <description>second identical address</description>
                <addressOffset>0x4</addressOffset>
              </register>
            </registers>
          </peripheral>
        '''
      ),

      ( # Check the window regsiters get a <dim> and <dimIncrement>
        'windowed register',
        {
          'registers': [
            {
              'skipto': 0x800,
            },
            {
              'window': {
                'name': 'MSG_FIFO',
                'items': '512',
                'swaccess': 'wo',
                'byte-write': 'true',
                'desc': 'Message FIFO',
                'genvalidbits': 32,
                'genoffset': 2048,
              },
            },
          ],
        },
        '''
          <peripheral>
            <name>gpio0</name>
            <baseAddress>0x20000000</baseAddress>
            <registers>
              <register>
                <name>MSG_FIFO%s</name><!-- SVD requires the %s for the register number -->
                <description>Message FIFO</description>
                <addressOffset>0x800</addressOffset>
                <access>write-only</access>
                <dim>512</dim>
                <dimIncrement>0x4</dimIncrement>>
              </register>
            </registers>
          </peripheral>
        '''
      ),

      ( # Check computed <cluster> addressOffsets.
        # This also reuses some previous register defintions to test
        # behavior of nested special registers.
        'cluster relative addresses',
        {
          'registers': [
            {
              'multireg': {
                'name': 'multi',
                'desc': 'generate a cluster',
                'genregs': [
                  {
                    'name': 'multi_a',
                    'desc': 'first multi',
                    'genoffset': 0x100,
                  },
                  {
                    'name': 'multi_b',
                    'desc': 'second multi',
                    'genoffset': 0x104,
                  },
                  {
                    'name': 'multi_c',
                    'desc': 'third multi',
                    'genoffset': 0x200,
                  },
                  { # Check nesting of a flattened register
                    'name': 'CLASSA_ACCUM_CNT',
                    'desc': 'Current accumulation count',
                    'fields': [
                      {
                        'name': 'classa_accum_cnt',
                        'bitinfo': [
                          65535,
                          16,
                          0
                        ],
                      }
                    ],
                    'genbitsused': 65535,
                    'genoffset': 0x138,
                  },
                  {
                    'window': {
                      'name': 'MSG_FIFO',
                      'items': '512',
                      'swaccess': 'wo',
                      'byte-write': 'true',
                      'desc': 'Message FIFO',
                      'genvalidbits': 32,
                      'genoffset': 2048,
                    },
                  },
                ],
              },
            },
          ],
        },
        '''
          <peripheral>
            <name>gpio0</name>
            <baseAddress>0x20000000</baseAddress>
            <registers>
              <cluster>
                <name>multi</name>
                <description>generate a cluster</description>
                <addressOffset>0x100</addressOffset>
                <register>
                  <name>multi_a</name>
                  <description>first multi</description>
                  <addressOffset>0x0</addressOffset>
                </register>
                <register>
                  <name>multi_b</name>
                  <description>second multi</description>
                  <addressOffset>0x4</addressOffset>
                </register>
                <register>
                  <name>multi_c</name>
                  <description>third multi</description>
                  <addressOffset>0x100</addressOffset>
                </register>
                <register>
                  <name>CLASSA_ACCUM_CNT</name>
                  <description>Current accumulation count</description>
                  <addressOffset>0x38</addressOffset>
                  <size>16</size>
                  <mask>0xffff</mask>
                </register>
                <register>
                  <name>MSG_FIFO%s</name><!-- SVD requires the %s for the register number -->
                  <description>Message FIFO</description>
                  <addressOffset>0x700</addressOffset>
                  <access>write-only</access>
                  <dim>512</dim>
                  <dimIncrement>0x4</dimIncrement>>
                </register>
              </cluster>
            </registers>
          </peripheral>
        '''
      ),

      ( # A minimal test for copy-pasta
        'change me',
        {
          'registers': [
          ],
        },
        '''
          <peripheral>
            <name>gpio0</name>
            <baseAddress>0x20000000</baseAddress>
            <registers>
            </registers>
          </peripheral>
        '''
      ),
    ]

    # return true iff all tests pass
    return all(check_peripheral(t[0], top, {'gpio': t[1]}, t[2]) for t in tests)


def test_paths():
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
        '.name':        'earlgrey-test',
        '.version':     'g1234567-test',
        '.description': 'earlgrey test',
        '.width':       '64',

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

    svd = convert_top_to_svd(top, ips, 'g1234567-test', 'earlgrey test', True)

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

    return success


if __name__ == '__main__':
    success = test_paths() and test_trees()
    if not success:
        raise SystemExit('svdgen tests failed')
