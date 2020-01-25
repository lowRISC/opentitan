#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Generating a System View Description file:

  This utility generates a CMSIS-SVD[1] file from the top configuration and
  IP module HJSON files. The resulting SVD describes the chip's peripherals
  and register layouts. This enables other tools such as `svd2rust`[2] to
  generate software interfaces to the hardware.

  When invoked from the command line this requires arguments pointing to
  all HJSON files and other configuration options. See `./svdgen.py --help`
  for the full options. The `hw/Makefile` script has an example command
  line to generate `top_earlgrey.svd`.

  [1] http://www.keil.com/pack/doc/CMSIS/SVD/html/index.html
  [2] https://docs.rs/svd2rust/

Semantics of the conversion:

  For the most part the HJSON files used by OpenTitan map directly to SVD
  semantics. However, there are a few places where some interpretation is
  required:

  * SVD files must contain a top-level <cpu> element which describe the
    high-level features of the chip. Some of these reflect SVD's origin
    to describe ARM SOCs, and the values aren't necessary to accurately
    described a RISC-V chip. To maintain compatibility with the SVD
    specification these fields are included.

    The fixed values are created in `generate_cpu()`.

  * OpenTitan uses a single `swaccess` field to define what operations
    software may use on a register. SVD uses a combination of three
    separate elements to do the same: <access>, <readAction>, and
    <modifiedWriteValues>.

    This mapping is performed within `sw_access_modes()`.

  * Most OpenTitan register definitions are assumed to be fixed width
    (32 bits). Smaller register width are specified by listing a single
    "field" element which specifies the reduced bit width. SVD instead
    allows each register to specify the reduced width by directly setting
    the <size> of a <register>.

    The heuristic used to detect and flatten these fields is documented
    in `generate_register()`.

  * Both OpenTitan and SVD allowing grouping registers with related
    funcationality. An OpenTitan "multireg" specifies all offsets
    relative to the peripheral base address, while SVD instead gives a
    <cluster> an <addressOffset>, and each <register> is relative to the
    <cluster>.

    This is computed in `generate_cluster()` and specified via the `base`
    argument to `generate_register()`.
"""

import argparse
import hjson
import pysvd
import subprocess
import sys
import xml.etree.ElementTree as ET
from pathlib import Path
from topgen import load_completecfg_and_ips


genhdr = '''
  Copyright lowRISC contributors.
  Licensed under the Apache License, Version 2.0, see LICENSE for details.
  SPDX-License-Identifier: Apache-2.0

  This file generated from HJSON source by "svdgen.py", do not edit.
'''

def hex_or_none(num: int) -> str or None:
    """Converts None -> None and everything else to a hex string. This
    simplifies use with `svd_node()` which ignores elements whose value is
    `None`."""

    if num == None:
        return None

    return hex(num)

def svd_node(element: str or ET.Element, *elements: [ET.Element], **texts: {"tag": object}) -> ET.Element:
    """Construct an SVD element using the information provided.

    If the first argument is not an `ET.Element` this constructs a new
    `ET.Element` using the argument as a name. Any keyword arguments are
    created as child elements whose text contents match the stringified
    value given.

    In addition to keyword arguments, this accepts any number of additional
    positional arguments. These must be `ET.Element` objects and are
    appended to the child elements *after* any named text arguments (even
    though Python syntaxt requires specifying them *before* all named
    parameters.) This is done to improve legibility of the generated XML,
    placing the shorter, textual elements before any deeply nested tree.

    This ignores any keyword arguments whose value is `None`. This
    simplifies reading HJSON and converting it; liberal use of `hjson.get()`
    will skip any optional values which aren't set."""

    if type(element) == str:
        element = ET.Element(element)
    elif type(element) != ET.Element:
        raise TypeError('expected str or ET.Element')

    for (tag, value) in texts.items():
        if value == None:
            continue

        e = ET.Element(tag)
        e.text = str(value)
        element.append(e)

    element.extend(elements)
    return element

def indent_tree(element: ET.Element, indent='\n'):
    """Pretty-print the given element. This modifies the element in place
    by tweaking the contents. It assumes that it is safe to adjust
    whitespace in the XML nodes. (This is true for SVD.)

    ElementTree prints all whitespace in the XML tree verbatim; it has
    no option to automatically indent its output. Without first touching
    this up the result is distracting to a human reader."""

    # element.text appears immediately following the element's openings
    # tag. In the case of a parent node this results in the child's
    # indentation level.
    #
    # element.tail appears immediately following the closing tag, this
    # results in padding for its next sibling/parent closing tag.
    #
    # This function takes advantage of a property of an SVD XML tree: a
    # node is either a parent or it contains text, never both.

    is_parent = len(element) != 0

    if is_parent:
        element.text = indent + '  '
    elif element.text != None:
        element.text = element.text.strip()

    element.tail = indent

    for child in element:
        indent_tree(child, indent + '  ')
        last = child

    if is_parent:
        last.tail = indent

def generate_all_interrupts(irqs: hjson) -> [ET.Element]:
    """Generate a series of <interrupt> nodes from HJSON. Yields nothing
    if irqs is `None`. (This simplifies use in `generate_peripheral()`.)"""

    if irqs == None:
        return

    for (num, irq) in enumerate(irqs):
        yield svd_node('interrupt',
            name        = irq['name'],
            description = irq.get('name'),
            value       = num)

def sw_access_modes(reg_or_field: [hjson]) -> (pysvd.type.access, pysvd.type.readAction, pysvd.type.modifiedWriteValues):
    """Converts from OpenTitan software register access level to equivalent
    SVD access types. Whereas OpenTitan uses a single string to identify
    each different level SVD uses a combination of up to three optional
    register attributes.

    This returns a triplet of pysvd types; each individual field may be
    `None` to indicate no matching SVD field is necessary in the register
    definition. See the following pysvd enum datatypes for reference:
       * `pysvd.type.access`
       * `pysvd.type.readAction`
       * `pysvd.type.modifiedWriteValues`

    There's one interesting access level with unique semantics: "r0w1c":
    read-zero, write-one-clears. SVD doesn't have a corresponding value;
    since software can always assume the value is zero this is mapped to
    a write-only access level."""

    # SVD register read/write access types:
    read_only  = pysvd.type.access.read_only
    read_write = pysvd.type.access.read_write
    write_only = pysvd.type.access.write_only

    # SVD action when register is read:
    clear_on_read = pysvd.type.readAction.clear

    # SVD modified register write semantics:
    one_clears  = pysvd.type.modifiedWriteValues.oneToClear
    one_sets    = pysvd.type.modifiedWriteValues.oneToSet
    zero_clears = pysvd.type.modifiedWriteValues.zeroToClear

    modes = {
        None:    (None,       None,          None),
        'ro':    (read_only,  None,          None),
        'rc':    (read_only,  clear_on_read, None),
        'rw':    (read_write, None,          None),
        'r0w1c': (write_only, None,          one_clears),
        'rw1s':  (read_write, None,          one_sets),
        'rw1c':  (read_write, None,          one_clears),
        'rw0c':  (read_write, None,          zero_clears),
        'wo':    (write_only, None,          None),
    }

    return modes[reg_or_field.get('swaccess')]

def generate_bitrange(bitinfo: [int, int, int]) -> str:
    """Convert a generated `bitfield` to <bitRange> text"""

    # HJSON bitinfo contains the LSB and field width; SVD <bitRange>
    # specifies the range [LSB:MSB] inclusive.
    (width, lsb) = (bitinfo[1], bitinfo[2])
    return '[%d:%d]' % (lsb+width-1, lsb)

def generate_field(bits: hjson) -> ET.Element:
    """Convert an HJSON bit field to a <field> node"""

    (access, readAction, modifiedWriteValues) = sw_access_modes(bits)
    return svd_node('field',
            name                = bits['name'],
            description         = bits['desc'],
            bitRange            = generate_bitrange(bits['bitinfo']),
            access              = access,
            readAction          = readAction,
            modifiedWriteValues = modifiedWriteValues)

def generate_register(reg: hjson, base=0) -> ET.Element:
    """Convert a standard register definition into a <register> node.
    Most of the work was previously done during validation and loading
    the HJSON file; what's left is mostly transliteration."""

    # To define registers with smaller bit widths the HJSON includes a
    # single field in the register; that field has a single element
    # "bits". During `reggen.validate` the field is expanded with data
    # gleaned from the parent register.
    #
    # SVD has different semantics. Instead the register may have a
    # `<size>` element set specifying the width. (If not set, the width
    # is inherited from the top-level <device>.)
    #
    # When generating a register we must detect and flatten the field
    # into the register. This occurs when there is a single field whose
    # name matches the register and whose bit offset is zero.
    fields = reg.get('fields')
    flatten = fields != None and \
            len(fields) == 1 and \
            fields[0]['name'] == reg['name'] and \
            fields[0]['bitinfo'][2] == 0

    if flatten:
        size = fields[0]['bitinfo'][1]
    else:
        size = None

    # Ignore an empty or flattened <fields>
    def generate_all_fields(flatten: bool, fields: [hjson]) -> ET.Element:
        if not flatten and fields != None:
            yield svd_node('fields', *map(generate_field, fields))

    (access, readAction, modifiedWriteValues) = sw_access_modes(reg)
    return svd_node('register',
            name                = reg['name'],
            description         = reg['desc'],
            addressOffset       = hex_or_none(reg['genoffset'] - base),
            size                = size,
            mask                = hex_or_none(reg.get('genbitsused')),
            resetValue          = hex_or_none(reg.get('genresval')),
            resetMask           = hex_or_none(reg.get('genresmask')),
            access              = access,
            readAction          = readAction,
            modifiedWriteValues = modifiedWriteValues,
            *generate_all_fields(flatten, fields))

def generate_dim_register(window: hjson) -> ET.Element:
    """Generate an SVD <register> element containing a buffer. This is
    done by setting the the <dim> subelement, indicating the register
    contains multiple items."""

    window = svd_node(generate_register(window),
            dim          = window['items'],
            dimIncrement = hex_or_none(int(window['genvalidbits']/8)))

    # SVD files require the magic string "%s" in the register to generate
    # a numbered offset into the window. HJSON doesn't have this; append
    # it as necessary.
    name = window.find('./name')
    if name.text.find('%s') < 0:
        name.text += '%s'

    return window

def generate_cluster(multi: [hjson]) -> ET.Element:
    """Generate a <cluster> node from a multireg. The <cluster> will
    contain a <register> for each register in `genregs`.

    The <cluster> node will have its `addressOffset` set from its child
    register's lowest `genoffset`; following SVD convention all the
    <register> "addressOffset" values will be relative to the parent
    <cluster>."""

    genregs = multi['genregs']

    # All registers in the multiregs have their 'genoffset' set relative
    # to the peripheral. Set the cluster's addressOffset to the lowest
    # genoffset, and then generate all registers relative to this.
    base = min(reg['genoffset'] for reg in genregs)

    return svd_node('cluster',
            name          = multi['name'],
            description   = multi['desc'],
            addressOffset = hex_or_none(base),
            *(generate_register(reg, base) for reg in genregs))

def generate_all_registers(regs: [hjson]) -> [ET.Element]:
    """Convert a list of register HJSON element into a <registers> node.
    Like generating C headers, this needs to filter based on a register's
    type.

    This is a generator function; due to filtering reserved/skipped
    memory and expanding multi-registers the number of registers produced
    likely will not match the number of registers in."""

    for reg in regs:
        if 'reserved' in reg or 'skipto' in reg:
            pass
        elif 'window' in reg:
            yield generate_dim_register(reg['window'])
        elif 'sameaddr' in reg:
            yield from map(generate_register, reg['sameaddr'])
        elif 'multireg' in reg:
            yield generate_cluster(reg['multireg'])
        else:
            yield generate_register(reg)

def generate_peripheral(module: hjson, ip: hjson) -> ET.Element:
    """Convert an IP module definition to a <peripheral> element. This
    pulls only the name and base address from the top-level HJSON."""

    # argument ordering is deceptive; <name> and <baseAddress> will
    # preceed all <interrupt>s, <register>s, and the comment
    return svd_node('peripheral',
            *generate_all_interrupts(ip.get('interrupt_list')),
            svd_node('registers', *generate_all_registers(ip['registers'])),
            ET.Comment('end of %s' % module['name']),
            name        = module['name'],
            baseAddress = module['base_addr'])

def generate_peripherals(modules: hjson, ips: {'name': hjson}) -> ET.Element:
    """Generate a <peripherals> element filled by cross-referencing the
    IP definition for each item in the top's module list."""

    return svd_node('peripherals',
            *(generate_peripheral(module, ips[module['type']]) for module in modules))

def generate_cpu() -> ET.Element:
    """Generate a <cpu> element. Currently all values are hardcoded as
    they are not included in either the top level or IP module HJSON.

    Multiple values are set to comply with the SVD specification, even
    though the don't apply to the ibex processor."""

    return svd_node('cpu',
            name                = pysvd.type.cpuName.other,
            endian              = pysvd.type.endian.little,
            revision            = 0,
            mpuPresent          = "false",
            fpuPresent          = "false",
            nvicPrioBits        = 0,
            vendorSystickConfig = "false")

def generate_device(top: hjson, ips: {'name': hjson}, version: str, description: str) -> ET.Element:
    """Generate an SVD <device> node from the top-level HJSON. For each
    module defined in `top` the corresponding peripheral definition is
    generated by the IP block in `ips`.

    SVD files need some basic information that isn't provided within the
    HJSON descriptions. While they might be available elsewhere in the
    configuration, it's simplest just to declare them here."""

    return svd_node(ET.Element('device', attrib = {
                'schemaVersion': '1.1',
                'xmlns:xs': 'http://www.w3.org/2001/XMLSchema-instance',
                'xs:noNamespaceSchemaLocation': 'CMSIS-SVD.xsd',
            }),
            generate_cpu(),
            generate_peripherals(top['module'], ips),
            vendor          = 'lowRISC',
            name            = top['name'],
            version         = version,
            description     = description,
            width           = top['datawidth'],
            size            = top['datawidth'],
            addressUnitBits = 8)

def convert_top_to_svd(top: hjson, ips: {'name': hjson}, version: str, description: str, verify=True) -> ET.Element:
    """Convert a top-level configuration and IP register definition set
    into a System View Description ("SVD") file. This returns an
    `xml.etree.ElementTree.Element` object matching the passed HJSON.

    The input HJSON must be a top-level configuration (earlgrey) and the
    full set of IP module definitions for that configuration. These two
    will be parsed and converted into a single XML tree with a top-level
    "<device>" node. Both the top configuration and IP modules must have
    been previously validated. (see `topgen.validate_top` and `reggen.validate()`)

    If `verify` is true then the resulting SVD tree is validated using
    the `pysvd` module."""

    root = generate_device(top, ips, version, description)

    # Manually indent the XML tree. When writing out XML ElementTree
    # maintains all whitespace verbatim; skipping this step causes the
    # SVD file's newlines and indentation to match what was read from
    # the HJSON file.
    indent_tree(root)

    # Simply constructing a Device is enough to run the pysvd parser and
    # validate the structure of the XML tree.
    if verify:
        pysvd.element.Device(root)

    return root

def write_svd(device: ET.Element, output):
    """Write out the generated SVD <device> element and its children to a
    file in XML format. The SVD contents are preceeded by a comment with
    the given copyright notice and a warning that the file was generated
    by this script."""

    comment = ET.Comment(genhdr)
    comment.tail = '\n'

    # The python3 ElementTree API doesn't natively support a top-level
    # documentation comment. Fake it for reader clarity.
    ET.ElementTree(comment).write(output, encoding='unicode', xml_declaration=True)
    ET.ElementTree(device).write(output, encoding='unicode', xml_declaration=False)


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


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--topcfg',
                        required=True,
                        help='`top_{name}.hjson` file.')
    parser.add_argument('--ip_dir',
                        required=True,
                        help='IP module directory')
    parser.add_argument('--version',
                        required=True,
                        help='the version to embed in the SVD')
    parser.add_argument('--readme',
                        required=True,
                        help='the README file to embed in the Svd')
    parser.add_argument('--output',
                        required=True,
                        help='the destination SVD filename')
    parser.add_argument('--self-test',
                        action='store_true',
                        help='run self-tests')
    args = parser.parse_args()

    if args.self_test:
        test()

    description = Path(args.readme).read_text()
    topcfg = Path(args.topcfg)
    ip_dir = Path(args.ip_dir)

    completecfg, ip_objs = load_completecfg_and_ips(topcfg, ip_dir)
    ips = {ip['name'].lower(): ip for ip in ip_objs}
    svd = convert_top_to_svd(completecfg, ips, args.version, description)

    with open(args.output, 'w') as output:
        write_svd(svd, output)


if __name__ == '__main__':
    main()
