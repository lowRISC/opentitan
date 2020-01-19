# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Generate SVD file from validated register JSON tree
"""

import hjson
import pysvd
import subprocess
import sys
import xml.etree.ElementTree as ET

DESCRIPTION = '''
OpenTitan is an open source silicon Root of Trust (RoT) project. OpenTitan
will make the silicon RoT design and implementation more transparent,
trustworthy, and secure for enterprises, platform providers, and chip
manufacturers. OpenTitan is administered by lowRISC CIC as a collaborative
project to produce high quality, open IP for instantiation as a full-featured
product. See the the OpenTitan site and OpenTitan docs for more information
about the project.'''

COPYRIGHT = ''' Generated register defines for "%s".

Copyright information found in source file: %s
Licensing information found in source file: %s
'''


def read_git_version() -> str:
    """Read the repository version string from Git"""

    describe = 'git describe --tags --long --dirty'.split()
    describe = subprocess.run(describe, capture_output=True)
    if describe.returncode != 0:
        raise SystemExit('failed to determine Git repository version: %s' %
                str(describe.stderr, 'UTF-8'))

    return str(describe.stdout, 'UTF-8').strip()

def value(num: int) -> str or None:
    """Converts None -> None and everything else to hex"""

    if num != None:
        return hex(num)

def ordinal(n: int) -> str:
    """Convert an integer into its English ordinal number: 1st, 2nd, ...
    The returned value is 1-based to account for sequence numbering in a
    list (intended for human consumption)."""

    tens, digit = divmod(n%100, 10)
    suffix = 'stndrdth'[2*min(digit + (tens==1)*3, 3):]
    return '%i%s' % (n+1, suffix[:2])

def create(element: str or ET.Element, /, *elements: [ET.Element], **texts: {"tag": object}) -> ET.Element:
    """Construct an SVD element using the information provided.

    If the first argument is not an `ET.Element` this constructs a new
    `ET.Element` using the argument as a name. Any keyword arguments are
    created a child elements whose text contents match the stringified
    value given.

    In addition to keyword arguments, this accepts any number of additional
    positional arguments. These must be `ET.Element` objects and are
    appended to the child elements *after* any named text arguments (even
    though Python syntaxt requires specifying them *before* all named
    parameters.) This is done to improve legibility of the generated XML,
    placing the shorter, textual elements before any deeply nested tree.

    This ignores any keyword arguments whose value is `None`. This
    simplfies reading HJSON and converting it; liberal use of `hjson.get()`
    will skip any values not present."""

    if type(element) != ET.Element:
        element = ET.Element(str(element))

    for (tag, value) in texts.items():
        if value != None:
            e = ET.Element(tag)
            e.text = str(value)
            element.append(e)

    element.extend(elements)
    return element

def beautify(element: ET.Element, indent='\n') -> ET.Element:
    """Pretty-print the given element. This modifies the element in place
    by tweaking the contents. It assumes that it is safe to adjust
    whitespace in the XML nodes. (This is true for SVD)"""

    if len(element) != 0:
        element.text = indent + '  '
    elif element.text != None:
        element.text = element.text.strip()

    element.tail = indent

    last = None
    for child in element:
        last = beautify(child, indent + '  ')

    if last != None:
        last.tail = indent

    return element

def interrupts(irqs: hjson) -> [ET.Element]:
    """Generate a series of <interrupt> nodes from HJSON. Yields nothing
    if irqs is `None`. (This simplifies use in `peripheral()`.)"""

    if irqs == None:
        return

    for (num, irq) in enumerate(irqs):
        yield create('interrupt',
            name        = irq['name'],
            description = irq.get('name'),
            value       = num)

def swaccess(reg_or_field: [hjson]) -> (pysvd.type.access, pysvd.type.readAction, pysvd.type.modifiedWriteValues):
    """Converts from OpenTitan software register access level to equivalent
    SVD access types. Whereas OpenTitan uses a single string to identify
    each different level, each OpenTitan level maps to a combincation of
    SVD register attributes.

    This returns a triplet of pysvd types; each individual field may be
    `None` to indicate no matching SVD field. See the following pysvd
    enum datatypes for reference:
       * `pysvd.type.access`
       * `pysvd.type.readAction`
       * `pysvd.type.modifiedWriteValues`"""

    swaccesses = {
        None:    (None, None, None),
        'ro':    (pysvd.type.access.read_only,
                  None,
                  None),
        'rc':    (pysvd.type.access.read_only,
                  pysvd.type.readAction.clear,
                  None),
        'rw':    (pysvd.type.access.read_write,
                  None,
                  None),
        'r0w1c': (pysvd.type.access.write_only,
                  None,
                  pysvd.type.modifiedWriteValues.oneToClear),
        'rw1s':  (pysvd.type.access.read_write,
                  None,
                  pysvd.type.modifiedWriteValues.oneToSet),
        'rw1c':  (pysvd.type.access.read_write,
                  None,
                  pysvd.type.modifiedWriteValues.oneToClear),
        'rw0c':  (pysvd.type.access.read_write,
                  None,
                  pysvd.type.modifiedWriteValues.zeroToClear),
        'wo':    (pysvd.type.access.write_only,
                  None,
                  None),
    }

    return swaccesses[reg_or_field.get('swaccess')]

def bitfield(bitinfo: [int, int, int]) -> str:
    """Convert a generated `bitfield` to <bitRange> text"""

    (width, lsb) = (bitinfo[1], bitinfo[2])
    return '[%d:%d]' % (lsb+width, lsb)

def field(bits: hjson) -> ET.Element:
    """Convert an HJSON bit field to a <field> node"""

    (access, readAction, modifiedWriteValues) = swaccess(bits)
    return create('field',
            name                = bits['name'],
            description         = bits['desc'],
            bitRange            = bitfield(bits['bitinfo']),
            access              = access,
            readAction          = readAction,
            modifiedWriteValues = modifiedWriteValues)

def register(reg: hjson, base=0) -> ET.Element:
    """Convert a standard register definition into a <register> node.
    Most of the work was previously done during validation and loading
    the HJSON file; what's left is mostly transliteration."""

    # To define registers with smaller widths the HJSON includes a
    # single field in the register; that field has a single element
    # "bits". During `reggen.validate` the field is expanded with data
    # gleaned from the parent register.
    #
    # SVD has a different semantics, where instead the register has a
    # `<size>` element set specifying the width. (If not set, the width
    # is inherited from the top-level <device>.)
    #
    # When generating a register we must detect and flatten the field
    # into the register. This occurs when there is a single field whose
    # name matches the register and whose bit offset is zero.
    flatten = (fields := reg.get('fields')) != None and \
            len(fields) == 1 and \
            fields[0]['name'] == reg['name'] and \
            fields[0]['bitinfo'][2] == 0

    size = flatten and fields[0]['bitinfo'][1] or None

    # Ignore an empty or flattened <fields>
    def regfields(flatten: bool, fields: [hjson]) -> ET.Element:
        if not flatten and fields != None:
            yield create('fields', *map(field, fields))

    (access, readAction, modifiedWriteValues) = swaccess(reg)
    return create('register',
            name                = reg['name'],
            description         = reg['desc'],
            addressOffset       = hex(reg['genoffset'] - base),
            size                = size,
            mask                = value(reg.get('genbitsused')),
            resetValue          = value(reg.get('genresval')),
            resetMask           = value(reg.get('genresmask')),
            access              = access,
            readAction          = readAction,
            modifiedWriteValues = modifiedWriteValues,
            *regfields(flatten, fields))

def window(window: hjson) -> ET.Element:
    """This should generate an SVD <register> element, likely with a set
    of `dimElementGroup` subelements. Currently, it just returns a comment
    documenting the omission."""

    # TODO: generate window register
    #gen_cdefine_window(outstr, reg['window'], component, regwidth, rnames)
    #hjson.dump(window, sys.stderr, indent='  ', sort_keys=True, default=str)

    return ET.Comment('skipped %d byte register window "%s"' % (int(window['items']), window['name']))

def multireg(multi: [hjson]) -> [ET.Element]:
    """Generate a series of <register> nodes from a multireg. If the
    multireg is empty this yields no items; if it contains a single item
    then it yields a single <register> node. When it contains multiple
    items then a <cluster> element is created containing a <register>
    node for each."""

    genregs = multi['genregs']
    if len(genregs) == 1:
        yield register(genregs[0])
    elif len(genregs) > 1:
        # A cluster has a base address, and then registers within the
        # cluster have address offsets relative to the cluster base.
        base = min(reg['genoffset'] for reg in genregs)

        yield create('cluster',
                name          = multi['name'],
                description   = multi['desc'],
                addressOffset = hex(base),
                *(register(reg, base) for reg in genregs))

def registers(regs: [hjson]) -> [ET.Element]:
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
            yield window(reg['window'])
        elif 'sameaddr' in reg:
            yield from map(register, reg['sameaddr'])
        elif 'multireg' in reg:
            yield from multireg(reg['multireg'])
        else:
            yield register(reg)

def peripheral(module: hjson, ip: hjson) -> ET.Element:
    """Convert an IP module definition to a <peripheral> element. This
    pulls only the name and base address from the top-level HJSON."""

    # argument ordering is deceptive; <name> and <baseAddress> will
    # preceed all <interrupt>s, <register>s, and the comment
    return create('peripheral',
            *interrupts(ip.get('interrupt_list')),
            create('registers', *registers(ip['registers'])),
            ET.Comment('end of %s' % module['name']),
            name        = module['name'],
            baseAddress = module['base_addr'])

def cpu() -> ET.Element:
    """Generate a <cpu> element. Currently all values are hardcoded as
    they are not included in either the top level or IP module HJSON."""

    # TODO: allow customizing these.

    # RISCV is not present in pysvd so this would fail validation. We
    # set it to the (inaccurate) value `other`, and patch it up after
    # performing the validation step.
    name = pysvd.type.cpuName.other

    return create('cpu',
            name                = name,
            endian              = pysvd.type.endian.little,
            revision            = 0,
            mpuPresent          = "true",
            fpuPresent          = "false",
            nvicPrioBits        = 0,
            vendorSystickConfig = "false",
    )

def device(top: hjson, ips: {'name': hjson}, version: str) -> ET.Element:
    """Generate an SVD <device> node from the top-level HJSON. For each
    module defined in `top` the corresponding peripheral definition is
    generated by the IP block in `ips`.

    SVD files need some basic information that isn't provided within the
    HJSON descriptions. While they might be available elsewhere in the
    configuration, it's simplest just to declare them here."""

    # Cross reference module with IP to generate a peripheral
    def p(m: hjson) -> ET.Element:
        return peripheral(m, ips[m['type']])

    return create(ET.Element('device', attrib = {
                'schemaVersion': '1.1',
                'xmlns:xs': 'http://www.w3.org/2001/XMLSchema-instance',
                'xs:noNamespaceSchemaLocation': 'CMSIS-SVD.xsd',
            }),
            # TODO: pull the relevant copyright info from HJSON files.
            ET.Comment(COPYRIGHT % (top['name'], '???', '???')),
            cpu(),
            create('peripherals', *map(p, top['module'])),
            vendor          = 'lowRISC OpenTitan',
            vendorID        = 'lowRISC',
            name            = top['name'],
            version         = version,
            description     = DESCRIPTION,
            width           = top['datawidth'],
            size            = top['datawidth'],
            addressUnitBits = 8)

def generate(top: hjson, ips: {'name': hjson}, version: str, validate=True) -> ET.Element:
    """Convert a top-lvel configuration and IP register definition set
    into a System View Description ("SVD") file. SVD is an XML format,
    originally defined by ARM to "formalize the description of the system
    contained in Arm Cortex-M processor-based microcontrollers".¹ It has
    since been extended for use on other platforms, and is used in other
    fields such as Rust embedded programming.²

    SVD is an XML-based format with standardized definitions for memory
    layouts, register definitions, and similar microcontroller fields.

    The input HJSON must be a top-level configuration (earlgrey) and the
    full set of IP modeule definitions for that configuration. These two
    will be parsed and converted into a single XML tree with a top-level
    "<device>" node. Both the top configuration and IP modules must have
    been previously validated. (see ??? and `reggen.validate()`)

    If `validate` is true then the resulting SVD file is validated using
    the `pysvd` module.

    ¹ http://www.keil.com/pack/doc/CMSIS/SVD/html/index.html
    ² https://github.com/rust-embedded/svd2rust"""

    root = device(top, ips, version)

    # Simply constructing a Device is enough to run the pysvd parser and
    # validate the structure of the XML tree.
    if validate:
        pysvd.element.Device(root)

    # Workaround for limitations of SVD/pysvd. See comment in `cpu()`.
    root.find('.cpu/name').text = 'RISCV'

    beautify(root)
    return ET.ElementTree(root)

def validate(top: hjson, ips: {"name": hjson}) -> bool:
    """Validate the combined top-level HJSON and IP module definitions.
    This checks for required fields in all the HJSON and ensures that a
    corresponding IP block exists for all modules in `top`.

    This assumes each individual IP module was previously validated using
    the `reggen.validate.validate()` function."""

    for field in ['name', 'datawidth', 'module']:
        if not field in top:
            yield 'missing required field %s in top hjson' % field

    for (i, module) in enumerate(top['module']):
        name = module.get('name') or ordinal(i)

        for field in ['name', 'type', 'base_addr']:
            if not field in module:
                yield 'missing field "%s" in %s module' % (field, name)

        if (tipe := module.get('type')) != None and not tipe in ips:
            yield 'module "%s" references missing IP hjson: "%s"' % (name, tipe)

    for ip in ips.values():
        if ip['regwidth'] != top['datawidth']:
            yield 'register width of module "%s" does not top hjson' % ip['name']


def test():
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
                { # Should be ignored
                    'multireg': {
                        'name':    'UART_IGNORED',
                        'desc':    'UART ignored multireg',
                        'genregs': [],
                    },
                },
                { # Should flatten to single register
                    'multireg': {
                        'name':    'UART_FLATTEN',
                        'desc':    'UART flattened multireg',
                        'genregs': [
                            {
                                'name':      'UART_FLATTENED',
                                'desc':      'UART flattened',
                                'genoffset': 4,
                            },
                        ],
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
        '.cpu/name':   'RISCV',
        '.cpu/endian': 'little',

        '.peripherals/peripheral/name':       'uart0',
        '.peripherals/peripheral/baseAddress': '0x12345678',

        '.peripherals/peripheral/registers/register/name':          'CTRL',
        '.peripherals/peripheral/registers/register/description':   'UART control register',
        '.peripherals/peripheral/registers/register/addressOffset': '0x0',

        '.peripherals/peripheral/registers/register/fields/field/name':        'UART_IER',
        '.peripherals/peripheral/registers/register/fields/field/description': 'UART interrupt enable',
        '.peripherals/peripheral/registers/register/fields/field/bitRange':    '[7:1]',
        '.peripherals/peripheral/registers/register/fields/field/access':      'read-write',

        '.peripherals/peripheral/registers/cluster/name':          'UART_CTRL_MULTI',
        '.peripherals/peripheral/registers/cluster/description':   'UART control multi',
        '.peripherals/peripheral/registers/cluster/addressOffset': '0x8',

        '.peripherals/peripheral/registers/cluster/register/name':          'UART_CTRL_0',
        '.peripherals/peripheral/registers/cluster/register/description':   'UART 0 control register',
        '.peripherals/peripheral/registers/cluster/register/addressOffset': '0x0',

        '.peripherals/peripheral/registers/cluster/register/fields/field/name':        'UART_IER_0',
        '.peripherals/peripheral/registers/cluster/register/fields/field/description': 'UART 0 interrupt enable',
        '.peripherals/peripheral/registers/cluster/register/fields/field/bitRange':    '[8:4]',
        '.peripherals/peripheral/registers/cluster/register/fields/field/access':      'read-only',
    }

    success = True
    for error in validate(top, ips):
        success = False
        print('test data invalid:', error)

    svd = generate(top, ips, 'g1234567-test', True)

    if not svd.getroot().tag == 'device':
        success = False
        print('root node should be "device": ', svd.getroot().tag)

    for (path, expect) in tests.items():
        found = svd.find(path)
        if found == None:
            print('missing node: /device/%s' % path[1:])
            success = False
        elif found.text.strip() != expect:
            print('node /device/%s text incorrect: %s' % (path[1:], found.text))
            success = False

    if not success:
        svd.write(sys.stderr, encoding='unicode', xml_declaration=True)
        raise SystemExit('svdgen tests failed')

if __name__ == '__main__':
    test()
