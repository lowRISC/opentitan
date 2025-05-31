# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Generate Rust constants from validated register JSON tree
"""

import io
import logging as log
import sys
import textwrap
import warnings
from typing import Any, Optional, Set, TextIO

from reggen.ip_block import IpBlock
from reggen.multi_register import MultiRegister
from reggen.params import LocalParam
from reggen.register import Register
from reggen.window import Window

from version_file import VersionInformation

REG_VISIBILITY = 'pub(crate)'
FIELD_VISIBILITY = 'pub(crate)'


def genout(outfile: TextIO, msg: str, *args: Any, **kwargs: Any) -> None:
    outfile.write(msg.format(*args, **kwargs))


def indent(s: str, amount: int = 4) -> str:
    """Indents a multi-line string considering the depth of bracketing.

    This function assumes the input string is un-indented.  It will not
    unindent an inapprorpiately indented string.
    """
    result = []
    indent = 0
    for line in s.splitlines():
        indented = []
        comment = False
        for i, ch in enumerate(line):
            if i > 0 and ch == '/' and line[i - 1] == '/':
                comment = True
            if not comment and ch in ")]}":
                indent -= 1
            if i == 0:
                indented.append(' ' * indent * amount)
            if not comment and ch in "([{":
                indent += 1
            indented.append(ch)
        result.append(''.join(indented))
        if line == '':
            result.append('')
    return '\n'.join(result)


def to_snake_case(s: str) -> str:
    """Converts a string from a MixedCaseString to a snake_case_string."""
    val = []
    for i, ch in enumerate(s):
        if i > 0 and ch.isupper():
            val.append('_')
        val.append(ch)
    return ''.join(val)


def to_studly_caps(s: str) -> str:
    """Converts a string from a snake_case_string to a StudlyCapsString."""
    words = [w.capitalize() for w in s.split('_')]
    return ''.join(words)


def to_upper_snake_case(s: str) -> str:
    """Converts a string from a MixedCaseString to a UPPER_SNAKE_CASE_STRING."""
    s = s.upper()
    r = ''
    for i in range(0, len(s)):
        r += s[i] if s[i].isalnum() else '_'
    return r


def sanitize_name(s: str) -> str:
    """Remove special characters from name."""
    r = s.replace("-", '_').replace(" ", "_")
    return r


def first_line(s: str) -> str:
    """Returns the first line of a multi-line string"""

    # Just return the 's' if it is empty or 'None'.
    return s.splitlines()[0] if s else s


def format_comment(s: str) -> str:
    """Formats a string to comment wrapped to a 100 character line width

    Returns wrapped string including newline and /// comment characters.
    """
    comment = textwrap.wrap(s,
                            width=97,
                            initial_indent='/// ',
                            subsequent_indent='/// ')
    return '\n'.join(comment) + '\n'


def data_type(name: str, val: int, as_hex: bool) -> str:
    """ Returns proper data type for name-value pair. """

    if name.endswith("_OFFSET") or name.endswith("_BASE_ADDR"):
        return "usize"

    if val.bit_length() > 32:
        log.error(name + " value exceeds 32 bit " + str(val))
        sys.exit(1)

    if not as_hex and val < 0:
        return "i32"

    return "u32"


filler_no = 0


def possibly_gen_filler(regout: TextIO, highest_address: Set[int],
                        next_address: int) -> None:
    r"""Tock requires any gaps between registers do be declared as a reserved field.
    """

    global filler_no
    if len(highest_address) == 0:
        hiaddr = 0
    else:
        hiaddr = sorted(highest_address)[-1]
    if hiaddr >= next_address:
        return
    filler_no += 1
    genout(regout, "(0x{:04x} => _reserved{}),\n", hiaddr, filler_no)


def gen_const(outstr: TextIO,
              name: str,
              suffix: str,
              val: int,
              existing_defines: Set[str],
              as_hex: bool = False) -> str:
    r"""Produces a pub const string. Result includes newline.

    Arguments:
    name - Name of the constant
    val - Value of the constant
    existing_defines - set of already generated define names.
        Error if `name` is in `existing_defines`.

    Example result:
    name = 'A_NAME'
    val = '10'

    pub const A_NAME: u32 = 10

    """

    suffix = '' if not suffix.strip() else '_' + suffix
    name = name + suffix
    if name in existing_defines:
        log.error("Duplicate pub const for " + name)
        sys.exit(1)

    define_declare = 'pub const ' + name + ': ' + data_type(name, val, as_hex)

    val_str = hex(val) if as_hex else str(val)
    oneline_define = define_declare + ' = ' + val_str + ';'

    existing_defines.add(name)

    output = oneline_define + '\n'
    genout(outstr, output)
    return output


def access(reg: Any) -> str:
    swaccess = getattr(reg, 'swaccess', None)
    if swaccess is None:
        swaccess = 'unspecified'
    else:
        swaccess = swaccess.key
    if swaccess == 'ro':
        return 'ReadOnly'
    elif swaccess == 'wo':
        return 'WriteOnly'
    elif swaccess in ('rw', 'rw0c', 'rw1c', 'unspecified'):
        return 'ReadWrite'
    else:
        warnings.warn('{}: Unknown swaccess type {}'.format(
            reg.name, swaccess))
        return 'ReadWrite'


def gen_field_definitions(
        fieldout: TextIO,
        reg: Any,  # Should be Register|IpBlock
        name: str,
        width: int) -> None:
    genout(fieldout, "{} {} [", FIELD_VISIBILITY, name.upper())
    fields: Any
    if isinstance(reg, Register):
        fields = reg.fields
    elif isinstance(reg, IpBlock):
        fields = reg.interrupts
    else:
        raise TypeError(type(reg))

    for field in fields:
        if field.auto_split:
            for sub_field_id in range(field.bits.lsb, field.bits.width()):
                genout(fieldout, "\n{} OFFSET({}) NUMBITS({}) [],",
                       "{}_{}".format(field.name.upper(),
                                      sub_field_id), sub_field_id, 1)
        else:
            genout(fieldout, "\n{} OFFSET({}) NUMBITS({}) [",
                   field.name.upper(), field.bits.lsb, field.bits.width())
            if getattr(field, 'enum', None) is not None:
                for enum in field.enum:
                    genout(fieldout, "\n{} = {},",
                           sanitize_name(enum.name).upper(), enum.value)
                genout(fieldout, "\n],")
            else:
                genout(fieldout, "],")
    else:
        genout(fieldout, "\n],\n")


def gen_const_register(regout: TextIO, fieldout: TextIO, reg: Register,
                       block: IpBlock, rnames: Set[str],
                       existing_defines: Set[str], access_type: Set[str],
                       highest_address: Set[int]) -> None:
    possibly_gen_filler(regout, highest_address, reg.offset)
    if not block.no_auto_intr and reg.name.startswith('INTR_'):
        rname = "INTR"
    else:
        rname = reg.name.upper()
        gen_field_definitions(fieldout, reg, rname, block.regwidth)

    a = access(reg)
    access_type.add(a)
    highest_address.add(reg.offset + block.regwidth // 8)
    regout.write(format_comment(first_line(reg.desc)))
    genout(regout, "(0x{:04x} => {} {}: {}<u32, {}::Register>),\n", reg.offset,
           REG_VISIBILITY, reg.name.lower(), a, rname)


def gen_const_window(regout: TextIO, win: Window, block: IpBlock,
                     rnames: Set[str], existing_defines: Set[str],
                     access_type: Set[str], highest_address: Set[int]) -> None:
    possibly_gen_filler(regout, highest_address, win.offset)
    regout.write(format_comment('Memory area: ' + first_line(win.desc)))
    a = access(win)
    access_type.add(a)
    highest_address.add(win.offset + win.items * block.regwidth // 8)
    genout(regout, "(0x{:04x} => {} {}: [{}<u32>; {}]),\n", win.offset,
           REG_VISIBILITY, win.name.lower(), a, win.items)


def gen_rust_module_param(outstr: TextIO, param: LocalParam, module_name: str,
                          existing_defines: Set[str]) -> None:
    # Presently there is only one type (int), however if the new types are
    # added, they potentially need to be handled differently.
    known_types = ["int"]
    if param.param_type not in known_types:
        warnings.warn("Cannot generate a module define of type {}".format(
            param.param_type))
        return

    if param.desc is not None:
        outstr.write(format_comment(first_line(param.desc)))
    # Heuristic: if the name already has underscores, it's already snake_case,
    # otherwise, assume StudlyCaps and convert it to snake_case.
    param_name = param.name if '_' in param.name else to_snake_case(param.name)
    define_name = to_upper_snake_case(module_name + '_PARAM_' + param_name)
    if param.param_type == "int":
        gen_const(outstr, define_name, '', int(param.value), existing_defines)


def gen_const_module_params(outstr: TextIO, module_data: IpBlock,
                            module_name: str, register_width: int,
                            existing_defines: Set[str]) -> None:
    for param in module_data.params.get_localparams():
        gen_rust_module_param(outstr, param, module_name, existing_defines)

    outstr.write(format_comment(first_line("Register width")))
    define_name = to_upper_snake_case(module_name + '_PARAM_REG_WIDTH')
    gen_const(outstr, define_name, '', register_width, existing_defines)
    outstr.write('\n')


def gen_const_multireg(regout: TextIO, fieldout: TextIO,
                       multireg: MultiRegister, block: IpBlock,
                       rnames: Set[str], existing_defines: Set[str],
                       access_type: Set[str],
                       highest_address: Set[int]) -> None:
    reg = multireg.cregs[0]
    possibly_gen_filler(regout, highest_address, reg.offset)
    rname = reg.name.upper()
    if rname.endswith("_0"):
        rname = rname[:-2]
    rlen = len(multireg.cregs)
    genout(regout, format_comment(first_line(reg.desc)))
    a = access(reg)
    access_type.add(a)
    highest_address.add(reg.offset + rlen * block.regwidth // 8)
    genout(regout, "(0x{:04x} => {} {}: [{}<u32, {}::Register>; {}]),\n",
           reg.offset, REG_VISIBILITY, rname.lower(), a, rname, rlen)
    gen_field_definitions(fieldout, reg, rname, block.regwidth)


def gen_const_interrupts(fieldout: TextIO, block: IpBlock, component: str,
                         regwidth: int, existing_defines: Set[str]) -> None:
    # If no_auto_intr is true, then we do not generate common defines,
    # because the bit offsets for a particular interrupt may differ between
    # the interrupt enable/state/test registers.
    if block.no_auto_intr:
        return
    genout(fieldout, format_comment(first_line("Common Interrupt Offsets")))
    gen_field_definitions(fieldout, block, "INTR", block.regwidth)


def gen_tock(block: IpBlock, outfile: TextIO, src_file: Optional[str],
             src_lic: Optional[str], src_copy: str,
             version: VersionInformation) -> int:
    rnames = block.get_rnames()

    paramout = io.StringIO()
    regout = io.StringIO()
    genout(regout, 'register_structs! {{\npub {}Registers {{\n',
           to_studly_caps(block.name))
    fieldout = io.StringIO()
    genout(fieldout, 'register_bitfields![u32,\n')

    # This tracks the defines that have been generated so far, so we
    # can error if we attempt to duplicate a definition
    existing_defines = set()  # type: Set[str]
    access_type = set()  # type: Set[str]
    highest_address = set()  # type: Set[int]

    gen_const_module_params(paramout, block, block.name, block.regwidth,
                            existing_defines)

    gen_const_interrupts(fieldout, block, block.name, block.regwidth,
                         existing_defines)

    for rb in block.reg_blocks.values():
        for x in rb.entries:
            if isinstance(x, Register):
                gen_const_register(regout, fieldout, x, block, rnames,
                                   existing_defines, access_type,
                                   highest_address)
                continue

            if isinstance(x, MultiRegister):
                gen_const_multireg(regout, fieldout, x, block, rnames,
                                   existing_defines, access_type,
                                   highest_address)
                continue

            if isinstance(x, Window):
                gen_const_window(regout, x, block, rnames, existing_defines,
                                 access_type, highest_address)
                continue

    paramstr = paramout.getvalue()
    paramout.close()

    end = sorted(highest_address)[-1]
    # End the register file.
    genout(regout, '(0x{:04x} => @END),\n', end)
    # Close the "pub <block>" declaration, then the "register_structs!" macro.
    genout(regout, '}}\n}}\n\n')
    regstr = regout.getvalue()
    regout.close()

    # Close the "register_bitfields!" macro.
    genout(fieldout, '];\n\n')
    fieldstr = fieldout.getvalue()
    fieldout.close()

    # Opensource council has approved dual-licensing the generated files under
    # both Apache and MIT licenses.
    # Since these generated files are meant to be imported into the Tock
    # codebase, emit a header acceptable to Tock's license checker.
    genout(
        outfile,
        "// Licensed under the Apache License, Version 2.0 or the MIT License.\n"
    )
    genout(outfile, "// SPDX-License-Identifier: Apache-2.0 OR MIT\n")
    genout(outfile, "// Copyright lowRISC contributors (OpenTitan project).\n")
    genout(outfile, '\n')
    genout(outfile, '// Generated register constants for {}.\n', block.name)

    if version.scm_version() is not None:
        genout(outfile, '// Built for {}\n', version.scm_version())
    if version.scm_revision() is not None:
        genout(outfile, '// https://github.com/lowRISC/opentitan/tree/{}\n',
               version.scm_revision())
    if version.scm_status() is not None:
        genout(outfile, '// Tree status: {}\n', version.scm_status())

    if src_file:
        genout(outfile, '// Original reference file: {}\n', src_file)

    for access in sorted(access_type):
        genout(outfile, "use kernel::utilities::registers::{};\n", access)
    genout(
        outfile,
        "use kernel::utilities::registers::{{register_bitfields, register_structs}};\n"
    )

    outfile.write(indent(paramstr))
    outfile.write(indent(regstr))
    outfile.write(indent(fieldstr))

    genout(outfile, '// End generated register constants for {}\n', block.name)
    return 0


def test_gen_const() -> None:
    outstr = io.StringIO()

    basic_oneline = 'pub const MACRO_NAME 10;\n'
    assert (gen_const(outstr, 'MACRO', 'NAME', 10, set()) == basic_oneline)

    long_macro_name = 'A_VERY_VERY_VERY_VERY_VERY_VERY_VERY_VERY_VERY_VERY_VERY_LONG_MACRO_NAME'
    multiline = ('pub const ' + long_macro_name + ' \\\n' + '  1000000000;\n')

    assert (gen_const(outstr, long_macro_name, '', 1000000000,
                      set()) == multiline)
