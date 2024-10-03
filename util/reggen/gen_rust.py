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
from typing import Optional, Set, TextIO

from reggen.field import Field
from reggen.ip_block import IpBlock
from reggen.params import LocalParam
from reggen.register import Register
from reggen.multi_register import MultiRegister
from reggen.signal import Signal
from reggen.window import Window


def genout(outfile: TextIO, msg: str) -> None:
    outfile.write(msg)


def to_snake_case(s: str) -> str:
    val = []
    for i, ch in enumerate(s):
        if i > 0 and ch.isupper():
            val.append('_')
        val.append(ch)
    return ''.join(val)


def as_define(s: str) -> str:
    s = s.upper()
    r = ''
    for i in range(0, len(s)):
        r += s[i] if s[i].isalnum() else '_'
    return r


def first_line(s: str) -> str:
    """Returns the first line of a multi-line string"""
    return s.splitlines()[0]


def format_comment(s: str) -> str:
    """Formats a string to comment wrapped to an 80 character line width

    Returns wrapped string including newline and // comment characters.
    """
    comment = textwrap.wrap(s,
                            width=77,
                            initial_indent='// ',
                            subsequent_indent='// ')
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


def gen_const_register(outstr: TextIO, reg: Register, comp: str, width: int,
                       rnames: Set[str], existing_defines: Set[str]) -> None:
    rname = reg.name
    offset = reg.offset

    genout(outstr, format_comment(first_line(reg.desc)))
    defname = as_define(comp + '_' + rname)
    gen_const(outstr, defname, 'REG_OFFSET', offset, existing_defines, True)

    for field in reg.fields:
        dname = defname + '_' + as_define(field.name)
        field_width = field.bits.width()

        if field_width == 1:
            # single bit
            gen_const(outstr, dname, 'BIT', field.bits.lsb, existing_defines)
        else:
            # multiple bits (unless it is the whole register)
            if field_width != width:
                mask = field.bits.bitmask() >> field.bits.lsb
                gen_const(outstr, dname, 'MASK', mask, existing_defines, True)
                gen_const(outstr, dname, 'OFFSET', field.bits.lsb,
                          existing_defines)

            if field.enum is not None:
                for enum in field.enum:
                    ename = as_define(enum.name)
                    gen_const(outstr, defname + '_' + as_define(field.name),
                              'VALUE_' + ename, enum.value, existing_defines,
                              True)

    genout(outstr, '\n')
    return


def gen_const_window(outstr: TextIO, win: Window, comp: str, regwidth: int,
                     rnames: Set[str], existing_defines: Set[str]) -> None:
    offset = win.offset

    genout(outstr, format_comment('Memory area: ' + first_line(win.desc)))
    defname = as_define(comp + '_' + win.name)
    gen_const(outstr, defname, 'REG_OFFSET', offset, existing_defines, True)
    items = win.items
    gen_const(outstr, defname, 'SIZE_WORDS', items, existing_defines)
    items = items * (regwidth // 8)
    gen_const(outstr, defname, 'SIZE_BYTES', items, existing_defines)

    wid = win.validbits
    if (wid != regwidth):
        mask = (1 << wid) - 1
        gen_const(outstr, defname, 'MASK', mask, existing_defines, True)


def gen_rust_module_param(outstr: TextIO, param: LocalParam, module_name: str,
                          existing_defines: Set[str]) -> None:
    # Presently there is only one type (int), however if the new types are
    # added, they potentially need to be handled differently.
    known_types = ["int"]
    if param.param_type not in known_types:
        warnings.warn(
            f"Cannot generate a module define of type {param.param_type}")
        return

    if param.desc is not None:
        genout(outstr, format_comment(first_line(param.desc)))
    # Heuristic: if the name already has underscores, it's already snake_case,
    # otherwise, assume StudlyCaps and covert it to snake_case.
    param_name = param.name if '_' in param.name else to_snake_case(param.name)
    define_name = as_define(module_name + '_PARAM_' + param_name)
    if param.param_type == "int":
        gen_const(outstr, define_name, '', int(param.value), existing_defines)

    genout(outstr, '\n')


def gen_const_module_params(outstr: TextIO, module_data: IpBlock,
                            module_name: str, register_width: int,
                            existing_defines: Set[str]) -> None:
    for param in module_data.params.get_localparams():
        gen_rust_module_param(outstr, param, module_name, existing_defines)

    genout(outstr, format_comment(first_line("Register width")))
    define_name = as_define(module_name + '_PARAM_REG_WIDTH')
    gen_const(outstr, define_name, '', register_width, existing_defines)
    genout(outstr, '\n')


def gen_multireg_field_defines(outstr: TextIO, regname: str, field: Field,
                               subreg_num: int, regwidth: int,
                               existing_defines: Set[str]) -> None:
    field_width = field.bits.width()
    fields_per_reg = regwidth // field_width

    suffix = as_define(field.name + "_FIELD_WIDTH")
    gen_const(outstr, regname, suffix, field_width, existing_defines)

    suffix = as_define(field.name + "_FIELDS_PER_REG")
    gen_const(outstr, regname, suffix, fields_per_reg, existing_defines)

    gen_const(outstr, regname, "MULTIREG_COUNT", subreg_num, existing_defines)

    genout(outstr, '\n')


def gen_const_multireg(outstr: TextIO, multireg: MultiRegister, component: str,
                       regwidth: int, rnames: Set[str],
                       existing_defines: Set[str]) -> None:
    preg = multireg.pregs[0]
    comment = preg.desc + " (common parameters)"
    genout(outstr, format_comment(first_line(comment)))
    if len(preg.fields) == 1:
        regname = as_define(component + '_' + preg.name)
        gen_multireg_field_defines(outstr, regname, preg.fields[0],
                                   len(multireg.cregs), regwidth,
                                   existing_defines)
    else:
        log.warn("Non-homogeneous multireg " + preg.name +
                 " skip multireg specific data generation.")

    for subreg in multireg.cregs:
        gen_const_register(outstr, subreg, component, regwidth, rnames,
                           existing_defines)


def gen_interrupt_field(outstr: TextIO, interrupt: Signal, component: str,
                        regwidth: int, existing_defines: Set[str]) -> None:
    fieldlsb = interrupt.bits.lsb
    iname = interrupt.name
    defname = as_define(component + '_INTR_COMMON_' + iname)

    if interrupt.bits.width() == 1:
        # single bit
        gen_const(outstr, defname, 'BIT', fieldlsb, existing_defines)
    else:
        # multiple bits (unless it is the whole register)
        if interrupt.bits.width() != regwidth:
            mask = interrupt.bits.msb >> fieldlsb
            gen_const(outstr, defname, 'MASK', mask, existing_defines, True)
            gen_const(outstr, defname, 'OFFSET', fieldlsb, existing_defines)


def gen_const_interrupts(outstr: TextIO, block: IpBlock, component: str,
                         regwidth: int, existing_defines: Set[str]) -> None:
    # If no_auto_intr is true, then we do not generate common defines,
    # because the bit offsets for a particular interrupt may differ between
    # the interrupt enable/state/test registers.
    if block.no_auto_intr:
        return

    genout(outstr, format_comment(first_line("Common Interrupt Offsets")))
    for intr in block.interrupts:
        gen_interrupt_field(outstr, intr, component, regwidth,
                            existing_defines)
    genout(outstr, '\n')


def gen_rust(block: IpBlock, outfile: TextIO, src_lic: Optional[str],
             src_copy: str) -> int:
    rnames = block.get_rnames()

    outstr = io.StringIO()

    # This tracks the defines that have been generated so far, so we
    # can error if we attempt to duplicate a definition
    existing_defines = set()  # type: Set[str]

    gen_const_module_params(outstr, block, block.name, block.regwidth,
                            existing_defines)

    gen_const_interrupts(outstr, block, block.name, block.regwidth,
                         existing_defines)

    for rb in block.reg_blocks.values():
        for x in rb.entries:
            if isinstance(x, Register):
                gen_const_register(outstr, x, block.name, block.regwidth,
                                   rnames, existing_defines)
                continue

            if isinstance(x, MultiRegister):
                gen_const_multireg(outstr, x, block.name, block.regwidth,
                                   rnames, existing_defines)
                continue

            if isinstance(x, Window):
                gen_const_window(outstr, x, block.name, block.regwidth, rnames,
                                 existing_defines)
                continue

    generated = outstr.getvalue()
    outstr.close()

    genout(outfile,
           '// Generated register constants for ' + block.name + '\n\n')
    if src_copy != '':
        genout(outfile, '// Copyright information found in source file:\n')
        genout(outfile, '// ' + src_copy + '\n\n')
    if src_lic is not None:
        genout(outfile, '// Licensing information found in source file:\n')
        for line in src_lic.splitlines():
            genout(outfile, '// ' + line + '\n')
        genout(outfile, '\n')

    genout(outfile, generated)

    genout(outfile, '// End generated register constants for ' + block.name)

    return 0


def test_gen_const() -> None:
    outstr = io.StringIO()

    basic_oneline = 'pub const MACRO_NAME 10;\n'
    assert (gen_const(outstr, 'MACRO', 'NAME', 10, set()) == basic_oneline)

    long_macro_name = 'A_VERY_VERY_VERY_VERY_VERY_VERY_VERY_VERY_VERY_VERY_VERY_LONG_MACRO_NAME'
    multiline = ('pub const ' + long_macro_name + ' \\\n  1000000000;\n')

    assert (gen_const(outstr, long_macro_name, '', 1000000000,
                      set()) == multiline)
