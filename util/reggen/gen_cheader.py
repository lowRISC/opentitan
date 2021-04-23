# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Generate C header from validated register JSON tree
"""

import io
import logging as log
import sys
import textwrap
import warnings
from typing import List, Optional, Set, TextIO


from .field import Field
from .ip_block import IpBlock
from .params import LocalParam
from .register import Register
from .multi_register import MultiRegister
from .signal import Signal
from .window import Window


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
    return '\n'.join(
        textwrap.wrap(
            s, width=77, initial_indent='// ', subsequent_indent='// ')) + '\n'


def gen_define(name: str,
               args: List[str],
               body: str,
               existing_defines: Set[str],
               indent: str = '  ') -> str:
    r"""Produces a #define string, will split into two lines if a single line
    has a width greater than 80 characters. Result includes newline.

    Arguments:
    name - Name of the #define
    args - List of arguments for the define, provide an empty list if there are
        none
    body - Body of the #define
    existing_defines - set of already generated define names.
        Error if `name` is in `existing_defines`.
    indent - Gives string to prepend on any new lines produced by
    wrapping (default '  ')

    Example result:
    name = 'A_MACRO'
    args = ['arg1', 'arg2'],
    body = 'arg1 + arg2 + 10'

    #define A_MACRO(arg1, arg2) arg1 + arg2 + 10

    When the macro is wrapped the break happens after the argument list (or
    macro name if there is no argument list

    #define A_MACRO(arg1, arg2) \
      arg1 + arg2 + 10

    """

    if name in existing_defines:
        log.error("Duplicate #define for " + name)
        sys.exit(1)

    if len(args) != 0:
        define_declare = '#define ' + name + '(' + ', '.join(args) + ')'
    else:
        define_declare = '#define ' + name

    oneline_define = define_declare + ' ' + body

    existing_defines.add(name)

    if len(oneline_define) <= 80:
        return oneline_define + '\n'

    return define_declare + ' \\\n' + indent + body + '\n'


def gen_cdefine_register(outstr: TextIO,
                         reg: Register,
                         comp: str,
                         width: int,
                         rnames: Set[str],
                         existing_defines: Set[str]) -> None:
    rname = reg.name
    offset = reg.offset

    genout(outstr, format_comment(first_line(reg.desc)))
    defname = as_define(comp + '_' + rname)
    genout(
        outstr,
        gen_define(defname + '_REG_OFFSET', [], hex(offset), existing_defines))

    for field in reg.fields:
        dname = defname + '_' + as_define(field.name)
        field_width = field.bits.width()

        if field_width == 1:
            # single bit
            genout(
                outstr,
                gen_define(dname + '_BIT', [], str(field.bits.lsb),
                           existing_defines))
        else:
            # multiple bits (unless it is the whole register)
            if field_width != width:
                mask = field.bits.bitmask() >> field.bits.lsb
                genout(
                    outstr,
                    gen_define(dname + '_MASK', [], hex(mask),
                               existing_defines))
                genout(
                    outstr,
                    gen_define(dname + '_OFFSET', [], str(field.bits.lsb),
                               existing_defines))
                genout(
                    outstr,
                    gen_define(
                        dname + '_FIELD', [],
                        '((bitfield_field32_t) {{ .mask = {dname}_MASK, .index = {dname}_OFFSET }})'
                        .format(dname=dname), existing_defines))
            if field.enum is not None:
                for enum in field.enum:
                    ename = as_define(enum.name)
                    value = hex(enum.value)
                    genout(
                        outstr,
                        gen_define(
                            defname + '_' + as_define(field.name) +
                            '_VALUE_' + ename, [], value, existing_defines))
    genout(outstr, '\n')
    return


def gen_cdefine_window(outstr: TextIO,
                       win: Window,
                       comp: str,
                       regwidth: int,
                       rnames: Set[str],
                       existing_defines: Set[str]) -> None:
    offset = win.offset

    genout(outstr, format_comment('Memory area: ' + first_line(win.desc)))
    defname = as_define(comp + '_' + win.name)
    genout(
        outstr,
        gen_define(defname + '_REG_OFFSET', [], hex(offset), existing_defines))
    items = win.items
    genout(
        outstr,
        gen_define(defname + '_SIZE_WORDS', [], str(items), existing_defines))
    items = items * (regwidth // 8)
    genout(
        outstr,
        gen_define(defname + '_SIZE_BYTES', [], str(items), existing_defines))

    wid = win.validbits
    if (wid != regwidth):
        mask = (1 << wid) - 1
        genout(outstr,
               gen_define(defname + '_MASK ', [], hex(mask), existing_defines))


def gen_cdefines_module_param(outstr: TextIO,
                              param: LocalParam,
                              module_name: str,
                              existing_defines: Set[str]) -> None:
    # Presently there is only one type (int), however if the new types are
    # added, they potentially need to be handled differently.
    known_types = ["int"]
    if param.param_type not in known_types:
        warnings.warn("Cannot generate a module define of type {}"
                      .format(param.param_type))
        return

    if param.desc is not None:
        genout(outstr, format_comment(first_line(param.desc)))
    # Heuristic: if the name already has underscores, it's already snake_case,
    # otherwise, assume StudlyCaps and covert it to snake_case.
    param_name = param.name if '_' in param.name else to_snake_case(param.name)
    define_name = as_define(module_name + '_PARAM_' + param_name)
    if param.param_type == "int":
        define = gen_define(define_name, [], param.value,
                            existing_defines)

    genout(outstr, define)
    genout(outstr, '\n')


def gen_cdefines_module_params(outstr: TextIO,
                               module_data: IpBlock,
                               module_name: str,
                               register_width: int,
                               existing_defines: Set[str]) -> None:
    module_params = module_data.params

    for param in module_params.get_localparams():
        gen_cdefines_module_param(outstr, param, module_name, existing_defines)

    genout(outstr, format_comment(first_line("Register width")))
    define_name = as_define(module_name + '_PARAM_REG_WIDTH')
    define = gen_define(define_name, [], str(register_width), existing_defines)
    genout(outstr, define)
    genout(outstr, '\n')


def gen_multireg_field_defines(outstr: TextIO,
                               regname: str,
                               field: Field,
                               subreg_num: int,
                               regwidth: int,
                               existing_defines: Set[str]) -> None:
    field_width = field.bits.width()
    fields_per_reg = regwidth // field_width

    define_name = regname + '_' + as_define(field.name + "_FIELD_WIDTH")
    define = gen_define(define_name, [], str(field_width), existing_defines)
    genout(outstr, define)

    define_name = regname + '_' + as_define(field.name + "_FIELDS_PER_REG")
    define = gen_define(define_name, [], str(fields_per_reg), existing_defines)
    genout(outstr, define)

    define_name = regname + "_MULTIREG_COUNT"
    define = gen_define(define_name, [], str(subreg_num), existing_defines)
    genout(outstr, define)

    genout(outstr, '\n')


def gen_cdefine_multireg(outstr: TextIO,
                         multireg: MultiRegister,
                         component: str,
                         regwidth: int,
                         rnames: Set[str],
                         existing_defines: Set[str]) -> None:
    comment = multireg.reg.desc + " (common parameters)"
    genout(outstr, format_comment(first_line(comment)))
    if len(multireg.reg.fields) == 1:
        regname = as_define(component + '_' + multireg.reg.name)
        gen_multireg_field_defines(outstr, regname, multireg.reg.fields[0],
                                   len(multireg.regs), regwidth, existing_defines)
    else:
        log.warn("Non-homogeneous multireg " + multireg.reg.name +
                 " skip multireg specific data generation.")

    for subreg in multireg.regs:
        gen_cdefine_register(outstr, subreg, component, regwidth, rnames,
                             existing_defines)


def gen_cdefines_interrupt_field(outstr: TextIO,
                                 interrupt: Signal,
                                 component: str,
                                 regwidth: int,
                                 existing_defines: Set[str]) -> None:
    fieldlsb = interrupt.bits.lsb
    iname = interrupt.name
    defname = as_define(component + '_INTR_COMMON_' + iname)

    if interrupt.bits.width() == 1:
        # single bit
        genout(
            outstr,
            gen_define(defname + '_BIT', [], str(fieldlsb), existing_defines))
    else:
        # multiple bits (unless it is the whole register)
        if interrupt.bits.width() != regwidth:
            mask = interrupt.bits.msb >> fieldlsb
            genout(
                outstr,
                gen_define(defname + '_MASK', [], hex(mask), existing_defines))
            genout(
                outstr,
                gen_define(defname + '_OFFSET', [], str(fieldlsb),
                           existing_defines))
            genout(
                outstr,
                gen_define(
                    defname + '_FIELD', [],
                    '((bitfield_field32_t) {{ .mask = {dname}_MASK, .index = {dname}_OFFSET }})'
                    .format(dname=defname), existing_defines))


def gen_cdefines_interrupts(outstr: TextIO,
                            block: IpBlock,
                            component: str,
                            regwidth: int,
                            existing_defines: Set[str]) -> None:
    # If no_auto_intr_regs is true, then we do not generate common defines,
    # because the bit offsets for a particular interrupt may differ between
    # the interrupt enable/state/test registers.
    if block.no_auto_intr:
        return

    genout(outstr, format_comment(first_line("Common Interrupt Offsets")))
    for intr in block.interrupts:
        gen_cdefines_interrupt_field(outstr, intr, component, regwidth,
                                     existing_defines)
    genout(outstr, '\n')


def gen_cdefines(block: IpBlock,
                 outfile: TextIO,
                 src_lic: Optional[str],
                 src_copy: str) -> int:
    rnames = block.get_rnames()

    outstr = io.StringIO()

    # This tracks the defines that have been generated so far, so we
    # can error if we attempt to duplicate a definition
    existing_defines = set()  # type: Set[str]

    gen_cdefines_module_params(outstr, block, block.name, block.regwidth,
                               existing_defines)

    gen_cdefines_interrupts(outstr, block, block.name, block.regwidth,
                            existing_defines)

    for rb in block.reg_blocks.values():
        for x in rb.entries:
            if isinstance(x, Register):
                gen_cdefine_register(outstr, x, block.name, block.regwidth, rnames,
                                     existing_defines)
                continue

            if isinstance(x, MultiRegister):
                gen_cdefine_multireg(outstr, x, block.name, block.regwidth, rnames,
                                     existing_defines)
                continue

            if isinstance(x, Window):
                gen_cdefine_window(outstr, x, block.name, block.regwidth,
                                   rnames, existing_defines)
                continue

    generated = outstr.getvalue()
    outstr.close()

    genout(outfile, '// Generated register defines for ' + block.name + '\n\n')
    if src_copy != '':
        genout(outfile, '// Copyright information found in source file:\n')
        genout(outfile, '// ' + src_copy + '\n\n')
    if src_lic is not None:
        genout(outfile, '// Licensing information found in source file:\n')
        for line in src_lic.splitlines():
            genout(outfile, '// ' + line + '\n')
        genout(outfile, '\n')

    # Header Include Guard
    genout(outfile, '#ifndef _' + as_define(block.name) + '_REG_DEFS_\n')
    genout(outfile, '#define _' + as_define(block.name) + '_REG_DEFS_\n\n')

    # Header Extern Guard (so header can be used from C and C++)
    genout(outfile, '#ifdef __cplusplus\n')
    genout(outfile, 'extern "C" {\n')
    genout(outfile, '#endif\n')

    genout(outfile, generated)

    # Header Extern Guard
    genout(outfile, '#ifdef __cplusplus\n')
    genout(outfile, '}  // extern "C"\n')
    genout(outfile, '#endif\n')

    # Header Include Guard
    genout(outfile, '#endif  // _' + as_define(block.name) + '_REG_DEFS_\n')

    genout(outfile, '// End generated register defines for ' + block.name)

    return 0


def test_gen_define() -> None:
    basic_oneline = '#define MACRO_NAME body\n'
    assert gen_define('MACRO_NAME', [], 'body', set()) == basic_oneline

    basic_oneline_with_args = '#define MACRO_NAME(arg1, arg2) arg1 + arg2\n'
    assert (gen_define('MACRO_NAME', ['arg1', 'arg2'], 'arg1 + arg2',
                       set()) == basic_oneline_with_args)

    long_macro_name = 'A_VERY_VERY_VERY_VERY_VERY_VERY_VERY_VERY_VERY_VERY_VERY_LONG_MACRO_NAME'

    multiline = ('#define ' + long_macro_name + ' \\\n' +
                 '  a_fairly_long_body + something_else + 10\n')

    assert (gen_define(long_macro_name, [],
                       'a_fairly_long_body + something_else + 10',
                       set()) == multiline)

    multiline_with_args = ('#define ' + long_macro_name +
                           '(arg1, arg2, arg3) \\\n' +
                           '  a_fairly_long_body + arg1 + arg2 + arg3\n')

    assert (gen_define(long_macro_name, ['arg1', 'arg2', 'arg3'],
                       'a_fairly_long_body + arg1 + arg2 + arg3',
                       set()) == multiline_with_args)

    multiline_with_args_big_indent = (
        '#define ' + long_macro_name + '(arg1, arg2, arg3) \\\n' +
        '    a_fairly_long_body + arg1 + arg2 + arg3\n')

    assert (gen_define(long_macro_name, ['arg1', 'arg2', 'arg3'],
                       'a_fairly_long_body + arg1 + arg2 + arg3',
                       set(),
                       indent='    ') == multiline_with_args_big_indent)
