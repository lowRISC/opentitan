# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Generate C header from validated register JSON tree
"""

import io
import logging as log
import re
import sys
import textwrap


def genout(outfile, msg):
    outfile.write(msg)


def as_define(s):
    s = s.upper()
    r = ''
    for i in range(0, len(s)):
        r += s[i] if s[i].isalnum() else '_'
    return r


def first_line(s):
    """Returns the first line of a multi-line string"""
    return s.splitlines()[0]


def format_comment(s):
    """Formats a string to comment wrapped to an 80 character line width

    Returns wrapped string including newline and // comment characters.
    """
    return '\n'.join(
        textwrap.wrap(
            s, width=77, initial_indent='// ', subsequent_indent='// ')) + '\n'


def gen_define(name, args, body, indent='  '):
    r"""Produces a #define string, will split into two lines if a single line
    has a width greater than 80 characters. Result includes newline.

    Arguments:
    name - Name of the #define
    args - List of arguments for the define, provide an empty list if there are
    none
    body - Body of the #define
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
    if len(args) != 0:
        define_declare = '#define ' + name + '(' + ', '.join(args) + ')'
    else:
        define_declare = '#define ' + name

    oneline_define = define_declare + ' ' + body

    if len(oneline_define) <= 80:
        return oneline_define + '\n'

    return define_declare + ' \\\n' + indent + body + '\n'


def gen_cdefine_register(outstr, reg, comp, width, rnames):
    rname = reg['name']
    offset = reg['genoffset']

    genout(outstr, format_comment(first_line(reg['desc'])))
    defname = as_define(comp + '_' + rname)
    genout(
        outstr,
        gen_define(
            defname, ['id'],
            '(' + as_define(comp) + '##id##_BASE_ADDR + ' + hex(offset) + ')'))
    genout(outstr, gen_define(defname + '_REG_OFFSET', [], hex(offset)))

    for field in reg['fields']:
        fieldlsb = field['bitinfo'][2]
        fname = field['name']
        if fname == rname:
            dname = defname
        else:
            dname = defname + '_' + as_define(fname)

        if field['bitinfo'][1] == 1:
            # single bit
            genout(outstr, gen_define(dname, [], str(fieldlsb)))
        else:
            # multiple bits (unless it is the whole register)
            if field['bitinfo'][1] != width:
                mask = field['bitinfo'][0] >> fieldlsb
                genout(outstr, gen_define(dname + '_MASK', [], hex(mask)))
                genout(outstr, gen_define(dname + '_OFFSET', [],
                                          str(fieldlsb)))
            if 'enum' in field:
                for enum in field['enum']:
                    ename = as_define(enum['name'])
                    genout(
                        outstr,
                        gen_define(
                            defname + '_' + as_define(field['name']) + '_' +
                            ename, [], enum['value']))
    genout(outstr, '\n')
    return


def gen_cdefine_window(outstr, win, comp, regwidth, rnames):
    wname = win['name']
    offset = win['genoffset']

    genout(outstr, format_comment('Memory area: ' + first_line(win['desc'])))
    defname = as_define(comp + '_' + wname)
    genout(
        outstr,
        gen_define(
            defname, ['id'],
            '(' + as_define(comp) + '##id##_BASE_ADDR + ' + hex(offset) + ')'))
    genout(outstr, gen_define(defname + '_REG_OFFSET', [], hex(offset)))
    items = int(win['items'])
    genout(outstr, gen_define(defname + '_SIZE_WORDS', [], str(items)))
    items = items * (regwidth // 8)
    genout(outstr, gen_define(defname + '_SIZE_BYTES', [], str(items)))

    wid = win['genvalidbits']
    if (wid != regwidth):
        mask = (1 << wid) - 1
        genout(outstr, gen_define(defname + '_MASK ', [], hex(mask)))


# Must have called validate, so should have no errors


def gen_cdefines(regs, outfile, src_lic, src_copy):
    component = regs['name']
    registers = regs['registers']
    rnames = regs['genrnames']
    outstr = io.StringIO()

    if 'regwidth' in regs:
        regwidth = int(regs['regwidth'], 0)
    else:
        regwidth = 32

    for x in registers:
        if 'reserved' in x:
            continue

        if 'skipto' in x:
            continue

        if 'sameaddr' in x:
            for sareg in x['sameaddr']:
                gen_cdefine_register(outstr, sareg, component, regwidth,
                                     rnames)
            continue

        if 'window' in x:
            gen_cdefine_window(outstr, x['window'], component, regwidth,
                               rnames)
            continue

        if 'multireg' in x:
            for reg in x['multireg']['genregs']:
                gen_cdefine_register(outstr, reg, component, regwidth, rnames)
            continue

        gen_cdefine_register(outstr, x, component, regwidth, rnames)

    generated = outstr.getvalue()
    outstr.close()

    genout(outfile, '// Generated register defines for ' + component + '\n\n')
    if src_copy != '':
        genout(outfile, '// Copyright information found in source file:\n')
        genout(outfile, '// ' + src_copy + '\n\n')
    if src_lic != None:
        genout(outfile, '// Licensing information found in source file:\n')
        for line in src_lic.splitlines():
            genout(outfile, '// ' + line + '\n')
        genout(outfile, '\n')
    genout(outfile, '#ifndef _' + as_define(component) + '_REG_DEFS_\n')
    genout(outfile, '#define _' + as_define(component) + '_REG_DEFS_\n\n')
    genout(outfile, generated)
    genout(outfile, '#endif  // _' + as_define(component) + '_REG_DEFS_\n')
    genout(outfile, '// End generated register defines for ' + component)

    return


def test_gen_define():
    basic_oneline = '#define MACRO_NAME body\n'
    assert gen_define('MACRO_NAME', [], 'body') == basic_oneline

    basic_oneline_with_args = '#define MACRO_NAME(arg1, arg2) arg1 + arg2\n'
    assert (gen_define('MACRO_NAME', ['arg1', 'arg2'],
                       'arg1 + arg2') == basic_oneline_with_args)

    long_macro_name = 'A_VERY_VERY_VERY_VERY_VERY_VERY_VERY_VERY_VERY_VERY_VERY_LONG_MACRO_NAME'

    multiline = ('#define ' + long_macro_name + ' \\\n' +
                 '  a_fairly_long_body + something_else + 10\n')

    assert (gen_define(
        long_macro_name, [],
        'a_fairly_long_body + something_else + 10') == multiline)

    multiline_with_args = ('#define ' + long_macro_name +
                           '(arg1, arg2, arg3) \\\n' +
                           '  a_fairly_long_body + arg1 + arg2 + arg3\n')

    assert (gen_define(
        long_macro_name, ['arg1', 'arg2', 'arg3'],
        'a_fairly_long_body + arg1 + arg2 + arg3') == multiline_with_args)

    multiline_with_args_big_indent = (
        '#define ' + long_macro_name + '(arg1, arg2, arg3) \\\n' +
        '    a_fairly_long_body + arg1 + arg2 + arg3\n')

    assert (gen_define(long_macro_name, ['arg1', 'arg2', 'arg3'],
                       'a_fairly_long_body + arg1 + arg2 + arg3',
                       indent='    ') == multiline_with_args_big_indent)
