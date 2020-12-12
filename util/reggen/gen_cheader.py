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


def gen_define(name, args, body, existing_defines, indent='  '):
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


def gen_cdefine_register(outstr, reg, comp, width, rnames, existing_defines):
    rname = reg['name']
    offset = reg['genoffset']

    genout(outstr, format_comment(first_line(reg['desc'])))
    defname = as_define(comp + '_' + rname)
    genout(
        outstr,
        gen_define(defname + '_REG_OFFSET', [], hex(offset), existing_defines))

    for field in reg['fields']:
        fieldlsb = field['bitinfo'][2]
        fname = field['name']
        dname = defname + '_' + as_define(fname)

        if field['bitinfo'][1] == 1:
            # single bit
            genout(
                outstr,
                gen_define(dname + '_BIT', [], str(fieldlsb),
                           existing_defines))
        else:
            # multiple bits (unless it is the whole register)
            if field['bitinfo'][1] != width:
                mask = field['bitinfo'][0] >> fieldlsb
                genout(
                    outstr,
                    gen_define(dname + '_MASK', [], hex(mask),
                               existing_defines))
                genout(
                    outstr,
                    gen_define(dname + '_OFFSET', [], str(fieldlsb),
                               existing_defines))
                genout(
                    outstr,
                    gen_define(
                        dname + '_FIELD', [],
                        '((bitfield_field32_t) {{ .mask = {dname}_MASK, .index = {dname}_OFFSET }})'
                        .format(dname=dname), existing_defines))
            if 'enum' in field:
                for enum in field['enum']:
                    ename = as_define(enum['name'])
                    value = hex(int(enum['value'], 0))
                    genout(
                        outstr,
                        gen_define(
                            defname + '_' + as_define(field['name']) +
                            '_VALUE_' + ename, [], value, existing_defines))
    genout(outstr, '\n')
    return


def gen_cdefine_window(outstr, win, comp, regwidth, rnames, existing_defines):
    wname = win['name']
    offset = win['genoffset']

    genout(outstr, format_comment('Memory area: ' + first_line(win['desc'])))
    defname = as_define(comp + '_' + wname)
    genout(
        outstr,
        gen_define(defname + '_REG_OFFSET', [], hex(offset), existing_defines))
    items = int(win['items'])
    genout(
        outstr,
        gen_define(defname + '_SIZE_WORDS', [], str(items), existing_defines))
    items = items * (regwidth // 8)
    genout(
        outstr,
        gen_define(defname + '_SIZE_BYTES', [], str(items), existing_defines))

    wid = win['genvalidbits']
    if (wid != regwidth):
        mask = (1 << wid) - 1
        genout(outstr,
               gen_define(defname + '_MASK ', [], hex(mask), existing_defines))


def gen_cdefines_module_param(outstr, param, module_name, existing_defines):
    param_type = param['type']

    # Do not generate C defines for parameters that are not localparams defined
    # in the corresponding SystemVerilog package.
    if param["local"].lower() == "false":
        return

    # Presently there is only one type (int), however if the new types are
    # added, they potentially need to be handled differently.
    known_types = ["int"]
    if param_type not in known_types:
        warnings.warn(
            "Cannot generate a module define of type {}".format(param_type))
        return

    genout(outstr, format_comment(first_line(param['desc'])))
    define_name = as_define(module_name + '_PARAM_' + param['name'])
    if param_type == "int":
        define = gen_define(define_name, [], param['default'],
                            existing_defines)

    genout(outstr, define)
    genout(outstr, '\n')


def gen_cdefines_module_params(outstr, module_data, module_name,
                               register_width, existing_defines):
    module_params = set()

    if 'param_list' in module_data:
        module_params = module_data['param_list']

    for param in module_params:
        gen_cdefines_module_param(outstr, param, module_name, existing_defines)

    genout(outstr, format_comment(first_line("Register width")))
    define_name = as_define(module_name + '_PARAM_REG_WIDTH')
    define = gen_define(define_name, [], str(register_width), existing_defines)
    genout(outstr, define)
    genout(outstr, '\n')


def gen_multireg_field_defines(outstr, regname, field, subreg_num, regwidth,
                               existing_defines):
    field_width = field['bitinfo'][1]
    fields_per_reg = regwidth // field_width

    define_name = regname + '_' + as_define(field['name'] + "_FIELD_WIDTH")
    define = gen_define(define_name, [], str(field_width), existing_defines)
    genout(outstr, define)

    define_name = regname + '_' + as_define(field['name'] + "_FIELDS_PER_REG")
    define = gen_define(define_name, [], str(fields_per_reg), existing_defines)
    genout(outstr, define)

    define_name = regname + "_MULTIREG_COUNT"
    define = gen_define(define_name, [], str(subreg_num), existing_defines)
    genout(outstr, define)

    genout(outstr, '\n')


def gen_cdefine_multireg(outstr, register, component, regwidth, rnames,
                         existing_defines):
    multireg = register['multireg']
    subregs = multireg['genregs']

    comment = multireg['desc'] + " (common parameters)"
    genout(outstr, format_comment(first_line(comment)))
    if len(multireg['fields']) == 1:
        regname = as_define(component + '_' + multireg['name'])
        gen_multireg_field_defines(outstr, regname, multireg['fields'][0],
                                   len(subregs), regwidth, existing_defines)
    else:
        log.warn("Non-homogeneous multireg " + multireg['name'] +
                 " skip multireg specific data generation.")

    for subreg in subregs:
        gen_cdefine_register(outstr, subreg, component, regwidth, rnames,
                             existing_defines)


def gen_cdefines_interrupt_field(outstr, interrupt, component, regwidth,
                                 existing_defines):
    fieldlsb = interrupt['bitinfo'][2]
    iname = interrupt['name']
    defname = as_define(component + '_INTR_COMMON_' + iname)

    if interrupt['bitinfo'][1] == 1:
        # single bit
        genout(
            outstr,
            gen_define(defname + '_BIT', [], str(fieldlsb), existing_defines))
    else:
        # multiple bits (unless it is the whole register)
        if interrupt['bitinfo'][1] != regwidth:
            mask = interrupt['bitinfo'][0] >> fieldlsb
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


def gen_cdefines_interrupts(outstr, regs, component, regwidth,
                            existing_defines):
    # no_auto_intr_regs controls whether interrupt registers are automatically
    # generated from the interrupt_list. This key could be 'true' or 'false',
    # but might also be True or False (the python booleans).
    no_auto_i = False
    if 'no_auto_intr_regs' in regs:
        no_auto_intr_regs_val = regs['no_auto_intr_regs']
        if isinstance(no_auto_intr_regs_val, bool):
            no_auto_i = no_auto_intr_regs_val
        elif no_auto_intr_regs_val.lower() in ["true", "false"]:
            no_auto_i = no_auto_intr_regs_val == "true"
        else:
            pass

    # If no_auto_intr_regs is true, then we do not generate common defines,
    # because the bit offsets for a particular interrupt may differ between
    # the interrupt enable/state/test registers.
    if no_auto_i:
        return

    interrupts = regs.get('interrupt_list', [])
    genout(outstr, format_comment(first_line("Common Interrupt Offsets")))
    for intr in interrupts:
        gen_cdefines_interrupt_field(outstr, intr, component, regwidth,
                                     existing_defines)
    genout(outstr, '\n')


# Must have called validate, so should have no errors
def gen_cdefines(regs, outfile, src_lic, src_copy):
    component = regs['name']
    registers = regs['registers']
    rnames = regs['genrnames']
    outstr = io.StringIO()

    # This tracks the defines that have been generated so far, so we
    # can error if we attempt to duplicate a definition
    existing_defines = set()

    if 'regwidth' in regs:
        regwidth = int(regs['regwidth'], 0)
    else:
        regwidth = 32

    gen_cdefines_module_params(outstr, regs, component, regwidth,
                               existing_defines)

    gen_cdefines_interrupts(outstr, regs, component, regwidth,
                            existing_defines)

    for x in registers:
        if 'reserved' in x:
            continue

        if 'skipto' in x:
            continue

        if 'sameaddr' in x:
            for sareg in x['sameaddr']:
                gen_cdefine_register(outstr, sareg, component, regwidth,
                                     rnames, existing_defines)
            continue

        if 'window' in x:
            gen_cdefine_window(outstr, x['window'], component, regwidth,
                               rnames, existing_defines)
            continue

        if 'multireg' in x:
            gen_cdefine_multireg(outstr, x, component, regwidth, rnames,
                                 existing_defines)
            continue

        gen_cdefine_register(outstr, x, component, regwidth, rnames,
                             existing_defines)

    generated = outstr.getvalue()
    outstr.close()

    genout(outfile, '// Generated register defines for ' + component + '\n\n')
    if src_copy != '':
        genout(outfile, '// Copyright information found in source file:\n')
        genout(outfile, '// ' + src_copy + '\n\n')
    if src_lic is not None:
        genout(outfile, '// Licensing information found in source file:\n')
        for line in src_lic.splitlines():
            genout(outfile, '// ' + line + '\n')
        genout(outfile, '\n')

    # Header Include Guard
    genout(outfile, '#ifndef _' + as_define(component) + '_REG_DEFS_\n')
    genout(outfile, '#define _' + as_define(component) + '_REG_DEFS_\n\n')

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
    genout(outfile, '#endif  // _' + as_define(component) + '_REG_DEFS_\n')

    genout(outfile, '// End generated register defines for ' + component)

    return


def test_gen_define():
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
