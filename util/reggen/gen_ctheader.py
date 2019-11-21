# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Generate C header (Titan style) from validated register JSON tree
"""

import io
import logging as log
import re
import sys


def genout(outfile, msg):
    outfile.write(msg)


def as_define(s):
    s = s.upper()
    r = ''
    for i in range(0, len(s)):
        r += s[i] if s[i].isalnum() else '_'
    return r


def clean_desc(s):
    return s.splitlines()[0]


def gen_cdefine_register(outstr, reg, comp, width, rnames):
    rname = reg['name']
    offset = reg['genoffset']

    genout(outstr, '// ' + clean_desc(reg['desc']) + '\n')
    defname = as_define(comp + '_' + rname)
    genout(
        outstr, '#define ' + defname + '(id)\t' + '(' + as_define(comp) +
        ' ## id ## _BASE_ADDR  + ' + hex(offset) + ')\n')
    genout(outstr, '#define ' + defname + '_OFFSET\t' + hex(offset) + '\n')

    for field in reg['fields']:
        fname = field['name']
        fieldlsb = field['bitinfo'][2]
        if fname == rname:
            dname = defname
        else:
            dname = defname + '_' + as_define(fname)

        # yapf: disable
        genout(outstr, '# define ' + dname + '_LSB\t' +
               hex(fieldlsb) + '\n')
        genout(outstr, '# define ' + dname + '_MASK\t' +
               hex(field['bitinfo'][0] >> fieldlsb) + '\n')
        genout(outstr, '# define ' + dname + '_SIZE\t' +
               hex(field['bitinfo'][1]) + '\n')
        genout(outstr, '# define ' + dname + '_DEFAULT\t' +
               hex(field['genresval']) + '\n')
        # yapf: enable

        if 'enum' in field:
            for enum in field['enum']:
                ename = as_define(enum['name'])
                genout(
                    outstr,
                    '# define ' + defname + '_' + as_define(field['name']) +
                    '_' + ename + '\t' + hex(int(enum['value'], 0)) + '\n')
    genout(outstr, '\n')
    return


def gen_cdefine_window(outstr, win, comp, regwidth, rnames):
    wname = win['name']
    offset = win['genoffset']

    genout(outstr, '// Memory area: ' + clean_desc(win['desc']) + '\n')
    defname = as_define(comp + '_' + wname)
    genout(
        outstr,
        '#define ' + defname + '(base)\t' + '((base) + ' + hex(offset) + ')\n')
    items = int(win['items'])
    genout(outstr, '#define ' + defname + '_SIZE_WORDS\t' + str(items) + '\n')
    items = items * (regwidth // 8)
    genout(outstr, '#define ' + defname + '_SIZE_BYTES\t' + str(items) + '\n')

    wid = win['genvalidbits']
    if (wid != regwidth):
        mask = (1 << wid) - 1
        genout(outstr, '#define ' + defname + '_MASK\t' + hex(mask) + '\n')


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

    tmax = 0
    for l in generated.splitlines():
        tpos = l.find('\t')
        if tpos > tmax:
            tmax = tpos
    for l in generated.splitlines(keepends=True):
        genout(outfile, l.expandtabs(tmax + 2))

    genout(outfile, '#endif // _' + as_define(component) + '_REG_DEFS_\n')
    genout(outfile, '//End generated register defines for ' + component)

    return
