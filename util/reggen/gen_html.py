# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Generate HTML documentation from validated register Hjson tree
"""

import logging as log
import re
import sys


def genout(outfile, msg):
    outfile.write(msg)


# expand !!register references into HTML links, gen **bold** and *italic*
def desc_expand(s, rnames):
    def fieldsub(match):
        base = match.group(1).partition('.')[0].lower()
        if base in rnames:
            if match.group(1)[-1] == ".":
                return ('<a href="#Reg_' + base + '"><code class=\"reg\">' +
                        match.group(1)[:-1] + '</code></a>.')
            else:
                return ('<a href="#Reg_' + base + '"><code class=\"reg\">' +
                        match.group(1) + '</code></a>')
        log.warn('!!' + match.group(1).partition('.')[0] +
                 ' not found in register list.')
        return match.group(0)

    s = re.sub(r"!!([A-Za-z0-9_.]+)", fieldsub, s)
    s = re.sub(r"(?s)\*\*(.+?)\*\*", r'<B>\1</B>', s)
    s = re.sub(r"\*([^*]+?)\*", r'<I>\1</I>', s)
    return s


# Generation of HTML table with register bit-field summary picture
# Max 16-bit wide on one line


def gen_tbl_row(outfile, msb, width, close):
    if (close):
        genout(outfile, "</tr>\n")
    genout(outfile, "<tr>")
    for x in range(msb, msb - width, -1):
        genout(outfile, "<td class=\"bitnum\">" + str(x) + "</td>")

    genout(outfile, "</tr><tr>")


def gen_html_reg_pic(outfile, reg, width):

    if (width > 32):
        bsize = 3
        nextbit = 63
        hdrbits = 16
        nextline = 48
    elif (width > 16):
        bsize = 3
        nextbit = 31
        hdrbits = 16
        nextline = 16
    elif (width > 8):
        bsize = 3
        nextbit = 15
        nextline = 0
        hdrbits = 16
    else:
        bsize = 12
        nextbit = 7
        nextline = 0
        hdrbits = 8

    genout(outfile, "<table class=\"regpic\">")
    gen_tbl_row(outfile, nextbit, hdrbits, False)

    for field in reversed(reg['fields']):
        fieldlsb = field['bitinfo'][2]
        fieldwidth = field['bitinfo'][1]
        fieldmsb = fieldlsb + fieldwidth - 1
        fname = field['name']

        while nextbit > fieldmsb:
            if (nextbit >= nextline) and (fieldmsb < nextline):
                spans = nextbit - (nextline - 1)
            else:
                spans = nextbit - fieldmsb
            genout(
                outfile, "<td class=\"unused\" colspan=" + str(spans) +
                ">&nbsp;</td>\n")
            if (nextbit >= nextline) and (fieldmsb < nextline):
                nextbit = nextline - 1
                gen_tbl_row(outfile, nextbit, hdrbits, True)
                nextline = nextline - 16
            else:
                nextbit = fieldmsb

        while (fieldmsb >= nextline) and (fieldlsb < nextline):
            spans = fieldmsb - (nextline - 1)
            genout(
                outfile, "<td class=\"fname\" colspan=" + str(spans) + ">" +
                fname + "...</td>\n")
            fname = "..." + field['name']
            fieldwidth = fieldwidth - spans
            fieldmsb = nextline - 1
            nextline = nextline - 16
            gen_tbl_row(outfile, fieldmsb, hdrbits, True)

        namelen = len(fname)
        if namelen == 0 or fname == ' ': fname = "&nbsp;"
        if (namelen > bsize * fieldwidth):
            usestyle = (" style=\"font-size:" + str(
                (bsize * 100 * fieldwidth) / namelen) + "%\"")
        else:
            usestyle = ""

        genout(
            outfile, "<td class=\"fname\" colspan=" + str(fieldwidth) +
            usestyle + ">" + fname + "</td>\n")

        if (fieldlsb == nextline) and nextline > 0:
            gen_tbl_row(outfile, nextline - 1, hdrbits, True)
            nextline = nextline - 16

        nextbit = fieldlsb - 1
    while (nextbit > 0):
        spans = nextbit - (nextline - 1)
        genout(outfile,
               "<td class=\"unused\" colspan=" + str(spans) + ">&nbsp;</td>\n")
        nextbit = nextline - 1
        if (nextline > 0):
            gen_tbl_row(outfile, nextline - 1, hdrbits, True)
            nextline = nextline - 16

    genout(outfile, "</tr></table>")


# Generation of HTML table with header, register picture and details


def gen_html_register(outfile, reg, comp, width, rnames, toc, toclvl):
    def gen_merge(outfile, fieldlsb, mergebase, mergeprev, mergedesc):
        genout(
            outfile, "<tr><td class=\"regbits\">" + str(fieldlsb - 1) + ':' +
            str(mergebase) + "</td>")
        genout(outfile, "<td class=\"regperm\"></td>")
        genout(outfile, "<td class=\"regrv\"></td>")
        genout(outfile, "<td class=\"regfn\"></td>")
        if mergeprev != mergedesc:
            genout(outfile,
                   "<td class=\"regde\">" + mergedesc + ".." + mergeprev[4:])
        else:
            genout(outfile, "<td class=\"regde\">" + mergedesc)
        genout(outfile, "</td></tr>\n")

    rname = reg['name']
    offset = reg['genoffset']
    #in a multireg with multiple regs give anchor with base register name
    if 'genbasebits' in reg and rname[-1] == '0':
        genout(outfile, "<div id=\"Reg_" + rname[:-1].lower() + "\"></div>\n")
    regwen_string = ''
    if 'regwen' in reg and (reg['regwen'] != ''):
        regwen_string = '<br>Register enable = ' + reg['regwen']
    genout(
        outfile, "<table class=\"regdef\" id=\"Reg_" + rname.lower() + "\">\n"
        "<tr><th class=\"regdef\" colspan=5><div>" + comp + "." + rname +
        " @ + " + hex(offset) + "</div><div>" +
        desc_expand(reg['desc'], rnames) + "</div>" + "<div>Reset default = " +
        hex(reg['genresval']) + ", mask " + hex(reg['genresmask']) +
        regwen_string + "</div></th></tr>\n")
    if toc != None:
        toc.append((toclvl, comp + "." + rname, "Reg_" + rname.lower()))
    genout(outfile, "<tr><td colspan=5>")
    gen_html_reg_pic(outfile, reg, width)
    genout(outfile, "</td></tr>\n")

    genout(outfile, "<tr><th width=5%>Bits</th>")
    genout(outfile, "<th width=5%>Type</th>")
    genout(outfile, "<th width=5%>Reset</th>")
    genout(outfile, "<th>Name</th>")
    genout(outfile, "<th>Description</th></tr>")
    nextbit = 0
    fcount = 0
    mergebase = -1
    for field in reg['fields']:
        fcount += 1
        if not 'name' in field:
            fname = "field " + str(fcount)
        else:
            fname = field['name']

        fieldlsb = field['bitinfo'][2]
        if (fieldlsb > nextbit) and mergebase < 0:
            genout(outfile, "<tr><td class=\"regbits\">")
            if (nextbit == (fieldlsb - 1)):
                genout(outfile, str(nextbit))
            else:
                genout(outfile, str(fieldlsb - 1) + ":" + str(nextbit))
            genout(outfile,
                   "</td><td></td><td></td><td></td><td>Reserved</td></tr>")
        if 'genbasebits' in reg:
            if (((1 << fieldlsb) & reg['genbasebits']) == 0):
                mergeprev = field['desc']
                if (mergebase < 0):
                    mergebase = fieldlsb
                    mergedesc = field['desc']
                nextbit = fieldlsb + field['bitinfo'][1]
                continue
            else:
                if (mergebase >= 0):
                    gen_merge(outfile, fieldlsb, mergebase, mergeprev,
                              mergedesc)
                    mergebase = -1
        genout(outfile, "<tr><td class=\"regbits\">" + field['bits'] + "</td>")
        genout(outfile, "<td class=\"regperm\">" + field['swaccess'] + "</td>")
        genout(
            outfile, "<td class=\"regrv\">" +
            ('x' if field['genresvalx'] else hex(field['genresval'])) +
            "</td>")
        genout(outfile, "<td class=\"regfn\">" + fname + "</td>")
        if 'desc' in field:
            genout(
                outfile, "<td class=\"regde\">" +
                desc_expand(field['desc'], rnames) + "\n")
        else:
            genout(outfile, "<td>\n")

        if 'enum' in field:
            genout(outfile, "    <table>")
            for enum in field['enum']:
                if (not 'name' in enum):
                    ename = "enum for " + fname + " in " + rname
                else:
                    ename = enum['name']
                genout(outfile, "    <tr><td>" + enum['value'] + "</td>")
                genout(outfile, "<td>" + ename + "</td>")
                genout(
                    outfile, "<td>" + desc_expand(enum['desc'], rnames) +
                    "</td></tr>\n")

            genout(outfile, "    </table>")
            if 'genrsvdenum' in field:
                genout(outfile, "Other values are reserved.")
        genout(outfile, "</td></tr>\n")
        nextbit = fieldlsb + field['bitinfo'][1]

    # could be in the middle of a merge
    if (mergebase >= 0):
        gen_merge(outfile, nextbit, mergebase, mergeprev, mergedesc)

    genout(outfile, "</table>\n<br><br>\n")

    return


def gen_html_window(outfile, win, comp, regwidth, rnames, toc, toclvl):
    wname = win['name']
    offset = win['genoffset']
    genout(
        outfile, '<table class="regdef" id="Reg_' + wname.lower() + '">\n'
        '<tr><th class="regdef"><div>' + comp + '.' + wname + ' @ + ' +
        hex(offset) + '</div><div>' + win['items'] + ' item ' +
        win['swaccess'] + ' window</div><div>Byte writes are ' +
        ('' if win['genbyte-write'] else '<i>not</i> ') +
        'supported</div></th></tr>\n')
    genout(outfile, '<tr><td><table class="regpic">')
    genout(outfile, '<tr><td width="10%"></td>')
    wid = win['genvalidbits']

    for x in range(regwidth - 1, -1, -1):
        if x == regwidth - 1 or x == wid - 1 or x == 0:
            genout(outfile, '<td class="bitnum">' + str(x) + '</td>')
        else:
            genout(outfile, '<td class="bitnum"></td>')
    genout(outfile, '</tr>')
    tblmax = int(win['items']) - 1
    for x in [0, 1, 2, tblmax - 1, tblmax]:
        if x == 2:
            genout(
                outfile, '<tr><td>&nbsp;</td><td align=center colspan=' +
                str(regwidth) + '>...</td></tr>')
        else:
            genout(
                outfile, '<tr><td class="regbits">+' +
                hex(offset + x * (regwidth // 8)) + '</td>')
            if wid < regwidth:
                genout(
                    outfile, '<td class="unused" colspan=' +
                    str(regwidth - wid) + '>&nbsp;</td>\n')
                genout(
                    outfile,
                    '<td class="fname" colspan=' + str(wid) + '>&nbsp;</td>\n')
            else:
                genout(
                    outfile, '<td class="fname" colspan=' + str(regwidth) +
                    '>&nbsp;</td>\n')
            genout(outfile, '</tr>')
    genout(outfile, '</td></tr></table>')
    genout(
        outfile, '<tr><td class="regde">' + desc_expand(win['desc'], rnames) +
        '</td></tr>')
    genout(outfile, "</table>\n<br><br>\n")
    if toc != None:
        toc.append((toclvl, comp + "." + wname, "Reg_" + wname.lower()))


# Must have called validate, so should have no errors


def gen_html(regs, outfile, toclist=None, toclevel=3):
    component = regs['name']
    registers = regs['registers']
    rnames = regs['genrnames']

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
                gen_html_register(outfile, sareg, component, regwidth, rnames,
                                  toclist, toclevel)
            continue

        if 'window' in x:
            gen_html_window(outfile, x['window'], component, regwidth, rnames,
                            toclist, toclevel)
            continue

        if 'multireg' in x:
            for reg in x['multireg']['genregs']:
                gen_html_register(outfile, reg, component, regwidth, rnames,
                                  toclist, toclevel)
            continue

        gen_html_register(outfile, x, component, regwidth, rnames, toclist,
                          toclevel)
    return
