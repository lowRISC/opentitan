# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Generate HTML documentation from IpBlock
"""

from typing import Set, TextIO

from .ip_block import IpBlock
from .html_helpers import expand_paras, render_td
from .multi_register import MultiRegister
from .reg_block import RegBlock
from .register import Register
from .window import Window


def genout(outfile: TextIO, msg: str) -> None:
    outfile.write(msg)


# Generation of HTML table with register bit-field summary picture
# Max 16-bit wide on one line


def gen_tbl_row(outfile: TextIO, msb: int, width: int, close: bool) -> None:
    if (close):
        genout(outfile, "</tr>\n")
    genout(outfile, "<tr>")
    for x in range(msb, msb - width, -1):
        genout(outfile, "<td class=\"bitnum\">" + str(x) + "</td>")

    genout(outfile, "</tr><tr>")


def gen_html_reg_pic(outfile: TextIO, reg: Register, width: int) -> None:

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

    for field in reversed(reg.fields):
        fieldlsb = field.bits.lsb
        fieldwidth = field.bits.width()
        fieldmsb = field.bits.msb
        fname = field.name

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
            fname = "..." + field.name
            fieldwidth = fieldwidth - spans
            fieldmsb = nextline - 1
            nextline = nextline - 16
            gen_tbl_row(outfile, fieldmsb, hdrbits, True)

        namelen = len(fname)
        if namelen == 0 or fname == ' ':
            fname = "&nbsp;"
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


def gen_html_register(outfile: TextIO,
                      reg: Register,
                      comp: str,
                      width: int,
                      rnames: Set[str]) -> None:
    rname = reg.name
    offset = reg.offset
    regwen_div = ''
    if reg.regwen is not None:
        regwen_div = ('    <div>Register enable = {}</div>\n'
                      .format(reg.regwen))

    desc_paras = expand_paras(reg.desc, rnames)
    desc_head = desc_paras[0]
    desc_body = desc_paras[1:]

    genout(outfile,
           '<table class="regdef" id="Reg_{lrname}">\n'
           ' <tr>\n'
           '  <th class="regdef" colspan=5>\n'
           '   <div>{comp}.{rname} @ {off:#x}</div>\n'
           '   <div>{desc}</div>\n'
           '   <div>Reset default = {resval:#x}, mask {mask:#x}</div>\n'
           '{wen}'
           '  </th>\n'
           ' </tr>\n'
           .format(lrname=rname.lower(),
                   comp=comp,
                   rname=rname,
                   off=offset,
                   desc=desc_head,
                   resval=reg.resval,
                   mask=reg.resmask,
                   wen=regwen_div))
    if desc_body:
        genout(outfile,
               '<tr><td colspan=5>{}</td></tr>'
               .format(''.join(desc_body)))

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

    for field in reg.fields:
        fcount += 1
        fname = field.name

        fieldlsb = field.bits.lsb
        if fieldlsb > nextbit:
            genout(outfile, "<tr><td class=\"regbits\">")
            if (nextbit == (fieldlsb - 1)):
                genout(outfile, str(nextbit))
            else:
                genout(outfile, str(fieldlsb - 1) + ":" + str(nextbit))
            genout(outfile,
                   "</td><td></td><td></td><td></td><td>Reserved</td></tr>")
        genout(outfile, "<tr><td class=\"regbits\">" + field.bits.as_str() + "</td>")
        genout(outfile, "<td class=\"regperm\">" + field.swaccess.key + "</td>")
        genout(
            outfile, "<td class=\"regrv\">" +
            ('x' if field.resval is None else hex(field.resval)) +
            "</td>")
        genout(outfile, "<td class=\"regfn\">" + fname + "</td>")

        # Collect up any description and enum table
        desc_parts = []

        if field.desc is not None:
            desc_parts += expand_paras(field.desc, rnames)

        if field.enum is not None:
            desc_parts.append('<table>')
            for enum in field.enum:
                enum_desc_paras = expand_paras(enum.desc, rnames)
                desc_parts.append('<tr>'
                                  '<td>{val}</td>'
                                  '<td>{name}</td>'
                                  '<td>{desc}</td>'
                                  '</tr>\n'
                                  .format(val=enum.value,
                                          name=enum.name,
                                          desc=''.join(enum_desc_paras)))
            desc_parts.append('</table>')
            if field.has_incomplete_enum():
                desc_parts.append("<p>Other values are reserved.</p>")

        genout(outfile,
               '<td class="regde">{}</td>'.format(''.join(desc_parts)))
        nextbit = fieldlsb + field.bits.width()

    genout(outfile, "</table>\n<br>\n")


def gen_html_window(outfile: TextIO,
                    win: Window,
                    comp: str,
                    regwidth: int,
                    rnames: Set[str]) -> None:
    wname = win.name or '(unnamed window)'
    offset = win.offset
    genout(outfile,
           '<table class="regdef" id="Reg_{lwname}">\n'
           '  <tr>\n'
           '    <th class="regdef">\n'
           '      <div>{comp}.{wname} @ + {off:#x}</div>\n'
           '      <div>{items} item {swaccess} window</div>\n'
           '      <div>Byte writes are {byte_writes}supported</div>\n'
           '    </th>\n'
           '  </tr>\n'
           .format(comp=comp,
                   wname=wname,
                   lwname=wname.lower(),
                   off=offset,
                   items=win.items,
                   swaccess=win.swaccess.key,
                   byte_writes=('' if win.byte_write else '<i>not</i> ')))
    genout(outfile, '<tr><td><table class="regpic">')
    genout(outfile, '<tr><td width="10%"></td>')
    wid = win.validbits

    for x in range(regwidth - 1, -1, -1):
        if x == regwidth - 1 or x == wid - 1 or x == 0:
            genout(outfile, '<td class="bitnum">' + str(x) + '</td>')
        else:
            genout(outfile, '<td class="bitnum"></td>')
    genout(outfile, '</tr>')
    tblmax = win.items - 1
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
    genout(outfile,
           '<tr>{}</tr>'.format(render_td(win.desc, rnames, 'regde')))
    genout(outfile, "</table>\n<br>\n")


def gen_html_reg_block(outfile: TextIO,
                       rb: RegBlock,
                       comp: str,
                       width: int,
                       rnames: Set[str]) -> None:
    for x in rb.entries:
        if isinstance(x, Register):
            gen_html_register(outfile, x, comp, width, rnames)
        elif isinstance(x, MultiRegister):
            for reg in x.regs:
                gen_html_register(outfile, reg, comp, width, rnames)
        else:
            assert isinstance(x, Window)
            gen_html_window(outfile, x, comp, width, rnames)


def gen_html(block: IpBlock, outfile: TextIO) -> int:
    rnames = block.get_rnames()

    assert block.reg_blocks
    # Handle the case where there's just one interface
    if len(block.reg_blocks) == 1:
        rb = list(block.reg_blocks.values())[0]
        gen_html_reg_block(outfile, rb, block.name, block.regwidth, rnames)
        return 0

    # Handle the case where there is more than one device interface and,
    # correspondingly, more than one reg block.
    for iface_name, rb in block.reg_blocks.items():
        iface_desc = ('device interface <code>{}</code>'.format(iface_name)
                      if iface_name is not None
                      else 'the unnamed device interface')
        genout(outfile,
               '<h3>Registers visible under {}</h3>'.format(iface_desc))
        gen_html_reg_block(outfile, rb, block.name, block.regwidth, rnames)

    return 0
