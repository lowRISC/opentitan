# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Generate HTML documentation from IpBlock
"""

from typing import Optional, Set, TextIO, List, Union

import mistletoe as mk

from reggen.ip_block import IpBlock
from reggen.html_helpers import expand_paras, render_td, get_reg_link
from reggen.multi_register import MultiRegister
from reggen.reg_block import RegBlock
from reggen.register import Register
from reggen.window import Window


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


def gen_html_register_summary(outfile: TextIO, obj_list: List[Union[Window,
                                                                    Register]],
                              comp: str, width: int, rnames: Set[str]) -> None:

    bytew = width // 8
    genout(
        outfile, '<table class="regdef" id="RegSummary_{comp}">\n'
        ' <tr>\n'
        '  <th class="regdef" colspan=4> Summary </th>\n'
        ' </tr>\n'
        ' <tr>\n'
        '  <th class="regdef">Name</th>'
        '  <th class="regdef">Offset</th>'
        '  <th class="regdef">Length</th>'
        '  <th class="regdef">Description</th>'
        ' </tr>\n')

    for obj in obj_list:
        obj_length = bytew if isinstance(obj, Register) else bytew * obj.items
        desc_paras = expand_paras(obj.desc, rnames)
        obj_desc = desc_paras[0]

        genout(
            outfile, ' <tr>\n'
            f'  <td class="regfn">{comp}.{get_reg_link(obj.name)}</td>'
            f'  <td class="regfn">{obj.offset:#x}</td>'
            f'  <td class="regfn">{obj_length}</td>'
            f'  <td class="regfn">{obj_desc}</td>'
            ' </tr>\n')

    genout(outfile, '</table>')


def gen_html_register(outfile: TextIO, reg: Register, comp: str, width: int,
                      rnames: Set[str]) -> None:
    rname = reg.name
    offset = reg.offset
    resval = reg.resval
    resmask = reg.resmask
    regwen_div = ''
    if reg.regwen is not None:
        regwen_div = f'    <div>Register enable = {reg.regwen}</div>'

    desc_paras = expand_paras(reg.desc, rnames)
    desc_head = desc_paras[0]
    desc_body = desc_paras[1:]

    # If this is the first register of a multireg,
    # we also insert a label without the index so
    # that unnumbered links from the register table
    # descriptions and Hugo-generated docs are possible.
    if rname[-2:] == "0":
        mr_anchor = f'id="{rname[:-2].lower()}"'
    else:
        mr_anchor = ''

    genout(
        outfile, f'<table class="regdef" id="{rname.lower()}">\n'
        ' <tr>\n'
        f'  <th class="regdef" colspan=5 {mr_anchor}>\n'
        f'   <div>{comp}.{get_reg_link(rname)} @ {offset:#x}</div>\n'
        f'   <div>{desc_head}</div>\n'
        f'   <div>Reset default = {resval:#x}, mask {resmask:#x}</div>\n'
        f'{regwen_div}'
        '  </th>\n'
        ' </tr>\n')
    if desc_body:
        genout(outfile,
               f'<tr><td colspan=5>{mk.markdown(desc_body)}</td></tr>')

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
        genout(outfile,
               "<tr><td class=\"regbits\">" + field.bits.as_str() + "</td>")
        genout(outfile,
               "<td class=\"regperm\">" + field.swaccess.key + "</td>")
        genout(
            outfile, "<td class=\"regrv\">" +
            ('x' if field.resval is None else hex(field.resval)) + "</td>")
        genout(outfile, "<td class=\"regfn\">" + fname + "</td>")

        # Collect up any description and enum table
        desc_parts = []

        if field.desc is not None:
            desc_parts += expand_paras(mk.markdown(field.desc), rnames)

        if field.enum is not None:
            desc_parts.append('<table>')

            # Add two to include the "0x" part
            hex_width = 2 + ((field.bits.width() + 3) // 4)

            for enum in field.enum:
                val = enum.value
                enum_desc_paras = expand_paras(enum.desc, rnames)
                desc_parts.append('<tr>'
                                  f'<td>{val}:#0{hex_width}x</td>'
                                  f'<td>{enum.name}</td>'
                                  f'<td>{"".join(enum_desc_paras)}</td>'
                                  '</tr>\n')
            desc_parts.append('</table>')
            if field.has_incomplete_enum():
                desc_parts.append("<p>Other values are reserved.</p>")

        genout(outfile,
               '<td class="regde">{}</td>'.format(''.join(desc_parts)))
        nextbit = fieldlsb + field.bits.width()

    genout(outfile, "</table>\n<br>\n")


def gen_window_row(outfile: TextIO, base_addr: int, validbits: int,
                   regwidth: int, idx: Optional[int]) -> None:
    '''Generate a row for a window

    If idx is None, this is a row that shows we're skipping some addresses and
    has a "...". If idx is not None, this gives an address and we show the bits
    that are valid.
    '''
    assert 0 < validbits
    assert 0 < regwidth
    assert regwidth % 8 == 0
    assert validbits <= regwidth

    if idx is not None:
        assert idx >= 0
        addr = base_addr + idx * (regwidth // 8)
        addr_td = f'<td class="regbits">+{addr:#x}</td>'
        if validbits < regwidth:
            pad = regwidth - validbits
            unused_tds = f'<td class="unused" colspan="{pad}">&nbsp;</td>'
        else:
            unused_tds = ''
        data_tds = f'<td class="fname" colspan="{validbits}">&nbsp;</td>'
        tds = addr_td + unused_tds + data_tds
    else:
        tds = (f'<td>&nbsp;</td>'
               f'<td align="center" colspan="{regwidth}">...</td>')

    genout(outfile, f'<tr>{tds}</tr>')


def gen_html_window(outfile: TextIO, win: Window, comp: str, regwidth: int,
                    rnames: Set[str]) -> None:
    wname = win.name or '(unnamed window)'
    offset = win.offset
    byte_writes = '' if win.byte_write else '<i>not</i> '
    genout(
        outfile, f'<table class="regdef" id="{wname.lower()}">\n'
        '  <tr>\n'
        '    <th class="regdef">\n'
        f'      <div>{comp}.{get_reg_link(wname)} @ + {offset:#x}</div>\n'
        f'      <div>{win.items} item {win.swaccess.key} window</div>\n'
        f'      <div>Byte writes are {byte_writes}supported</div>\n'
        '    </th>\n'
        '  </tr>\n')
    genout(outfile, '<tr><td><table class="regpic">')
    genout(outfile, '<tr><td width="10%"></td>')
    wid = win.validbits

    for x in range(regwidth - 1, -1, -1):
        if x == regwidth - 1 or x == wid - 1 or x == 0:
            genout(outfile, '<td class="bitnum">' + str(x) + '</td>')
        else:
            genout(outfile, '<td class="bitnum"></td>')
    genout(outfile, '</tr>')

    # We want to show the first and last two addresses, with a blank line in
    # between if we skip anything.
    assert win.items >= 1
    if win.items <= 4:
        indices_0 = list(range(win.items))
        indices_1 = []
    else:
        indices_0 = [0, 1]
        indices_1 = [win.items - 2, win.items - 1]

    for idx in indices_0:
        gen_window_row(outfile, offset, win.validbits, regwidth, idx)
    if indices_1:
        gen_window_row(outfile, offset, win.validbits, regwidth, None)
    for idx in indices_1:
        gen_window_row(outfile, offset, win.validbits, regwidth, idx)

    genout(outfile, '</td></tr></table>')
    genout(outfile, '<tr>{}</tr>'.format(render_td(win.desc, rnames, 'regde')))
    genout(outfile, "</table>\n<br>\n")


def gen_html_reg_block(outfile: TextIO, rb: RegBlock, comp: str, width: int,
                       rnames: Set[str]) -> None:
    if len(rb.entries) == 0:
        genout(outfile, 'This interface does not expose any registers.')
    else:
        # Generate overview table first.
        obj_list: List[Union[Register, Window]] = []
        for x in rb.entries:
            if isinstance(x, MultiRegister):
                for reg in x.cregs:
                    obj_list += [reg]
            else:
                assert isinstance(x, Window) or isinstance(x, Register)
                obj_list += [x]
        gen_html_register_summary(outfile, obj_list, comp, width, rnames)

        # Generate detailed entries
        for x in rb.entries:
            if isinstance(x, Register):
                gen_html_register(outfile, x, comp, width, rnames)
            elif isinstance(x, MultiRegister):
                for reg in x.cregs:
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
                      if iface_name is not None else
                      'the unnamed device interface')
        genout(outfile,
               '<h3>Registers visible under {}</h3>'.format(iface_desc))
        gen_html_reg_block(outfile, rb, block.name, block.regwidth, rnames)

    return 0
