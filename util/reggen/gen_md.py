# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Generate Markdown documentation from IpBlock
"""

from typing import List, Optional, Set, TextIO, Union

import mistletoe as mk
from reggen.ip_block import IpBlock
from reggen.md_helpers import (bold, coderef, expand_paras, get_reg_link,
                               italic, md_safe_for_table, render_td, table,
                               title, url, wavejson)
from reggen.multi_register import MultiRegister
from reggen.reg_block import RegBlock
from reggen.register import Register
from reggen.window import Window


def genout(outfile: TextIO, msg: str) -> None:
    outfile.write(msg)

def gen_md_reg_picture(outfile: TextIO, reg: Register, width: int) -> str:
    # We use WaveDrom to generate the register since we already have a wavejson preprocessor,
    # we just output a wavejson block
    # bit-field is great but has some flaws that make it hard to draw nice
    # picture. Notably, it does not automatically rotate fields that don't fit
    # or increase the vertical space if necessary.
    # As the result, the following code makes some assumptions to decide when to rotate and
    # to compute the vertical space. Furthermore, we do not know the horizontal size so
    # we have to fix it, which mean that the final result might be rescaled on the page
    hspace = 640
    vspace = 80
    fontsize = 14
    lanes = 1
    margin = 10  # margin around text
    # estimated size that a character takes
    font_adv = 16
    # size of each bit in the picture
    bit_width = hspace * lanes / width

    fields = []
    next_bit = 0
    for field in reg.fields:
        fieldlsb = field.bits.lsb
        # add an empty field if necessary
        if fieldlsb > next_bit:
            fields.append({"bits": fieldlsb - next_bit})
        # we need to decide whether to rotate or not
        # compute the size needed to draw
        need_space = font_adv * len(field.name) + 2 * margin
        # if this too large horizontally, rotate
        # FIXME this does not account for splitting accross lanes
        rotate = 0
        if need_space > bit_width * field.bits.width():
            rotate = -90
            # increase vertical space if needed
            vspace = max(vspace, need_space)

        fields.append({
            "name": field.name,
            "bits": field.bits.width(),
            "attr": [field.swaccess.key],
            "rotate": rotate
        })
        next_bit = field.bits.msb + 1
    # add an empty field if necessary
    if width > next_bit:
        fields.append({"bits": width - next_bit})
    # wavedrom configuration, see https://github.com/wavedrom/bitfield
    config = {"lanes": lanes, "fontsize": fontsize, "vspace": vspace}
    genout(outfile, wavejson({"reg": fields, "config": config}))


# Generation of markdown table with header, register picture and details
def gen_kv(outfile: TextIO, key: str, value: str) -> None:
    genout(outfile, f'- {key}: {value}\n')


def gen_md_register_summary(outfile: TextIO, obj_list: List[Union[Window,
                                                                  Register]],
                            comp: str, width: int, rnames: Set[str]) -> None:

    bytew = width // 8
    genout(outfile, title("Summary", 4))

    header = ["Name", "Offset", "Length", "Description"]
    rows = []

    for obj in obj_list:
        obj_length = bytew if isinstance(obj, Register) else bytew * obj.items
        desc_paras = expand_paras(obj.desc, rnames)
        obj_desc = desc_paras[0]
        rows.append([
            f"{comp}.{get_reg_link(obj.name)}", f"{obj.offset:#x}",
            f"{obj_length}", f"{obj_desc}"
        ])

    genout(outfile, table(header, rows))


def gen_md_register(outfile: TextIO, reg: Register, comp: str, width: int,
                    rnames: Set[str]) -> None:
    rname = reg.name
    desc_paras = expand_paras(reg.desc, rnames)
    desc_head = desc_paras[0]
    desc_body = desc_paras[1:]

    genout(outfile, title(rname, 4))
    genout(outfile, desc_head)
    genout(outfile, "\n")
    header = ["Offset", "Reset default", "Reset mask"]
    row = [f"{reg.offset:#x}", f"{reg.resval:#x}", f"{reg.resmask:#x}"]
    colalign = ["center", "center", "center"]
    if reg.regwen is not None:
        header.append("Register enable")
        row.append(f"{get_reg_link(reg.regwen)}")
        colalign.append("center")
    genout(outfile, table(header, [row], colalign))
    genout(outfile, "\n")
    for p in desc_body:
        genout(outfile, p)
        genout(outfile, "\n")
    # generate bit-field pictur
    gen_md_reg_picture(outfile, reg, width)

    # If this is the first register of a multireg,
    # we also insert a label without the index so
    # that unnumbered links from the register table
    # descriptions and Hugo-generated docs are possible.
    # FIXME TODO insert anchor for first register, mdbook might super this in the future
    # https://github.com/rust-lang/mdBook/pull/2013
    # if rname[-2:] == "0":
    #     mr_anchor = ('id="{}"'
    #                  .format(rname[:-2].lower()))
    # else:
    #     mr_anchor = ''
    #
    # # FIXME TODO generate register fields "overview" in Markdown

    # table with fields
    header = ["Bits", "Type", "Reset", "Name", "Description"]
    colalign = ["center", "center", "center", "left", "left"]
    rows = []
    nextbit = width-1
    fcount = 0

    def maybe_add_reversed(msb):
        nonlocal nextbit
        nonlocal rows
        # insert a row for reserved bits if any
        if nextbit > msb:
            tmp_row = []
            if (nextbit == msb + 1):
                tmp_row.append(str(nextbit))
            else:
                tmp_row.append(str(nextbit) + ":" + str(msb + 1))
            tmp_row.extend(["", "", "", "Reserved"])
            rows.append(tmp_row)
            nextbit = msb

    for field in reversed(reg.fields):
        row = []
        fcount += 1
        fname = field.name

        # insert a row for reserved bits if any
        maybe_add_reversed(field.bits.msb)

        row.append(field.bits.as_str())
        row.append(field.swaccess.key)
        row.append('x' if field.resval is None else hex(field.resval))
        row.append(fname)

        # Collect up any description and enum table
        desc_parts = []

        if field.desc is not None:
            desc_parts += expand_paras(field.desc, rnames)

        if field.enum is not None:
            hex_width = 2 + ((field.bits.width() + 3) // 4)
            for enum in field.enum:
                enum_desc_paras = expand_paras(enum.desc, rnames)
                # if there are several paragraph, we join them together in one
                # many descriptions start by giving the value again which is redundant, ie
                #  6’b00_0001: Electronic Codebook (ECB) mode.
                # so we remove it
                if enum_desc_paras[0].startswith(f"{field.bits.width()}'b"):
                    idx = enum_desc_paras[0].find(':')
                    if idx is not None:
                        enum_desc_paras[0] = enum_desc_paras[0][idx + 1:]
                desc_parts.append(
                    coderef(f" {enum.value:#0{hex_width}x} = {enum.name}") +
                    ": " + " ".join(enum_desc_paras))
            if field.has_incomplete_enum():
                desc_parts.append(coderef("Other values are reserved."))

        row.append(md_safe_for_table(desc_parts))
        rows.append(row)
        nextbit = field.bits.lsb - 1
    # insert a row for reserved bits if any
    maybe_add_reversed(0)

    genout(outfile, table(header, rows, colalign))


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


def gen_md_window(outfile: TextIO, win: Window, comp: str, regwidth: int,
                  rnames: Set[str]) -> None:
    wname = win.name or '(unnamed window)'
    offset = win.offset
    desc_paras = expand_paras(win.desc, rnames)
    desc_head = desc_paras[0]
    desc_body = desc_paras[1:]

    genout(outfile, title(wname, 4))
    genout(outfile, desc_head)
    genout(outfile, "\n")
    gen_kv(outfile, "Offset", f"{offset:#x}")
    gen_kv(outfile, "Items", f"{win.items}")
    gen_kv(outfile, "Access", f"{win.swaccess.key}")
    gen_kv(outfile, "Byte writes",
           'supported' if win.byte_write else 'NOT supported')
    genout(outfile, "\n")
    for p in desc_body:
        genout(outfile, p)
        genout(outfile, "\n")

    # wid = win.validbits
    #
    # for x in range(regwidth - 1, -1, -1):
    #     if x == regwidth - 1 or x == wid - 1 or x == 0:
    #         genout(outfile, '<td class="bitnum">' + str(x) + '</td>')
    #     else:
    #         genout(outfile, '<td class="bitnum"></td>')
    # genout(outfile, '</tr>')
    #
    # # We want to show the first and last two addresses, with a blank line in
    # # between if we skip anything.
    # assert win.items >= 1
    # if win.items <= 4:
    #     indices_0 = list(range(win.items))
    #     indices_1 = []
    # else:
    #     indices_0 = [0, 1]
    #     indices_1 = [win.items - 2, win.items - 1]
    #
    # for idx in indices_0:
    #     gen_window_row(outfile, offset, win.validbits, regwidth, idx)
    # if indices_1:
    #     gen_window_row(outfile, offset, win.validbits, regwidth, None)
    # for idx in indices_1:
    #     gen_window_row(outfile, offset, win.validbits, regwidth, idx)
    #
    # genout(outfile, '</td></tr></table>')
    # genout(outfile,
    #        '<tr>{}</tr>'.format(render_td(win.desc, rnames, 'regde')))
    # genout(outfile, "</table>\n<br>\n")


def gen_md_reg_block(outfile: TextIO, rb: RegBlock, comp: str, width: int,
                     rnames: Set[str]) -> None:
    if len(rb.entries) == 0:
        genout(outfile, 'This interface does not expose any registers.')
    else:
        # Generate overview table first.
        obj_list: List[Union[Register, Window]] = []
        for x in rb.entries:
            if isinstance(x, MultiRegister):
                for reg in x.regs:
                    obj_list += [reg]
            else:
                assert isinstance(x, Window) or isinstance(x, Register)
                obj_list += [x]
        gen_md_register_summary(outfile, obj_list, comp, width, rnames)

        # Generate detailed entries
        for x in rb.entries:
            if isinstance(x, Register):
                gen_md_register(outfile, x, comp, width, rnames)
            elif isinstance(x, MultiRegister):
                for reg in x.regs:
                    gen_md_register(outfile, reg, comp, width, rnames)
            else:
                assert isinstance(x, Window)
                gen_md_window(outfile, x, comp, width, rnames)


def gen_md(block: IpBlock, outfile: TextIO) -> int:
    rnames = block.get_rnames()

    assert block.reg_blocks
    # Handle the case where there's just one interface
    if len(block.reg_blocks) == 1:
        rb = list(block.reg_blocks.values())[0]
        gen_md_reg_block(outfile, rb, block.name, block.regwidth, rnames)
        return 0

    # Handle the case where there is more than one device interface and,
    # correspondingly, more than one reg block.
    for iface_name, rb in block.reg_blocks.items():
        iface_desc = ('device interface <code>{}</code>'.format(iface_name)
                      if iface_name is not None else
                      'the unnamed device interface')
        genout(outfile, title(f"Registers visible under {iface_desc}", 3))
        gen_md_reg_block(outfile, rb, block.name, block.regwidth, rnames)

    return 0
