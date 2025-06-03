# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Generate markdown documentation for the registers of an IpBlock."""

import json
from typing import List, TextIO, Dict, Any, Optional

from reggen.ip_block import IpBlock
from reggen.md_helpers import (
    coderef, mono, italic, list_item, table,
    regref_to_link, first_line, title, url, wavejson,
)
from reggen.multi_register import MultiRegister
from reggen.reg_block import RegBlock
from reggen.register import Register
from reggen.window import Window


def gen_md(block: IpBlock, output: TextIO) -> int:
    assert block.reg_blocks
    # Handle the case where there's just one interface.
    if len(block.reg_blocks) == 1:
        rb = next(iter(block.reg_blocks.values()))
        gen_md_reg_block(output, rb, block.name, block.regwidth)
        return 0

    # Handle the case where there is more than one device interface and,
    # correspondingly, more than one reg block.
    for iface_name, rb in block.reg_blocks.items():
        assert iface_name
        gen_md_reg_block(output, rb, block.name, block.regwidth, iface_name)

    return 0


def gen_md_reg_block(output: TextIO,
                     rb: RegBlock,
                     comp: str,
                     width: int,
                     iface_name: Optional[str] = None) -> None:
    if len(rb.entries) == 0:
        output.write('This interface does not expose any registers.')
        return

    # Generate overview table.
    gen_md_register_summary(output, rb.entries, comp, width, iface_name)

    # Generate detailed entries.
    for x in rb.entries:
        if isinstance(x, Register):
            gen_md_register(output, x, comp, width)
        elif isinstance(x, MultiRegister):
            gen_md_multiregister(output, x, comp, width)
        else:
            assert isinstance(x, Window)
            gen_md_window(output, x, comp, width)


def gen_md_register_summary(output: TextIO,
                            entries: List[object],
                            comp: str,
                            width: int,
                            iface_name: Optional[str] = None) -> None:

    heading = "Summary" if iface_name is None \
        else "Summary of the " + coderef(iface_name) + " interface's registers"
    output.write(title(heading, 2))

    bytew = width // 8

    header = ["Name", "Offset", "Length", "Description"]
    rows: List[List[str]] = []

    def add_row(name: str, anchor: str, offset: int, length: int,
                description: str) -> None:
        rows.append([
            comp + "." + url(mono(name), "#" + anchor),
            hex(offset),
            str(length),
            first_line(description),
        ])

    for entry in entries:
        if isinstance(entry, MultiRegister):
            is_compact = multireg_is_compact(entry, width)
            for reg in entry.cregs:
                # If multiregisters are compact, each register has it's own section,
                # so the anchor should link to a section with the individual register name(s).
                # Otherwise, there is one section for the whole multiregister,
                # so the anchor should link to a section with the multiregister name.
                anchor = reg.name.lower() if is_compact else entry.name.lower()
                add_row(reg.name, anchor, reg.offset, bytew, reg.desc)
        elif isinstance(entry, Window):
            length = bytew * entry.items
            add_row(entry.name, entry.name.lower(), entry.offset, length,
                    entry.desc)
        else:
            assert isinstance(entry, Register)
            add_row(entry.name, entry.name.lower(), entry.offset, bytew,
                    entry.desc)

    output.write(table(header, rows))


def gen_md_window(output: TextIO, win: Window, comp: str,
                  regwidth: int) -> None:
    assert win.name
    wname = win.name

    # Word aligned start and end addresses.
    start_addr = win.offset
    end_addr = start_addr + 4 * win.items - 4

    output.write(
        title(wname, 2) + win.desc + "\n\n" +
        list_item("Word Aligned Offset Range: " + mono(f"{start_addr:#x}") +
                  "to" + mono(f"{end_addr:#x}")) +
        list_item("Size (words): " + mono(f"{win.items}") + "") +
        list_item("Access: " + mono(f"{win.swaccess.key}")) +
        list_item("Byte writes are " +
                  (italic("not") if not win.byte_write else "") +
                  " supported.") + "\n")


def multireg_is_compact(mreg: MultiRegister, width: int) -> bool:
    # Note that validation guarantees that compacted multiregs only ever have one field.
    return mreg.compact and (mreg.pregs[0].fields[0].bits.msb + 1) <= width // 2


def describe_reg_hdr(output: TextIO, reg: Register, with_offset: bool) -> None:
    '''Write a header for the register description.

    If with_offset is True, this includes the offset of the register. (Set it
    to False if printing a MultiRegister)
    '''
    regwen_str = ""
    if reg.regwen is not None:
        regwen_url = "#" + reg.regwen.lower()
        regwen_str = list_item("Register enable: " +
                               url(mono(reg.regwen), regwen_url))

    offset_str = (list_item("Offset: " +
                            mono(f"{reg.offset:#x}")) if with_offset else "")
    output.write(
        title(reg.name, 2) + regref_to_link(reg.desc) + "\n" + offset_str +
        list_item("Reset default: " + mono(f"{reg.resval:#x}")) +
        list_item("Reset mask: " + mono(f"{reg.resmask:#x}")) + regwen_str)


def gen_md_multiregister(output: TextIO, mreg: MultiRegister, comp: str,
                         width: int) -> None:
    # Check whether this is a compacted multireg, in which case we cannot use
    # the general definition of the first register as an example for all
    # other instances.
    if multireg_is_compact(mreg, width):
        for reg in mreg.cregs:
            gen_md_register(output, reg, comp, width)
        return

    # The general definition of the registers making up this multiregister block.
    reg_def = mreg.pregs[0]

    # Information
    describe_reg_hdr(output, reg_def, False)

    # Instances
    output.write("\n" + title("Instances", 3))
    output.write(
        table(
            ["Name", "Offset"],
            [[reg.name, hex(reg.offset)] for reg in mreg.cregs],
        ))

    # Fields
    output.write("\n" + title("Fields", 3))

    # Generate bit-field wavejson.
    gen_md_reg_picture(output, reg_def, width)

    # Generate fields
    gen_md_reg_fields(output, reg_def, width)


def gen_md_register(output: TextIO, reg: Register, comp: str,
                    width: int) -> None:
    describe_reg_hdr(output, reg, True)

    # Fields
    output.write("\n" + title("Fields", 3))

    # Generate bit-field wavejson.
    gen_md_reg_picture(output, reg, width)

    # Generate fields
    gen_md_reg_fields(output, reg, width)


def gen_md_reg_picture(output: TextIO, reg: Register, width: int) -> None:
    """Outputs a wavejson description of the register in a markdown code block.

    We use WaveDrom to illustrate the register since we already have a wavejson preprocessor.
    The wavejson bit-field is great but has some limitations that make it hard to draw nice picture.
    Notably, it does not automatically rotate fields that don't fit
    or increase the vertical space if necessary.
    As the result, the following code makes some assumptions to decide when to rotate
    and to compute the vertical space.
    Furthermore, we do not know the horizontal size so we have to fix it,
    which mean that the final result might be rescaled on the page.
    """
    hspace = 640
    vspace = 80
    fontsize = 10
    lanes = 1
    margin = 10  # margin around text
    # estimated size that a character takes
    font_adv = 10
    # size of each bit in the picture
    bit_width = hspace * lanes / width

    fields: List[Dict[str, Any]] = []
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

    json_str = json.dumps({"reg": fields, "config": config})
    output.write(wavejson(json_str))


def gen_md_reg_fields(output: TextIO, reg: Register, width: int) -> None:
    # The maximum field description length allowed in a register's field table
    MAX_DESCRIPTION_LEN = 250

    # If any field is an enum or has a long description,
    # put fields in their own sections.
    field_sections = any(
        field.enum is not None or
        (field.desc is not None and len(field.desc) > MAX_DESCRIPTION_LEN)
        for field in reg.fields)

    header = ["Bits", "Type", "Reset", "Name"]
    colalign = ["center", "center", "center", "left"]
    # If generating field sections, the description of fields will not be put in the table.
    if not field_sections:
        header.append("Description")
        colalign.append("left")

    def reserved_row(msb: int, lsb: int) -> List[str]:
        return (([f"{msb}:{lsb}"] if msb != lsb else [str(msb)]) +
                (["", "", ""] if not field_sections else ["", ""]) +
                ["Reserved"])

    rows = []
    nextbit = width - 1
    for field in reversed(reg.fields):
        fname = field.name
        msb = field.bits.msb

        # Insert a row for any reserved bits before this field
        if nextbit > msb:
            rows.append(reserved_row(nextbit, msb + 1))

        row = [
            field.bits.as_str(),
            field.swaccess.key,
            'x' if field.resval is None else hex(field.resval),
        ]
        # If generating field sections, just add the name with a link to it's section.
        if field_sections:
            row.append(url(fname, f"#{reg.name.lower()}--{fname.lower()}"))
        # Otherwise, add the name and description to the table.
        else:
            row.extend([
                fname, "" if field.desc is None else regref_to_link(field.desc)
            ])

        rows.append(row)

        nextbit = field.bits.lsb - 1

    # Insert a row for any remaining reserved bits
    if nextbit > 0:
        rows.append(reserved_row(nextbit, 0))

    output.write(table(header, rows, colalign))

    # Return before generating field sections, if they are not wanted.
    if not field_sections:
        return

    # Generate field sections.
    for field in reversed(reg.fields):
        fname = field.name

        output.write(title(f"{reg.name} . {fname}", 3))

        if field.desc is not None:
            output.write(regref_to_link(field.desc) + "\n")

        if field.enum is not None:
            if len(field.enum) == 0:
                output.write("All values are reserved.\n")
            else:
                header = ["Value", "Name", "Description"]
                hex_width = 2 + ((field.bits.width() + 3) // 4)
                rows = [[f"{enum.value:#0{hex_width}x}", enum.name, enum.desc]
                        for enum in field.enum]
                output.write(table(header, rows))

                if field.has_incomplete_enum():
                    output.write("Other values are reserved.\n")

        output.write("\n")
