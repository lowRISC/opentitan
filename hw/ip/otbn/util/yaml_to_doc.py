#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Generate Markdown documentation for the instructions in insns.yml'''

import argparse
import os
import sys
from typing import Dict, List, TextIO

from shared.bool_literal import BoolLiteral
from shared.encoding import Encoding
from shared.insn_yaml import Insn, InsnsFile, InsnGroup, load_file
from shared.operand import ImmOperandType, Operand


def render_operand_row(operand: Operand) -> str:
    '''Generate the single row of a markdown table for an operand'''

    # This is in <tr><td> form, but we want to embed arbitrary markup (and
    # don't want to have to faff around with &lt; encodings. So we have to
    # include a blank line above and below. This makes (at least) Github
    # flavoured markdown switch back to "markdown mode" for the contents.
    parts = []
    parts.append('<tr><td>\n\n')
    parts.append('`<{}>`'.format(operand.name))
    parts.append('\n\n</td><td>')

    # The "description" cell contains any documentation supplied in the file,
    # and then any extra documentation that's implied by the type of the
    # operand.
    if operand.doc is not None:
        parts.append('\n\n')
        parts.append(operand.doc)

    if operand.op_type is not None:
        ot_doc = operand.op_type.markdown_doc()
        if ot_doc is not None:
            parts.append('\n\n')
            parts.append(ot_doc)

    parts.append('\n\n</td></tr>')
    return ''.join(parts)


def render_operand_table(insn: Insn) -> str:
    '''Generate the operand table for an instruction'''

    # We have to generate this in <tr><td> form because we want to put
    # block-level elements into the table cells (and markdown tables only
    # support inline elements).
    parts = []
    parts.append('<table><thead>'
                 '<tr><th>Assembly symbol</th><th>Description</th></tr>'
                 '</thead>'
                 '<tbody>')
    for operand in insn.operands:
        parts.append(render_operand_row(operand))
    parts.append('</tbody></table>\n\n')
    return ''.join(parts)


def render_encoding(mnemonic: str,
                    name_to_operand: Dict[str, Operand],
                    encoding: Encoding) -> str:
    '''Generate a table displaying an instruction encoding'''
    parts = []
    parts.append('<table style="font-size: 75%">')
    parts.append('<tr>')
    parts.append('<td></td>')
    for bit in range(31, -1, -1):
        parts.append('<td>{}</td>'.format(bit))
    parts.append('</tr>')

    # Build dictionary of bit ranges, keyed by the msb and with value a pair
    # (width, desc) where width is the width of the range in bits and desc is a
    # string describing what is stored in the range.
    by_msb = {}

    for field_name, field in encoding.fields.items():
        scheme_field = field.scheme_field
        # If this field is a literal value, explode it into single bits. To do
        # so, we walk the ranges and match up with ranges in the value.
        if isinstance(field.value, BoolLiteral):
            assert field.value.width > 0
            assert field.value.width == scheme_field.bits.width
            bits_seen = 0
            for msb, lsb in scheme_field.bits.ranges:
                val_msb = scheme_field.bits.width - 1 - bits_seen
                val_lsb = val_msb - msb + lsb
                bits_seen += msb - lsb + 1

                for idx in range(0, msb - lsb + 1):
                    desc = field.value.char_for_bit(val_lsb + idx)
                    by_msb[lsb + idx] = (1, '' if desc == 'x' else desc)
            continue

        # Otherwise this field's value is an operand name
        assert isinstance(field.value, str)
        operand_name = field.value

        # Figure out whether there's any shifting going on.
        op_type = name_to_operand[operand_name].op_type
        shift = op_type.shift if isinstance(op_type, ImmOperandType) else 0

        # If there is only one range (and no shifting), that's easy.
        if len(scheme_field.bits.ranges) == 1 and shift == 0:
            msb, lsb = scheme_field.bits.ranges[0]
            by_msb[msb] = (msb - lsb + 1, operand_name)
            continue

        # Otherwise, we have to split up the operand into things like "foo[8:5]"
        bits_seen = 0
        for msb, lsb in scheme_field.bits.ranges:
            val_msb = shift + scheme_field.bits.width - 1 - bits_seen
            val_lsb = val_msb - msb + lsb
            bits_seen += msb - lsb + 1
            if msb == lsb:
                desc = '{}[{}]'.format(operand_name, val_msb)
            else:
                desc = '{}[{}:{}]'.format(operand_name, val_msb, val_lsb)
            by_msb[msb] = (msb - lsb + 1, desc)

    parts.append('<tr>')
    parts.append('<td>{}</td>'.format(mnemonic.upper()))

    # Now run down the ranges in descending order of msb to get the table cells
    next_bit = 31
    for msb in sorted(by_msb.keys(), reverse=True):
        # Sanity check to make sure we have a dense table
        assert msb == next_bit

        width, desc = by_msb[msb]
        next_bit = msb - width

        parts.append('<td colspan="{}">{}</td>'.format(width, desc))

    assert next_bit == -1
    parts.append('</tr>')

    parts.append('</table>\n\n')
    return ''.join(parts)


def render_literal_pseudo_op(rewrite: List[str]) -> str:
    '''Generate documentation with expansion of a pseudo op'''
    parts = []
    parts.append('This instruction is a pseudo-operation and expands to the '
                 'following instruction sequence:\n```\n')
    for line in rewrite:
        parts.append(line)
        parts.append('\n')
    parts.append('```\n\n')
    return ''.join(parts)


def render_insn(insn: Insn, heading_level: int) -> str:
    '''Generate the documentation for an instruction

    heading_level is the current Markdown heading level. It should be greater
    than zero. For example, if it is 3, then the instruction will be introduced
    with "### <insn_name>".

    '''
    assert heading_level > 0

    parts = []

    # Heading, based on mnemonic (upper-cased)
    parts.append('{} {}\n'.format('#' * heading_level,
                                  insn.mnemonic.upper()))

    # If there's a note, render it as a callout
    if insn.note is not None:
        parts.append('<div class="bd-callout bd-callout-warning">'
                     '<h5>Note</h5>\n\n')
        parts.append(insn.note)
        parts.append('\n\n</div>\n\n')

    # Optional synopsis: some bold-face text expanding the mnemonic to
    # something more understandable.
    if insn.synopsis is not None:
        parts.append('**{}.**\n'.format(insn.synopsis))

    # Optional documentation (using existing markdown formatting). Add a blank
    # line afterwards to separate from the syntax and operand table.
    if insn.doc is not None:
        parts.append(insn.doc + '\n\n')

    # Syntax example: either given explicitly or figured out from operands
    parts.append("```\n")
    parts.append(insn.mnemonic.upper() + ('' if insn.glued_ops else ' '))
    parts.append(insn.syntax.render_doc())
    parts.append("\n```\n\n")

    # If this came from the RV32I instruction set, say so.
    if insn.rv32i:
        parts.append('This instruction is defined in the RV32I instruction set.\n\n')

    # If this takes more than a single cycle, say so.
    if insn.cycles > 1:
        parts.append('This instruction takes {} cycles.\n\n'
                     .format(insn.cycles))

    # Show any trailing documentation (stuff that should come after the syntax
    # example but before the operand table).
    if insn.trailing_doc is not None:
        parts.append('\n')
        parts.append(insn.trailing_doc)
        parts.append('\n\n')

    # Show the operand table if at least one operand has an associated
    # description.
    if any(op.doc is not None for op in insn.operands):
        parts.append(render_operand_table(insn))

    # Show encoding if we have one
    if insn.encoding is not None:
        parts.append(render_encoding(insn.mnemonic,
                                     insn.name_to_operand,
                                     insn.encoding))

    # If this is a pseudo-op with a literal translation, show it
    if insn.literal_pseudo_op is not None:
        parts.append(render_literal_pseudo_op(insn.literal_pseudo_op))

    # Show decode pseudo-code if given
    if insn.decode is not None:
        parts.append('{} Decode\n\n'
                     '```python3\n'
                     '{}\n'
                     '```\n\n'
                     .format('#' * (heading_level + 1),
                             insn.decode))

    # Show operation pseudo-code if given
    if insn.operation is not None:
        parts.append('{} Operation\n\n'
                     '```python3\n'
                     '{}\n'
                     '```\n\n'
                     .format('#' * (heading_level + 1),
                             insn.operation))
    return ''.join(parts)


def render_insn_group(group: InsnGroup,
                      heading_level: int,
                      out_file: TextIO) -> None:
    # We don't print the group heading: that's done in the top-level
    # documentation so it makes it into the TOC.

    out_file.write(group.doc + '\n\n')

    if not group.insns:
        out_file.write('No instructions in group.\n\n')
        return

    for insn in group.insns:
        out_file.write(render_insn(insn, heading_level))


def render_insns(insns: InsnsFile,
                 heading_level: int,
                 out_dir: str) -> None:
    '''Render documentation for all instructions'''
    for group in insns.groups.groups:
        group_path = os.path.join(out_dir, group.key + '.md')
        with open(group_path, 'w') as group_file:
            render_insn_group(group, heading_level, group_file)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('yaml_file')
    parser.add_argument('out_dir')

    args = parser.parse_args()

    try:
        insns = load_file(args.yaml_file)
    except RuntimeError as err:
        print(err, file=sys.stderr)
        return 1

    try:
        os.makedirs(args.out_dir, exist_ok=True)
    except OSError as err:
        print('Failed to create output directory {!r}: {}.'
              .format(args.out_dir, err))

    render_insns(insns, 3, args.out_dir)
    return 0


if __name__ == '__main__':
    sys.exit(main())
