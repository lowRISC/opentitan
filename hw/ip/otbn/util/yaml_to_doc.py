#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Generate Markdown documentation for the instructions in insns.yml'''

import argparse
import sys

from insn_yaml import Insn, InsnsFile, Operand, load_file


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
    parts.append(insn.mnemonic.upper() + ' ')
    if insn.syntax is not None:
        parts.append(insn.syntax.raw_string())
    else:
        parts.append(', '.join('<{}>'.format(op.name) for op in insn.operands))
    parts.append("\n```\n\n")

    # If this came from the RV32I instruction set, say so.
    if insn.rv32i:
        parts.append('This instruction is defined in the RV32I instruction set.\n\n')

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


def render_insns(insns: InsnsFile, heading_level: int) -> str:
    '''Render documentation for all instructions'''
    parts = []
    for group, group_insns in insns.grouped_insns():
        parts.append('{} {}\n\n'.format('#' * heading_level, group.title))
        parts.append(group.doc)
        parts.append('\n\n')

        if not group_insns:
            parts.append('No instructions in group.\n\n')
            continue

        for insn in group_insns:
            parts.append(render_insn(insn, heading_level + 1))

    return ''.join(parts)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('yaml_file')

    args = parser.parse_args()

    try:
        insns = load_file(args.yaml_file)
    except RuntimeError as err:
        sys.stderr.write('{}\n'.format(err))
        return 1

    print(render_insns(insns, 2))
    return 0


if __name__ == '__main__':
    sys.exit(main())
