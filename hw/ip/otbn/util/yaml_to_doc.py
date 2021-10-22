#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Generate Markdown documentation for the instructions in insns.yml'''

import argparse
import os
import sys
from typing import Dict, List, Optional, TextIO, Tuple

from shared.bool_literal import BoolLiteral
from shared.encoding import Encoding
from shared.insn_yaml import Insn, InsnsFile, InsnGroup, load_file
from shared.operand import EnumOperandType, OptionOperandType, Operand

from docs.get_impl import read_implementation

_O2EDicts = Tuple[Dict[str, List[str]], Dict[int, str]]


def render_operand_row(operand: Operand,
                       op_ranges: Optional[List[str]]) -> str:
    '''Generate the single row of a markdown table for an operand'''

    # This is in <tr><td> form, but we want to embed arbitrary markup (and
    # don't want to have to faff around with &lt; encodings. So we have to
    # include a blank line above and below. This makes (at least) Github
    # flavoured markdown switch back to "markdown mode" for the contents.
    parts = []
    parts.append('<tr><td>\n\n')
    parts.append('`{}`'.format(operand.name))
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

        if op_ranges is not None:
            parts.append('\n\n')
            dec_str = operand.op_type.describe_decode(op_ranges)
            parts.append('Decode as `{}`\n\n'.format(dec_str))

    parts.append('\n\n</td></tr>')
    return ''.join(parts)


def render_operand_table(operands: List[Operand],
                         o2e: Optional[Dict[str, List[str]]]) -> str:
    '''Generate the operand table for an instruction'''

    # We have to generate this in <tr><td> form because we want to put
    # block-level elements into the table cells (and markdown tables only
    # support inline elements).
    parts = []
    parts.append('<table><thead>'
                 '<tr><th>Operand</th><th>Description</th></tr>'
                 '</thead>'
                 '<tbody>')
    for operand in operands:
        if o2e is None:
            op_ranges = None
        else:
            op_ranges = o2e.get(operand.name)
            # If we had an encoding, it should have encoded every operand, so
            # name_op_enc_fields should have picked up operand.
            assert op_ranges is not None

        parts.append(render_operand_row(operand, op_ranges))

    parts.append('</tbody></table>\n\n')
    return ''.join(parts)


def render_encoding(mnemonic: str,
                    encoding: Encoding,
                    e2o: Dict[int, str]) -> str:
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

        # Otherwise this field's value is an operand name. name_op_enc_fields
        # should have added the MSBs of its ranges to e2o.
        assert isinstance(field.value, str)
        for msb, lsb in scheme_field.bits.ranges:
            assert msb in e2o
            by_msb[msb] = (msb - lsb + 1, e2o[msb])

    parts.append('<tr>')
    parts.append('<td>{}</td>'.format(mnemonic.upper()))

    # Now run down the ranges in descending order of msb to get the table cells
    next_bit = 31
    for msb in sorted(by_msb.keys(), reverse=True):
        # Check to make sure we have a dense table (this should be guaranteed
        # because encoding objects ensure they hit every bit).
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


def name_op_enc_fields(name_to_operand: Dict[str, Operand],
                       encoding: Encoding) -> _O2EDicts:
    '''Name the encoding fields corresponding to operators

    In the generated documentation, we name encoding fields based on the
    operand that the encode. For example, if the operand "foo" is encoded in a
    field, the field will be labelled "FOO" in the table. If the field is split
    over multiple bit ranges, they will be labelled like "FOO_0", "FOO_1" etc,
    counting from the LSB. If an operand has an abbreviated name, this will be
    used for the field instead of the full operand name.

    Returns a pair of dicts: (o2e, e2o). o2e maps an operand name to the list
    of (our names for) encoding fields that contribute to it, MSB first. e2o
    maps the MSB of a bit range in an encoding field to the name that should
    appear for that range in the documentation.

    In the example above, o2e['foo'] = ["FOO_1", "FOO_0"]. Suppose that the
    upper range of bits for the encoding field for 'foo' had MSB 10. Then
    e2o[10] = 'FOO_1'.

    '''
    o2e = {}  # type: Dict[str, List[str]]
    e2o = {}  # type: Dict[int, str]

    for field_name, field in encoding.fields.items():
        # Ignore literal values: these don't correspond to operands
        if isinstance(field.value, BoolLiteral):
            continue

        # Otherwise this field's value is an operand name
        assert isinstance(field.value, str)
        operand_name = field.value

        # An encoding should never use an operand more than once
        assert operand_name not in o2e

        # Get the base name to use for fields. This is either an upper-case
        # version of the operand name, or uses the operand's abbreviated name
        # if available.
        operand = name_to_operand.get(operand_name)
        assert operand is not None
        basename = operand_name if operand.abbrev is None else operand.abbrev
        basename = basename.upper()

        # There should always be at least one bit range for the field
        scheme_field = field.scheme_field
        assert scheme_field.bits.ranges

        # If there is just one bit range, we generate a single named range by
        # capitalizing the operand name.
        if len(scheme_field.bits.ranges) == 1:
            msb = scheme_field.bits.ranges[0][0]
            assert msb not in e2o
            range_name = basename
            o2e[operand_name] = [range_name]
            e2o[msb] = range_name
            continue

        # Otherwise, we need to label the operands. We iterate over the ranges
        # in scheme_field LSB-first (so that we can number things with the LSB
        # field having index zero).
        o2e_list = []
        for idx, (msb, lsb) in enumerate(reversed(scheme_field.bits.ranges)):
            range_name = '{}_{}'.format(basename, idx)
            o2e_list.append(range_name)
            assert msb not in e2o
            e2o[msb] = range_name
        # We want to store o2e_list MSB-first, so reverse it here.
        o2e_list.reverse()
        o2e[operand_name] = o2e_list

    return (o2e, e2o)


def render_insn(insn: Insn, impl: Optional[str], heading_level: int) -> str:
    '''Generate the documentation for an instruction

    heading_level is the current Markdown heading level. It should be greater
    than zero. For example, if it is 3, then the instruction will be introduced
    with "### <insn_name>".

    '''
    assert heading_level > 0

    parts = []
    mnem = insn.mnemonic.upper()
    subhead = '#' * (heading_level + 1) + ' '

    # Heading, based on mnemonic (upper-cased)
    parts.append('{} {}\n'.format('#' * heading_level, mnem))

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
        parts.append(insn.doc + '\n')
    parts.append('\n')

    # If this came from the RV32I instruction set, say so.
    if insn.rv32i:
        parts.append('This instruction is defined in the '
                     'RV32I instruction set.\n\n')

    # A list of errors that the instruction might cause.
    if insn.errs is not None:
        parts.append(subhead + 'Errors\n')
        if not insn.errs:
            parts.append('{} cannot cause any software errors.\n'.format(mnem))
        else:
            parts.append('{} might cause the following software errors:\n'
                         .format(mnem))
            for desc in insn.errs:
                parts.append('- {}\n'.format(desc))
        parts.append('\n')

    # Syntax example: either given explicitly or figured out from operands
    parts.append(subhead + 'Syntax\n')
    parts.append("```\n")
    parts.append(insn.mnemonic.upper() + ('' if insn.glued_ops else ' '))
    parts.append(insn.syntax.render_doc())
    parts.append("\n```\n\n")

    is_pseudo = insn.literal_pseudo_op or insn.python_pseudo_op

    # If we have an encoding, match up encoding fields with operands
    if is_pseudo or insn.encoding is None:
        o2e = None
        e2o = None
    else:
        o2e, e2o = name_op_enc_fields(insn.name_to_operand, insn.encoding)

    # Show the operand table if there is at least one operand and this isn't a
    # pseudo-op.
    if insn.operands and not is_pseudo:
        parts.append(subhead + 'Operands\n')
        parts.append(render_operand_table(insn.operands, o2e))

    # Show encoding if we have one
    if e2o is not None:
        parts.append(subhead + 'Encoding\n')
        assert insn.encoding is not None
        parts.append(render_encoding(insn.mnemonic, insn.encoding, e2o))

    # If this is a pseudo-op with a literal translation, show it
    if insn.literal_pseudo_op is not None:
        parts.append(render_literal_pseudo_op(insn.literal_pseudo_op))

    if impl is not None:
        parts.append(subhead + 'Operation\n')

        # Add a handy header to remind readers that enum operands and option
        # operands are referred to by their integer values.
        not_num_ops = []
        for operand in insn.operands:
            if ((isinstance(operand.op_type, EnumOperandType) or
                 isinstance(operand.op_type, OptionOperandType))):
                not_num_ops.append(operand.name)

        if not_num_ops:
            if len(not_num_ops) == 1:
                op_str = ('operand `{}` is referred to by its'
                          .format(not_num_ops[0]))
            else:
                op_str = ('operands {} and `{}` are referred to by their'
                          .format(', '.join('`{}`'.format(e)
                                            for e in not_num_ops[:-1]),
                                  not_num_ops[-1]))

            parts.append('In the listing below, {} integer value.\n'
                         'The operand table above shows how this corresponds '
                         'to assembly syntax.\n\n'
                         .format(op_str))

        # Note: No trailing newline after the inserted contents because libcst
        # (which we use for extracting documentation) always adds a trailing
        # newline itself.
        parts.append('```\n'
                     '{}'
                     '```\n\n'
                     .format(impl))
    return ''.join(parts)


def render_insn_group(group: InsnGroup,
                      impls: Dict[str, str],
                      heading_level: int,
                      out_file: TextIO) -> None:
    # We don't print the group heading: that's done in the top-level
    # documentation so it makes it into the TOC.

    out_file.write(group.doc + '\n\n')

    if not group.insns:
        out_file.write('No instructions in group.\n\n')
        return

    for insn in group.insns:
        class_name = insn.mnemonic.replace('.', '').upper()
        impl = impls.get(class_name)
        out_file.write(render_insn(insn, impl, heading_level))


def render_insns(insns: InsnsFile,
                 impls: Dict[str, str],
                 heading_level: int,
                 out_dir: str) -> None:
    '''Render documentation for all instructions'''
    for group in insns.groups.groups:
        group_path = os.path.join(out_dir, group.key + '.md')
        with open(group_path, 'w') as group_file:
            render_insn_group(group, impls, heading_level, group_file)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('yaml_file')
    parser.add_argument('py_file')
    parser.add_argument('out_dir')

    args = parser.parse_args()

    try:
        insns = load_file(args.yaml_file)
        impls = read_implementation(args.py_file)
    except RuntimeError as err:
        print(err, file=sys.stderr)
        return 1

    try:
        os.makedirs(args.out_dir, exist_ok=True)
    except OSError as err:
        print('Failed to create output directory {!r}: {}.'
              .format(args.out_dir, err))

    render_insns(insns, impls, 2, args.out_dir)
    return 0


if __name__ == '__main__':
    sys.exit(main())
