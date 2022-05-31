#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
'''A wrapper around riscv32-unknown-elf-as for OTBN

Partial support:

  - This doesn't currently support .include directives fully (the included file
    will not be transformed, so OTBN instructions won't work there).

  - .file support assumes we're not using DWARF2 file numbers.

  - Operands may not have embedded spaces or commas. Complicated immediate
    expressions are not currently supported.

'''

import os
import re
import subprocess
import sys
import tempfile
from typing import Dict, List, Optional, Set, TextIO, Tuple

from shared.bit_ranges import BitRanges
from shared.encoding import Encoding
from shared.insn_yaml import Insn, InsnsFile, load_insns_yaml
from shared.operand import ImmOperandType, Operand, RegOperandType
from shared.toolchain import find_tool


class RVFmt:
    '''A simple representation of a format supported by .insn

    The internal representation has the list of operand names (self.operands).
    These are keys for self.op_data, whose entries are tuples (fmt, shift,
    ranges).

    Later, the assembler will need to look up fields by bit. The self.bit_to_op
    attribute is a list of length 32 (indexed by bit) whose items are tuples
    (msb, lsb, op_name, shift). Such a tuple means "the range of bits
    {msb,...lsb} appears in the operand called op_name and its LSB there is
    shift".

    To make these easy to write down, we parse a textual format which describes
    the bit fields and then the .insn syntax. This is a sort of "inside out"
    version of the BitRanges format, but more closely matches the RISC-V
    documentation, so should be easier to write by hand.

    The bit fields should be a list of strings of the form NAME:TYPE. NAME is
    the name of the field which is just used to match up with the syntax. TYPE
    is one of the following:

        f<n>:    An n-bit literal value.
        r:       A 5-bit register name.
        i<n>:    An n-bit signed immediate
        u<n>:    An n-bit unsigned immediate

    The syntax should be a list of NAMEs. When an immediate in the encoding is
    split into multiple fields, they can be recombined here with a pipe symbol.
    So "foo|bar" means that the operand is split into the bit fields called
    "foo" and "bar" (MSB first). If the field is shifted (i.e. the assembly
    syntax N gets encoded as N >> S), the shift can be specified by a <<n
    suffix.

    '''

    def __init__(self, name: str, bitfields: List[str],
                 syntax: List[str]) -> None:
        self.name = name
        self.operands = syntax
        self.op_data = {}  # type: Dict[str, Tuple[str, int, BitRanges]]

        # First, expand the bitfield types to a dict mapping name to (fmt, msb,
        # lsb). Here, and below, we use assertions for error checking: the
        # inputs are from the code, so we don't need proper error messages.
        name_to_triple = {}
        msb = 31
        for field in bitfields:
            name, fmt_width = field.split(':')
            fmt = fmt_width[0]
            assert fmt in ['f', 'r', 'i', 'u']
            width = 5 if fmt == 'r' else int(fmt_width[1:])

            assert name not in name_to_triple
            lsb = msb - width + 1

            name_to_triple[name] = (fmt, msb, lsb)
            msb -= width

        assert msb == -1

        fields_used = set()  # type: Set[str]
        b2o_dict = {}

        for operand in syntax:
            op_fmt = None
            op_ranges = []

            op_shift = 0
            shift_idx = operand.find('<<')
            unshifted_name = operand
            if shift_idx >= 0:
                op_shift = int(operand[shift_idx + 2:])
                unshifted_name = operand[:shift_idx]

            # Work through the fields LSB-first (so that we can figure out the
            # shifts despite not knowing the width of the operand in advance).
            field_lsb = 0
            for field_name in reversed(unshifted_name.split('|')):
                assert field_name not in fields_used
                fields_used.add(field_name)
                assert field_name in name_to_triple
                fmt, msb, lsb = name_to_triple[field_name]

                assert op_fmt is None or fmt == op_fmt
                op_fmt = fmt

                op_ranges.append((msb, lsb))

                b2o_tuple = (msb, lsb, operand, op_shift + field_lsb)
                for bit in range(lsb, msb + 1):
                    assert bit not in b2o_dict
                    b2o_dict[bit] = b2o_tuple

                field_lsb += msb - lsb + 1

            # Reverse op_ranges again, because we want them MSB-first when we
            # call the BitRanges constructor.
            op_ranges.reverse()

            assert operand not in self.op_data
            assert op_fmt is not None
            self.op_data[operand] = (op_fmt, op_shift,
                                     BitRanges.from_list(op_ranges))

        assert len(b2o_dict) == 32

        # We've checked that we didn't use any fields twice. Now, make sure
        # that each field is actually associated with (part of) an operand in
        # the syntax.
        assert len(fields_used) == len(name_to_triple)

        self.bit_to_op = [b2o_dict[bit] for bit in range(32)]


def rv_render(fmt: str, num: int) -> str:
    '''Render a number as expected by a RISC-V .insn field'''
    if fmt in ['f', 'i', 'u']:
        return '{:#x}'.format(num)

    assert fmt == 'r'
    return 'x{}'.format(num)


# A _PartFieldEncoding is a list with items:
#
#    ((field_msb, field_lsb), rv_name, rv_lsb)
#
# This means: "The range of bits, {field_msb..field_lsb}, from the instruction
# field should be written in the .insn line by putting them in the operand
# called rv_name after shifting left by rv_lsb."
_PartFieldEncoding = List[Tuple[Tuple[int, int], str, int]]


class RVEncoding:
    '''A mapping from an Encoding to a RVFmt

    If we have one of these, we can use it to express the use of an instruction
    that has the given encoding as a .insn line (with the given RVFmt).

    '''

    def __init__(self, encoding: Encoding, rvfmt: RVFmt,
                 rv_masks: Dict[str, int], rv_to_full_op: Dict[str, str],
                 part_field_to_rv: Dict[str, _PartFieldEncoding]) -> None:
        self.encoding = encoding
        self.rvfmt = rvfmt
        self.rv_masks = rv_masks
        self.rv_to_full_op = rv_to_full_op
        self.part_field_to_rv = part_field_to_rv


RISCV_FORMATS = [
    RVFmt('r', ['func7:f7', 'rs2:r', 'rs1:r', 'func3:f3', 'rd:r', 'opcode:f7'],
          ['opcode', 'func3', 'func7', 'rd', 'rs1', 'rs2']),
    RVFmt('r4', [
        'rs3:r', 'func2:f2', 'rs2:r', 'rs1:r', 'func3:f3', 'rd:r', 'opcode:f7'
    ], ['opcode', 'func3', 'func2', 'rd', 'rs1', 'rs2', 'rs3']),
    RVFmt('i', ['simm12:i12', 'rs1:r', 'func3:f3', 'rd:r', 'opcode:f7'],
          ['opcode', 'func3', 'rd', 'rs1', 'simm12']),
    RVFmt('s',
          ['imm0:i7', 'rs2:r', 'rs1:r', 'func3:f3', 'imm1:i5', 'opcode:f7'],
          ['opcode', 'func3', 'rs2', 'rs1', 'imm0|imm1']),
    RVFmt('sb', [
        'imm12:i1', 'imm105:i6', 'rs2:r', 'rs1:r', 'func3:f3', 'imm41:i4',
        'imm11:i1', 'opcode:f7'
    ], ['opcode', 'func3', 'rs2', 'rs1', 'imm12|imm11|imm105|imm41<<1']),

    # The "U" format is used for LUI. The immediate operand gives imm[31:12]
    # for some imm. Confusingly, the spec implies that this is a signed
    # immediate, probably because it *is* sign-extended for the 64-bit
    # architecture. For a 32-bit architecture, the top bit is the sign, so
    # there is no sign extension to be done. The binutils assembler rejects
    # things like "lui x1, -1", treating the immediate as unsigned.
    RVFmt('u', ['imm20:u20', 'rd:r', 'opcode:f7'], ['opcode', 'rd', 'imm20']),
    RVFmt('j',
          ['i20:i1', 'i101:i10', 'i11:i1', 'i1912:i8', 'rd:r', 'opcode:f7'],
          ['opcode', 'rd', 'i20|i1912|i11|i101<<1'])
]


def find_rv_encoding(enc: Encoding, name_to_operand: Dict[str, Operand],
                     rvfmt: RVFmt) -> Optional[RVEncoding]:
    '''Try to find an RVEncoding that expresses enc with rvfmt'''

    # A map from RV field to operand name. It holds operands that fit
    # completely in a field and don't need any recoding.
    rv_field_to_op = {}  # type: Dict[str, str]
    full_ops = set()

    # When we assemble an instruction, it will look something this:
    #
    #    opcode r0, r1, 1, some_symbol
    #
    # Operands that take immediates (the "1" and "some_symbol" in the example)
    # are complicated, and we want to make sure that they correspond to an
    # immediate field in the encoding, so we can pass them through
    # syntactically and leave the GNU assembler to do the work.
    #
    # Operands that take registers (or options, or enums) are much simpler: we
    # can always get the integer value from the syntax. These, we can splat all
    # over a .insn line without having to worry.
    #
    # To work out whether an encoding is possible, we first go through fields
    # with "difficult" immediate operands. These need to map exactly to a field
    # in the RISC-V format.
    for field_name, field in enc.fields.items():
        if not isinstance(field.value, str):
            continue

        op_type = name_to_operand[field.value].op_type
        if op_type.syntax_determines_value():
            continue

        # We only support immediate operands (ImmOperandType) below here,
        # because we need to extract the "signed" field. If this instruction
        # uses some weird new operand type whose syntax doesn't determine its
        # value, we'll have to give up.
        if not isinstance(op_type, ImmOperandType):
            return None

        assert field.value not in full_ops
        full_ops.add(field.value)

        # Try to find a non-fixed field in rvfmt with the same bit ranges as
        # those in the encoding field.
        match = None
        for rv_name, (fmt, shift, rv_bits) in rvfmt.op_data.items():
            if fmt == 'f':
                continue
            if field.scheme_field.bits == rv_bits:
                match = (fmt, shift)
                break

        # If we didn't find a field in rvfmt for this field, we've failed.
        if match is None:
            return None

        fmt, shift = match

        # These "difficult" operands can only be encoded in immediate fields of
        # the correct shift and sign.
        if shift != op_type.shift:
            return None
        if fmt == 'i':
            if not op_type.signed:
                return None
        elif fmt == 'u':
            if op_type.signed:
                return None
        else:
            return None

        rv_field_to_op[rv_name] = field.value

    # We've dealt with any difficult operands and, if we got to here, we know
    # we're going to be able to make an .insn encoding for this instruction.
    # Now, we need to deal with all the other instruction fields. We accumulate
    # literal values from into a set of fixed masks (indexed by RV field name)
    # and take ranges from the other operands, describing how they should be
    # mapped to RV fields.
    #
    # We construct a dictionary of partial field mappings, keyed by encoding
    # field. The value at a field is a _PartFieldEncoding (see comment above
    # the definition there).
    partial_fields = {}

    for field_name, field in enc.fields.items():
        if isinstance(field.value, str):
            # An operand. Have we dealt with this already?
            if field.value in full_ops:
                continue

            operand = name_to_operand[field.value]
            assert operand.op_type.syntax_determines_value()

        scheme_field = field.scheme_field
        items = []

        # If not, look at the bit ranges in the instruction encoding and
        # work out how to map them to RV fields.
        bits_taken = 0
        for msb, lsb in scheme_field.bits.ranges:
            while msb >= lsb:
                rv_msb, rv_lsb, rv_op, rv_shift = rvfmt.bit_to_op[msb]

                # Intersect {msb..lsb} with {rv_msb..rv_lsb} to give the range
                # of bits we're covering in the eventual encoding.
                enc_msb = min(msb, rv_msb)
                enc_lsb = max(lsb, rv_lsb)
                enc_width = enc_msb - enc_lsb + 1

                # Since we looked up by msb, at least that point should be
                # in the range.
                assert enc_lsb <= msb <= enc_msb

                # {field_msb..field_lsb} is the range of bits from the
                # instruction field that are used.
                field_msb = scheme_field.bits.width - 1 - bits_taken
                field_lsb = field_msb - enc_width + 1
                assert 0 <= field_lsb <= field_msb <= scheme_field.bits.width

                # Finally, {rv_msb..rv_lsb} is the range of bits in the .insn
                # operand that we'll write.
                rv_lsb = rv_shift + (enc_lsb - rv_lsb)

                items.append(((field_msb, field_lsb), rv_op, rv_lsb))

                msb = enc_lsb - 1
                bits_taken += enc_width

        partial_fields[field_name] = items

    # Now we work through the fields (yet) again. For any fixed field, we can
    # calculate fixed values that will always be written. rv_masks is keyed by
    # rv operand name and contains those fixed values. part_field_to_rv_field
    # is everything else (with the same format as partial_fields)
    rv_masks = {}
    for rv_op in rvfmt.operands:
        rv_masks[rv_op] = 0

    part_field_to_rv_field = {}

    for field_name, pf_data in partial_fields.items():
        field = enc.fields[field_name]
        if isinstance(field.value, str):
            part_field_to_rv_field[field_name] = pf_data
            continue

        for (field_msb, field_lsb), rv_name, rv_lsb in pf_data:
            for field_bit in range(field_lsb, field_msb + 1):
                is_one = field.value.char_for_bit(field_bit) == '1'
                if is_one:
                    rv_bit = field_bit - field_lsb + rv_lsb
                    rv_masks[rv_name] |= 1 << rv_bit

    return RVEncoding(enc, rvfmt, rv_masks, rv_field_to_op,
                      part_field_to_rv_field)


def find_insn_schemes(mnem_to_insn: Dict[str, Insn]) -> Dict[str, RVEncoding]:
    '''Try to find a .insn scheme for each instruction'''
    ret = {}
    for mnem, insn in mnem_to_insn.items():
        # We definitely aren't going to manage it if we have no encoding
        if insn.encoding is None:
            continue

        for rvfmt in RISCV_FORMATS:
            rve = find_rv_encoding(insn.encoding, insn.name_to_operand, rvfmt)
            if rve is not None:
                ret[mnem] = rve
                break
    return ret


def parse_positionals(
        argv: List[str]) -> Tuple[List[str], List[str], Set[str]]:
    '''A partial argument parser that extracts positional arguments'''

    # The only arguments we actually need to parse from as are the input files:
    # we'll pass anything else straight through. Unfortunately, we can't use
    # argparse's parse_known_args because GNU as has an unusual syntax where
    # '--' means "standard input", rather than "stuff after this positional".
    positionals = []
    others = []

    # The switches listed in the as manual that can be specified as "--foo bar"
    # (we need to know them so that we don't think that "bar" is a positional
    # argument).
    space_args = ['--debug-prefix-map', '--defsym', '-I', '-o']

    # OTBN-specific flags
    otbn_flags = ['--otbn-translate']

    flags = set()

    expecting_arg = False
    for arg in argv[1:]:
        if expecting_arg:
            others.append(arg)
            expecting_arg = False
            continue

        if arg in otbn_flags:
            flags.add(arg)

        if arg in space_args:
            others.append(arg)
            expecting_arg = True
            continue

        if arg.startswith('-'):
            others.append(arg)
            continue

        positionals.append(arg)

    if '-h' in others or '--help' in others:
        print('otbn_as.py:\n\n'
              'A wrapper around riscv32-unknown-elf-as for OTBN.\n'
              'Most arguments are passed through: see "man as" '
              'for more information.\n'
              '\n'
              '  --otbn-translate: Translate the input and dump to '
              'stdout rather than calling as.\n')
        sys.exit(0)

    return (positionals, others, flags)


def _unpack_lx(where: str, mnemonic: str,
               op_to_expr: Dict[str, Optional[str]]) -> Tuple[str, str]:
    '''Unpack the arguments to li or la'''
    if set(op_to_expr.keys()) != {'grd', 'imm'}:
        umnem = mnemonic.upper()
        keys_list = list(op_to_expr.keys())
        raise RuntimeError(f'When expanding {umnem}, got wrong op_to_expr '
                           f'keys ({keys_list}). This is a mismatch between '
                           f'expand_{mnemonic} in otbn_as.py and the operands '
                           f'for {umnem} in insns.yml.')

    grd = op_to_expr['grd']
    imm = op_to_expr['imm']
    if grd is None:
        raise RuntimeError('When expanding LI, got <grd> = None. Is the '
                           '<grd> operand wrongly marked as optional in '
                           'insns.yml?')
    if imm is None:
        raise RuntimeError('When expanding LI, got <imm> = None. Is the '
                           '<imm> operand wrongly marked as optional in '
                           'insns.yml?')

    try:
        gpr_type = RegOperandType('gpr', False, True)
        grd_op_val = gpr_type.str_to_op_val(grd)
        assert grd_op_val is not None
    except ValueError as err:
        raise RuntimeError('{}: When parsing LI instruction, <grd> '
                           'operand is wrong: {}'.format(where, err))

    grd_txt = gpr_type.op_val_to_str(grd_op_val, None)
    return (grd_txt, imm)


def expand_li(where: str, op_to_expr: Dict[str, Optional[str]]) -> List[str]:
    '''Expand the li pseudo-op'''

    # This logic is slightly complicated so it has some associated tests in the
    # ISS testsuite (where we can run the results). If adding more cleverness
    # to this or fixing bugs, we should also add a check at
    # hw/ip/otbn/dv/otbnsim/test/simple/pseudos/li.s.

    grd_txt, imm = _unpack_lx(where, 'li', op_to_expr)
    try:
        imm_int = int(imm, 0)
    except ValueError:
        raise RuntimeError('{}: Cannot parse {!r}, the immediate for an LI '
                           'instruction, as an integer.'.format(where, imm))

    # We allow immediates in the range [-2^31, 2^31-1] (the i32 range), plus
    # [2^31, 2^32-1] (to allow any u32 constant).
    if not (-(1 << 31) <= imm_int <= (1 << 32) - 1):
        raise RuntimeError('{}: The immediate for an LI instruction is {}, '
                           'which does not fit in a 32-bit integer.'.format(
                               where, imm))

    # Convert any large positive constants to negative ones, so imm_int ends up
    # in the range [-2^31, 2^31-1].
    if (1 << 31) <= imm_int:
        imm_int -= 1 << 32

    assert -(1 << 31) <= imm_int <= (1 << 31) - 1

    # If imm_int is representable as an i12, we can just generate an addi
    if -(1 << 11) <= imm_int < (1 << 11):
        return ['addi {}, x0, {}'.format(grd_txt, imm_int)]

    imm_uint = imm_int if imm_int > 0 else (1 << 32) + imm_int
    assert imm_uint >= 0
    assert (imm_uint >> 32) == 0

    # Otherwise, we'll have to start with LUI. Extract the 12-bit constant as a
    # signed integer.
    mask_12 = (1 << 12) - 1
    imm_12 = mask_12 & imm_uint
    if imm_12 >> 11:
        imm_12 = imm_12 - (1 << 12)

    if imm_12 == 0:
        # We can just generate an LUI here
        return ['lui {}, {:#x}'.format(grd_txt, imm_uint >> 12)]

    if imm_12 > 0:
        # LUI; ADDI with a positive constant
        return [
            'lui {}, {:#x}'.format(grd_txt, imm_uint >> 12),
            'addi {}, {}, {:#x}'.format(grd_txt, grd_txt, imm_12)
        ]

    # LUI; ADDI with a negative constant. Add 1 to the upper immediate to
    # subtract from it.
    return [
        'lui {}, {:#x}'.format(grd_txt, 1 + (imm_uint >> 12)),
        'addi {}, {}, {}'.format(grd_txt, grd_txt, imm_12)
    ]


def expand_la(where: str, op_to_expr: Dict[str, Optional[str]]) -> List[str]:
    '''Expand the la pseudo-op'''

    # For RISC-V, "la rd, symbol" expands to two instructions:
    #
    #    auipc rd, delta[31:12] + delta[11]
    #    addi  rd, rd, delta[11:0]
    #
    # where delta = symbol - pc.
    #
    # For OTBN, both IMEM and DMEM are small. This means that we can represent
    # every symbol in 12 bits, so "la rd, symbol" can expand to:
    #
    #    addi rd, x0, %lo(symbol)
    #
    # Much easier!
    grd_txt, imm = _unpack_lx(where, 'la', op_to_expr)
    return [
        'lui {}, %hi({})'.format(grd_txt, imm),
        'addi {}, {}, %lo({})'.format(grd_txt, grd_txt, imm)
    ]


_PSEUDO_OP_ASSEMBLERS = {'li': expand_li, 'la': expand_la}


class Transformer:
    '''A simple parser/transformer for OTBN input files

    We have to do some basic tokenization to understand things like comments
    and strings (which can contain embedded newlines). We don't want to perturb
    the existing syntax, and want to pass comments through properly. Since the
    grammar we're recognising is very simple, it's probably easiest to
    hand-roll the parser.

    The grammar in a lazy pseudo-BNF syntax:

       file  ::= statement*

       blank ::= [\t ]+

       ws ::= blank? '#' [^n]* '\n'
            | blank? '/*' .*? '*/'
            | blank

       statement ::= ws? labels stmt-body? '\n'

       labels ::= label*

       label ::= symbol ':' ws?

       stmt-body ::= key-sym expr*

       key-sym ::= symbol    (this is a .directive or a mnemonic)

       symbol ::= [a-zA-Z0-9$._]+

    The proper syntax for "expr" depends on the key-sym, but we want to be very
    permissive, so allow pretty much anything up to end of line. The only
    reason we have to be careful is because strings can contain newlines, so we
    end up with:

       string ::= "... the usual \n \" rules with
                   embedded newlines" ws?

       normal-token ::= [^ \t"]+ ws?

       token ::= string | normal-token

       expr ::= token*

    Note that, while we don't need to understand the labels themselves, we do
    need to spot them in order to find the key-sym.

    '''

    def __init__(self, out_handle: TextIO, in_path: str, insns_file: InsnsFile,
                 glued_insns_dec_len: List[Insn],
                 mnem_to_rve: Dict[str, RVEncoding]) -> None:
        self.out_handle = out_handle
        self.in_path = in_path
        self.insns_file = insns_file
        self.glued_insns_dec_len = glued_insns_dec_len
        self.mnem_to_rve = mnem_to_rve

        self.line_number = 0

        # Strings that should be spat out verbatim
        self.acc = []  # type: List[str]

        # The key symbol for this statement
        self.key_sym = None  # type: Optional[str]

        self.in_comment = False
        self.in_string = False

        # FSM state.
        #
        #    0: Waiting for statement
        #    1: Waiting for body of statement (directive or instruction)
        self.state = 0

        # Write .file and .line directives to tell the assembler where the code
        # came from.
        out_handle.write('.file "{}"\n.line 1\n'.format(in_path))

    def mk_raw_line(self, insn: Insn, op_to_expr: Dict[str,
                                                       Optional[str]]) -> str:
        '''Generate a .word-style raw line

        insn must have an encoding and op_to_expr should map the operand names
        of insn to their string expressions from the assembly file.

        '''
        assert insn.encoding is not None

        # Generate a mapping from operand name to an encoded value. Note that
        # read_index checks that the value fits in the operand type and
        # converts to the value that should be encoded.
        op_to_idx = {}
        for op_name, expr in op_to_expr.items():
            op_type = insn.name_to_operand[op_name].op_type
            try:
                op_val = (0 if expr is None else op_type.str_to_op_val(
                    expr.strip()))
            except ValueError as err:
                raise RuntimeError('{}:{}: {}'.format(self.in_path,
                                                      self.line_number,
                                                      err)) from None
            if op_val is None:
                raise RuntimeError('{}:{}: Cannot resolve operand expression '
                                   '{!r} to an index and the instruction {!r} '
                                   'has an encoding incompatible with rv32i '
                                   '.insn lines.'.format(
                                       self.in_path, self.line_number, expr,
                                       insn.mnemonic)) from None

            try:
                enc_val = op_type.op_val_to_enc_val(op_val, None)
            except ValueError as err:
                raise RuntimeError('{}:{}: {}'.format(self.in_path,
                                                      self.line_number,
                                                      err)) from None

            if enc_val is None:
                raise RuntimeError(
                    '{}:{}: Cannot encode {!r} operand for '
                    '{!r} instruction without a current PC '
                    '(which is not known to otbn_as.py).'.format(
                        self.in_path, self.line_number, expr,
                        insn.mnemonic)) from None

            op_to_idx[op_name] = enc_val

        try:
            word_val = insn.encoding.assemble(op_to_idx)
        except ValueError as err:
            raise RuntimeError('{}:{}: {}'.format(self.in_path,
                                                  self.line_number,
                                                  err)) from None

        return '.word {:#010x}'.format(word_val)

    def mk_rve_line(self, insn: Insn, rve: RVEncoding,
                    op_to_expr: Dict[str, Optional[str]]) -> str:

        # Take a copy of the fixed fields
        rv_nums = rve.rv_masks.copy()

        # Now resolve all the fields for which we know we'll be able to get
        # numerical values
        for field_name, pfe in rve.part_field_to_rv.items():
            field = rve.encoding.fields[field_name]
            assert isinstance(field.value, str)

            expr = op_to_expr[field.value]
            if expr is None:
                continue

            op_type = insn.name_to_operand[field.value].op_type
            try:
                op_val = op_type.str_to_op_val(expr.strip())
                assert op_val is not None
                enc_val = op_type.op_val_to_enc_val(op_val, None)
                assert enc_val is not None
            except ValueError as err:
                raise RuntimeError('{}:{}: {}'.format(self.in_path,
                                                      self.line_number,
                                                      err)) from None

            # read_index should always return a non-None result if
            # syntax_determines_value() returned false.
            assert enc_val is not None

            for (field_msb, field_lsb), rv_name, rv_lsb in pfe:
                part_field_mask = (1 << (field_msb - field_lsb + 1)) - 1
                part_field_value = (enc_val >> field_lsb) & part_field_mask
                assert 0 == ((rv_nums[rv_name] >> rv_lsb) & part_field_mask)
                rv_nums[rv_name] |= part_field_value << rv_lsb

        rv_strings = {}
        for rv_name, rv_num in rv_nums.items():
            rv_op_fmt, _, _ = rve.rvfmt.op_data[rv_name]
            if rv_num != 0:
                # We've got some fixed or partial data. We shouldn't have a
                # match in rv_to_full_op (because the code in find_rv_encoding
                # will put an operand in that or rv_masks, but not both)
                assert rv_name not in rve.rv_to_full_op
                rv_strings[rv_name] = rv_render(rv_op_fmt, rv_num)
                continue

            op_name = rve.rv_to_full_op.get(rv_name)
            if op_name is not None:
                expr = op_to_expr[op_name]
                if expr is not None:
                    rv_strings[rv_name] = expr.strip()
                    continue

            rv_strings[rv_name] = rv_render(rv_op_fmt, rv_num)

        rv_str_list = []
        for rv_name in rve.rvfmt.operands:
            rv_str_list.append(rv_strings[rv_name])

        return '.insn {} {}'.format(rve.rvfmt.name, ', '.join(rv_str_list))

    def gen_line(self, insn: Insn, op_to_expr: Dict[str,
                                                    Optional[str]]) -> None:
        '''Build and write out a line for this instruction'''
        assert self.key_sym is not None

        expansion = None

        # If this instruction is a pseudo-operation with a literal expansion,
        # dump that literal expansion.
        if insn.literal_pseudo_op is not None:
            expansion = insn.literal_pseudo_op

        # If this instruction has a special-case in the assembler, use it. We
        # checked when loading our instruction definitions that if the
        # instruction claims to have a special-case assembler, it really does.
        if insn.python_pseudo_op:
            where = '{}:{}'.format(self.in_path, self.line_number)
            po_assembler = _PSEUDO_OP_ASSEMBLERS[insn.mnemonic]
            expansion = po_assembler(where, op_to_expr)

        reconstructed = self.key_sym + ''.join(self.acc).rstrip()
        assert '\n' not in reconstructed

        if expansion is not None:
            self.out_handle.write(
                '# pseudo-expansion for: {}\n'.format(reconstructed))
            for entry in expansion:
                self.out_handle.write('.line {}\n{}\n'.format(
                    self.line_number - 1, entry))
            return

        # If this instruction comes from the rv32i instruction set, we can just
        # pass it straight through.
        if insn.rv32i:
            self.out_handle.write('.line {}\n{}\n'.format(
                self.line_number - 1, reconstructed))
            return

        # If we don't know an encoding for this instruction, we're not going to
        # have much chance.
        if insn.encoding is None:
            raise RuntimeError(
                '{}:{}: Instruction {!r} has no encoding.'.format(
                    self.in_path, self.line_number, insn.mnemonic))

        # A custom instruction. We have two possible approaches.
        #
        #  1. Generate a .insn line. This is fine if the encoding happens to
        #     map on to one of the encodings that riscv32-unknown-elf-as
        #     supports, but won't work otherwise.
        #
        #  2. Just generate the bits by hand. This is fine if we can resolve
        #     everything, but it won't work if there are any relocs to deal
        #     with.
        #
        # Option 1 is nicer, and actually makes our lives easier: we don't have
        # to properly parse expressions for immediate operands. But we don't
        # know that every instruction has an encoding that maps perfectly on to
        # one of supported encoding schemes. Those that do appear in
        # self.mnem_to_rve. We try option 1 first, and fall back on option 2 if
        # it fails.
        rve = self.mnem_to_rve.get(self.key_sym.lower())
        if rve is not None:
            line = self.mk_rve_line(insn, rve, op_to_expr)
        else:
            line = self.mk_raw_line(insn, op_to_expr)

        self.out_handle.write('# {}\n.line {}\n{}\n'.format(
            reconstructed, self.line_number - 1, line))

    def _continue_block_comment(self, line: str, pos: int) -> int:
        '''Continue whitespace matching in a block comment

        Return end pos. Clear self.in_comment if we get to the end before EOL.

        '''
        assert self.in_comment

        # Search from pos for */
        idx = line.find('*/', pos)

        # If there is no such index, return EOL (and leave self.in_comment
        # set). Don't eat the \n at the end of the line: that will be added by
        # take_line.
        if idx == -1:
            return len(line) - 1

        # Otherwise, update pos to just after it and then eat any trailing
        # whitespace.
        assert 0 <= idx <= len(line) - 2

        self.in_comment = False
        return self._eat_ws(line, idx + 2)

    def _continue_string(self, line: str, pos: int) -> int:
        '''Continue reading a string'''
        assert self.in_string
        assert self.state == 1

        while True:
            # Search from pos for " (end of string) or \ (possible escape
            # sequence)
            quot_idx = line.find('"', pos)
            esc_quot_idx = line.find('\\"', pos)

            if max(quot_idx, esc_quot_idx) < 0:
                # EOL within string.
                self.acc.append(line[pos:])
                return len(line)

            if quot_idx < 0:
                # No " before EOL, but there is a \". Eat that and keep going.
                self.acc.append(line[pos:esc_quot_idx + 2])
                pos = esc_quot_idx + 2
                continue

            if esc_quot_idx < 0 or quot_idx < esc_quot_idx:
                # Either no \" or " comes first anyway
                self.acc.append(line[pos:quot_idx + 1])
                self.in_string = False
                return quot_idx + 1

    def _eat_ws(self, line: str, pos: int) -> int:
        '''Consume whitespace, updating FSM state if necessary'''
        # Eat any blanks
        match = re.match(r'[\t ]+', line[pos:])
        if match:
            end = match.end()
            self.acc.append(' ')
            pos += end

        # Return if at EOL
        if pos == len(line):
            return pos

        # Spot a line comment ('#'). In that case, eat to EOL and return.
        if line[pos] == '#':
            return len(line) - 1

        # The other possibility is a block comment ('/*'). If we're not looking
        # at that, we can return the current position.
        if line[pos:pos + 2] != '/*':
            return pos

        # Otherwise, eat the /* and switch to reading block comments. Add a
        # single space to acc to make sure we tokenize properly in examples
        # like "foo/* xxx */bar"
        self.in_comment = True
        self.acc.append(' ')

        return self._continue_block_comment(line, pos + 2)

    def _eat_optional_label(self, line: str, pos: int) -> Tuple[int, bool]:
        '''Consume an optional label'''
        assert self.state == 0
        match = re.match(r'[0-9a-zA-Z_$.]+:', line[pos:])
        if match is None:
            return (pos, False)

        end = pos + match.end()
        self.acc.append(line[pos:end])
        return (self._eat_ws(line, end), True)

    def _eat_labels(self, line: str, pos: int) -> int:
        '''Consume zero or more labels'''
        assert self.state == 0
        found = True
        while found:
            pos, found = self._eat_optional_label(line, pos)
        return pos

    def _eat_optional_token(self, line: str, pos: int) -> int:
        '''Consume an optional token'''
        assert self.state == 1
        assert self.key_sym is not None
        assert not self.in_comment
        assert not self.in_string

        assert pos < len(line)
        if line[pos] == '"':
            self.acc.append(line[pos])
            return self._continue_string(line, pos + 1)

        match = re.match(r'[^ \t"]*', line[pos:])
        assert match is not None
        end = pos + match.end()
        self.acc.append(match.group(0))
        return self._eat_ws(line, end)

    def _insn_for_keysym(self) -> Insn:
        '''Find an instruction for the current key symbol'''
        assert self.key_sym is not None

        # Most of the time, we'd hope the key sym appears in mnemonic_to_insn
        low_key_sym = self.key_sym.lower()
        insn = self.insns_file.mnemonic_to_insn.get(low_key_sym)
        if insn is not None:
            return insn

        # But we could have a glued operation, so key_sym might contain a
        # following operation. Find the longest mnemonic with glued operations
        # that is a prefix of key_sym (assuming there is one).
        for insn in self.glued_insns_dec_len:
            if low_key_sym.startswith(insn.mnemonic):
                return insn

        raise RuntimeError('{}:{}: Unknown mnemonic: {!r}.'.format(
            self.in_path, self.line_number, self.key_sym))

    def _end_stmt_line(self) -> None:
        '''Called at end of a stmt line to deal with any completed statement'''
        assert self.state == 1
        assert self.key_sym is not None

        # If we're still in a comment or a string, keep going
        if self.in_comment or self.in_string:
            return

        # Otherwise, set state back to zero (@ beginning of statement)
        self.state = 0

        # If key_sym is a directive (starts with '.'), we can just pass it
        # straight through.
        if self.key_sym.startswith('.'):
            self.out_handle.write(self.key_sym)
            self.out_handle.write(''.join(self.acc))
            self.acc = []
            self.key_sym = None
            return

        insn = self._insn_for_keysym()

        # Gather up everything after the mnemonic (possibly including some
        # glued operands) as a string.
        operands_str = self.key_sym[len(insn.mnemonic):] + ''.join(self.acc)

        match = insn.asm_pattern.match(operands_str.rstrip())
        if match is None:
            raise RuntimeError(
                '{}:{}: Cannot match syntax for {!r} ({!r}).'.format(
                    self.in_path, self.line_number, self.key_sym,
                    insn.syntax.render_doc()))

        op_to_val = {}  # type: Dict[str, Optional[str]]
        for op, grp in insn.pattern_op_to_grp.items():
            op_to_val[op] = match.group(grp)

        self.gen_line(insn, op_to_val)
        self.acc = []
        self.key_sym = None
        return

    def _continue_stmt(self, line: str, pos: int) -> None:
        '''Continue reading statement, up to EOL'''
        assert self.state == 1
        assert self.key_sym is not None
        assert not self.in_comment
        assert not self.in_string

        pos = self._eat_ws(line, pos)
        while pos < len(line):
            pos = self._eat_optional_token(line, pos)

        self._end_stmt_line()

    def _take_stmt_body(self, line: str, pos: int) -> None:
        '''Read the body of a statement'''
        assert self.state == 0
        assert self.key_sym is None
        assert pos < len(line)

        match = re.match(r'[0-9a-zA-Z_$.]+', line[pos:])
        if match is None:
            raise RuntimeError(
                '{}:{}:{}: Expected key symbol, but found {!r}.'.format(
                    self.in_path, self.line_number, pos, line[pos:]))

        self.key_sym = match.group(0)
        self.state = 1

        # We don't add key_sym to acc here: it will be read from self.key_sym
        # at the end of the instruction / directive.
        self._continue_stmt(line, pos + match.end())
        return

    def take_line(self, line: str) -> None:
        '''Consume a single line from the input'''
        pos = 0
        self.line_number += 1

        # Append a newline if the line doesn't have one. In practice, this just
        # happens with the last line of a file that doesn't end with a newline.
        if line and line[-1] != '\n':
            line = line + '\n'

        # Finish up any block comment
        if self.in_comment:
            # Strings can't contain nested comments
            assert not self.in_string

            pos = self._continue_block_comment(line, pos)
            if self.in_comment:
                self.acc.append('\n')
                return

        # Finish up any nested string
        if self.in_string:
            assert not self.in_comment
            assert self.state != 0
            pos = self._continue_string(line, pos)
            if self.in_string:
                return

        if self.state == 0:
            # Waiting for statement
            assert not self.in_string

            pos = self._eat_ws(line, pos)
            # If we're at EOL, we're done (degenerate statement or block comment)
            if line[pos] == '\n':
                self.acc.append('\n')
                return

            pos = self._eat_labels(line, pos)
            # If we're at EOL, we're done (degenerate statement)
            if line[pos] == '\n':
                self.acc.append('\n')
                return

            # Flush acc and then take the rest of the statement body. This
            # always consumes the rest of the line (but might not finish the
            # statement)
            self.out_handle.write(''.join(self.acc))
            self.acc = []
            self._take_stmt_body(line, pos)

        elif self.state == 1:
            # Part-way through a statement
            self._continue_stmt(line, pos)

        else:
            # Invalid state
            assert 0

    def at_eof(self) -> None:
        '''Finish any tidy-up at EOF'''
        if self.in_comment:
            raise RuntimeError('Reached EOF while still in a comment.')
        if self.in_string:
            raise RuntimeError('Reached EOF while still in a string.')


def transform_input(out_handle: TextIO, in_path: str, in_handle: TextIO,
                    insns_file: InsnsFile, glued_insns_dec_len: List[Insn],
                    mnem_to_rve: Dict[str, RVEncoding]) -> None:
    '''Transform an input file to make it suitable for riscv as'''
    transformer = Transformer(out_handle, in_path, insns_file,
                              glued_insns_dec_len, mnem_to_rve)
    for line in in_handle:
        transformer.take_line(line)
    transformer.at_eof()


def transform_inputs(out_dir: str, inputs: List[str], insns_file: InsnsFile,
                     mnem_to_rve: Dict[str, RVEncoding],
                     glued_insns_dec_len: List[Insn],
                     just_translate: bool) -> List[str]:
    '''Transform inputs to make them suitable for riscv as'''
    out_paths = []
    for idx, in_path in enumerate(inputs):
        out_path = os.path.join(out_dir, str(idx))
        out_paths.append(out_path)

        in_handle = sys.stdin
        pretty_in_path = 'stdin'
        out_handle = sys.stdout
        try:
            if in_path != '--':
                in_handle = open(in_path, 'r')
                pretty_in_path = in_path

            if not just_translate:
                out_handle = open(out_path, 'w')

            transform_input(out_handle, pretty_in_path, in_handle, insns_file,
                            glued_insns_dec_len, mnem_to_rve)

        finally:
            if in_handle is not sys.stdin and in_handle is not None:
                in_handle.close()
            if out_handle is not sys.stdout:
                out_handle.close()

    return out_paths


def run_binutils_as(other_args: List[str], inputs: List[str]) -> int:
    '''Run binutils' as on transformed inputs

    Performs no output redirection and returns the process's exit code.

    '''
    as_name = find_tool('as')

    default_args = [
        # Don't ask the linker to do relaxation because, in some cases, this
        # might generate a GP-relative load. OTBN doesn't treat x3 (gp)
        # specially, so this won't work.
        '-mno-relax',
        # OTBN isn't a standard RISC-V architecture, disable .riscv.attributes.
        '-mno-arch-attr',
        # OTBN is based on RV32I without any hard float support.
        '-mabi=ilp32',
    ]

    cmd = [as_name] + default_args + other_args + inputs
    try:
        return subprocess.run(cmd).returncode
    except FileNotFoundError:
        sys.stderr.write('Unknown command: {!r}.\n'.format(as_name))
        return 127


def main(argv: List[str]) -> int:
    files, other_args, flags = parse_positionals(argv)
    files = files or ['--']
    just_translate = '--otbn-translate' in flags

    # files is now a nonempty list of input files. Rather unusually, '--'
    # (rather than '-') denotes standard input.

    try:
        insns_file = load_insns_yaml()
    except RuntimeError as err:
        sys.stderr.write('{}\n'.format(err))
        return 1

    # A list of instructions that have "glued operations" (which means their
    # syntax doesn't require a space between the mnemonic and the first
    # operation). Ordered from longest to shortest mnemonic, so that you can
    # find a maximal prefix by linearly searching through the list and calling
    # startswith.
    glued_insns_dec_len = []
    for insn in insns_file.insns:
        if insn.glued_ops:
            glued_insns_dec_len.append(insn)
    glued_insns_dec_len.sort(key=lambda insn: len(insn.mnemonic), reverse=True)

    # Check that any instruction that claims to have a Python pseudo-op
    # assembler really does.
    for insn in insns_file.insns:
        if insn.python_pseudo_op:
            if insn.mnemonic not in _PSEUDO_OP_ASSEMBLERS:
                sys.stderr.write(
                    "Instruction {!r} has python-pseudo-op true, "
                    "but otbn_as.py doesn't have a custom assembler "
                    "for it.\n".format(insn.mnemonic))
                return 1

    # Try to match up OTBN instruction encodings with .insn schemes (as stored
    # in RISCV_FORMATS).
    mnem_to_rve = find_insn_schemes(insns_file.mnemonic_to_insn)

    with tempfile.TemporaryDirectory(suffix='.otbn-as') as tmpdir:
        try:
            transformed = transform_inputs(tmpdir, files, insns_file,
                                           mnem_to_rve, glued_insns_dec_len,
                                           just_translate)
        except RuntimeError as err:
            sys.stderr.write('{}\n'.format(err))
            return 1

        if just_translate:
            # transform_inputs already printed out the translated code. We're
            # done.
            return 0

        return run_binutils_as(transformed, other_args)


if __name__ == '__main__':
    sys.exit(main(sys.argv))
