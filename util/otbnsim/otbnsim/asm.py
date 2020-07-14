# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from lark import Lark, Transformer, v_args, Token
import argparse
import sys
from struct import pack

from riscvmodel.isa import reverse_lookup
from .insn import *

from .variant import RV32IXotbn

otbn_grammar = r"""
start: statement+
statement: instruction
        | loop
        | "\n"

instruction: MNEMONIC operands? "\n"

operands: operand ("," operand)*

operand: REGNAME
    | NUMBER
    | addr_operand
    | select_operand
    | shift_operand
    | fg_operand

shift_operand: SHIFT_TYPE SHIFT_BYTES

fg_operand: "FG0" | "FG1"

select_operand: REGNAME "." SELECT

addr_operand: NUMBER "(" REGNAME ")"

loop: "LOOP"i REGNAME "(" "\n" statement+ ")" "\n"
    | "LOOPI"i NUMBER "(" "\n" statement+ ")" "\n"

MNEMONIC: ("a".."z" | "A".."Z" | ".")+
NUMBER: ("0".."9" | "a".."f" | "A".."F" | "x" | "-")+
REGNAME: "a".."z" NUMBER
SELECT: ("l" | "u" | "0".."3")
SHIFT_TYPE: ("<<" | ">>")
SHIFT_BYTES: NUMBER "B"
WHITESPACE: (" " | "\t" )+
COMMENT: "//" /[^\n]*/ "\n" | "/*" /(.|\n)+/ "*/"

%ignore COMMENT
%ignore WHITESPACE
"""


class lowerLoop:
    def flatten(stmtlist):
        flat = []
        for stmt in stmtlist:
            if stmt is None:
                continue
            if isinstance(stmt, list):
                flat += lowerLoop.flatten(stmt)
            else:
                flat.append(stmt)
        return flat

    def generate(self, t):
        if t.data == "start":
            return lowerLoop.flatten(
                [self.generate(stmt) for stmt in t.children])
        elif t.data == "statement":
            if len(t.children) > 0:
                return self.generate(t.children[0])
        elif t.data == "instruction":
            mnemonic = str(t.children[0]).lower().split(".")
            if len(mnemonic) == 1:
                ops = []
                mnemonic = mnemonic[0]
            else:
                # Can only be a "bn.<mnemonic>[.<mod>]+"
                assert mnemonic[0] == "bn"
                ops = mnemonic[2:] if len(mnemonic) > 2 else []
                mnemonic = "{}.{}".format(mnemonic[0], mnemonic[1])
            cls = reverse_lookup(mnemonic, RV32IXotbn)
            assert cls, "Unknown instruction: {}".format(mnemonic)
            insn = cls()
            if len(t.children) > 1:
                for o in t.children[1].children:
                    ops += self.generate(o)
            insn.ops_from_list(ops)
            return insn
        elif t.data == "operand":
            if isinstance(t.children[0], Token):
                return [t.children[0].value]
            else:
                return self.generate(t.children[0])
        elif t.data == "addr_operand":
            return [t.children[0].value, t.children[1].value]
        elif t.data == "select_operand":
            return ["{}.{}".format(t.children[0].value, t.children[1].value)]
        elif t.data == "shift_operand":
            return [t.children[0].value, t.children[1].value]
        elif t.data == "fg_operand":
            return [t.value]
        elif t.data == "loop":
            iterations = str(t.children[0])
            bodysize = len(t.children[1:])
            if t.children[0].type == "NUMBER":
                insn = InstructionLOOPI(int(iterations), bodysize)
            else:
                insn = InstructionLOOP(iterations, bodysize)
            insns = [insn]
            insns += [self.generate(insn) for insn in t.children[1:]]
            return insns
        # Fallthrough
        return None


def parse(text):
    otbn_parser = Lark(otbn_grammar)
    code = otbn_parser.parse(text)
    return lowerLoop().generate(code)


def output_asm(code, file):
    file.write("".join(["{}\n".format(insn) for insn in code]))


def output_carray(code, file):
    file.write("static const uint32_t code [] = {\n")
    code = ["    0x{:08x}, // {}".format(insn.encode(), insn) for insn in code]
    file.write("\n".join(code) + "\n")
    file.write("};\n")


def output_binary(code, file):
    for insn in code:
        file.write(pack("I", insn.encode()))



def output(code, outfile, format="asm"):
    output_funcs = {
        "asm": output_asm,
        "binary": output_binary,
        "carray": output_carray
    }
    output_funcs[format](code, outfile)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("infile",
                        nargs="?",
                        type=argparse.FileType('r'),
                        default=sys.stdin)
    parser.add_argument("outfile",
                        nargs="?",
                        type=argparse.FileType('wb'),
                        default=sys.stdout)
    parser.add_argument("-O",
                        "--output-format",
                        choices=["asm", "binary", "carray"],
                        default="asm")

    args = parser.parse_args()
    code = parse(args.infile.read())
    output(code, args.outfile, args.output_format)
