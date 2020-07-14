# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from lark import Lark, Token
import argparse
import sys
from collections import namedtuple

from struct import pack

from riscvmodel.isa import reverse_lookup
from .insn import *

from .variant import RV32IXotbn

otbn_grammar = r"""
start: statement+
label: LABEL ":"
statement: instruction
    | loop
    | label
    | "\n"

instruction: MNEMONIC operands? "\n"

operands: operand ("," operand)*

operand: REGNAME
    | NUMBER
    | addr_operand
    | select_operand
    | shift_operand
    | fg_operand
    | flag_operand
    | inc_operand
    | label_operand

label_operand:   LABEL
shift_operand:   REGNAME SHIFT_TYPE (SHIFT_BYTES | NUMBER)
fg_operand:      FGID
flag_operand:    (FGID ".")? FLAG
select_operand:  REGNAME "." SELECT
addr_operand:    NUMBER "(" REGNAME "+"i? ")"
inc_operand:     REGNAME "+"

loop: "LOOP"i REGNAME "(" "\n" statement+ ")" "\n"
    | "LOOPI"i NUMBER "(" "\n" statement+ ")" "\n"

MNEMONIC: ("a".."z" | "A".."Z" | ".")+
NUMBER: ("0".."9" | "a".."f" | "A".."F" | "x" | "-")+
REGNAME: ("x" | "w") ("0".."9")+
LABEL: ("a".."z" | "A".."Z") ("0".."9" | "a".."z" | "A".."Z" | "_")*
SELECT: ("l" | "u" | "0".."3")
SHIFT_TYPE: ("<<" | ">>")
SHIFT_BYTES: NUMBER ("B" | "b")
FGID: ("FG0" | "FG1")
FLAG: ("C" | "M" | "L" | "Z")
WHITESPACE: (" " | "\t" )+
COMMENT: "//" /[^\n]*/ "\n" | "/*" /(.|\n)+/ "*/"

%ignore COMMENT
%ignore WHITESPACE
"""

Target = namedtuple("Target", ["id"])
Label = namedtuple("Label", ["id"])
Insn = namedtuple("Insn", ["cls", "ops"])


class ProcessTree:
    @staticmethod
    def flatten(stmtlist):
        """
        Generates a flat list of statements

        This function removes all empty statements and flattens lists (former
        subtrees) into one linear list of the program statements.
        """
        flat = []
        for stmt in [stmt for stmt in stmtlist if stmt is not None]:
            if isinstance(stmt, list):
                flat += ProcessTree.flatten(stmt)
            else:
                flat.append(stmt)
        return flat

    @staticmethod
    def resolve(stmtlist):
        """
        Resolves all label references

        Build library of label addresses and resolve references. This is also
        the final stage where the actual instructions are generated from the
        class and operand information.
        """
        insns = []
        count = 0
        labels = {}
        for stmt in stmtlist:
            if isinstance(stmt, Label):
                labels[stmt.id] = count
            else:
                insns.append(stmt)
                count += 1
        pos = 0
        final = []
        for stmt in insns:
            insn = stmt.cls()
            ops = []
            for op in stmt.ops:
                if isinstance(op, Target):
                    tpos = labels[op.id]
                    ops.append((tpos - pos) * 4)
                else:
                    ops.append(op)
            insn.ops_from_list(ops)
            pos += 1
            final.append(insn)
        return final

    def generate(self, t):
        """
        Depth-first tree iteration that generates instructions from code

        First iterate over all elements of the parse tree and lookup
        instructions. It also lowers LOOP(i) body notation to the proper
        operand. Finally, flattens the tree to a linear list of statements and
        generates instructions and branch/jump offsets.
        """
        if t.data == "start":
            # After the first stage we have Target, Label, Insn or None, in
            # nested lists
            tree = [self.generate(stmt) for stmt in t.children]
            # After the second stage we have only Target, Label and Insn left
            # and in a flat list
            tree = ProcessTree.flatten(tree)
            # After the last stage all targets resolved, only instances of
            # Instruction subclasses are left
            return ProcessTree.resolve(tree)
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
            if len(t.children) > 1:
                for o in t.children[1].children:
                    ops += self.generate(o)
            insn = Insn(cls=cls, ops=ops)
            return insn
        elif t.data == "operand":
            assert len(t.children) == 1
            if isinstance(t.children[0], Token):
                return [t.children[0].value]
            else:
                return self.generate(t.children[0])
        elif t.data == "addr_operand":
            return [t.children[0].value, t.children[1].value]
        elif t.data == "select_operand":
            return ["{}.{}".format(t.children[0].value, t.children[1].value)]
        elif t.data == "shift_operand":
            return [
                t.children[0].value, t.children[1].value, t.children[2].value
            ]
        elif t.data == "flag_operand":
            return [token.value for token in t.children]
        elif t.data == "fg_operand":
            return [token.value for token in t.children]
        elif t.data == "inc_operand":
            return [t.children[0].value + "+"]
        elif t.data == "label_operand":
            return [Target(id=t.children[0].value)]
        elif t.data == "loop":
            iterations = str(t.children[0])
            bodysize = len(t.children[1:])
            if t.children[0].type == "NUMBER":
                insn = Insn(cls=InstructionLOOPI,
                            ops=[int(iterations), bodysize])
            else:
                insn = Insn(cls=InstructionLOOPI, ops=[iterations, bodysize])
            insns = [insn]
            insns += [self.generate(insn) for insn in t.children[1:]]
            return insns
        elif t.data == "label":
            return [Label(id=t.children[0].value)]
        # Fallthrough
        return None


def parse(text):
    otbn_parser = Lark(otbn_grammar)
    code = otbn_parser.parse(text)
    return ProcessTree().generate(code)


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
