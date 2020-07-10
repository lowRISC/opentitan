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

operands: OPERAND ("," OPERAND)*

loop: "LOOP"i REGNAME "(" "\n" statement+ ")" "\n"
    | "LOOPI"i NUMBER "(" "\n" statement+ ")" "\n"

MNEMONIC: ("a".."z" | "A".."Z")+
NUMBER: ("0".."9")+
OPERAND: ("a".."z" | "A".."Z" | "0".."9" | "(" | ")" | "+" | "-")+
REGNAME: "a".."z" NUMBER
WHITESPACE: (" ")+
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
      return lowerLoop.flatten([self.generate(stmt) for stmt in t.children])
    elif t.data == "statement":
      if len(t.children) > 0:
        return self.generate(t.children[0])
    elif t.data == "instruction":
      mnemonic = str(t.children[0]).lower()
      cls = reverse_lookup(mnemonic, RV32IXotbn)
      assert cls
      insn = cls()
      if len(t.children) > 1:
        insn.ops_from_string(",".join([str(o) for o in t.children[1].children]))
      return insn
    elif t.data == "loop":
      iterations = str(t.children[0])
      bodysize = len(t.children[1:])
      if t.children[0].type == "NUMBER":
        insn = InstructionLOOPI(int(iterations), bodysize)
      else:
        insn = InstructionLOOP().ops_from_string("{},{}".format(iterations, bodysize))
      insns  = [insn]
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


def output_cstruct(code, file):
    file.write("struct uint32_t code [] = {\n")
    code = ["    0x{:08x}".format(insn.encode()) for insn in code]
    file.write(",\n".join(code)+"\n")
    file.write("};\n")

def output_binary(code, file):
    try:
      for insn in code:
        file.write(pack("I", insn.encode()))
    except TypeError:
      print("Cannot write binary to output file, no output produced..")

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("infile", nargs="?", type=argparse.FileType('r'), default=sys.stdin)
    parser.add_argument("outfile", nargs="?", type=argparse.FileType('wb'), default=sys.stdout)
    parser.add_argument("-O", "--output-format", choices=["asm", "binary", "cstruct"], default="asm")

    args = parser.parse_args()

    code = parse(args.infile.read())

    output_funcs = {"asm": output_asm, "binary": output_binary, "cstruct": output_cstruct}
    output_funcs[args.output_format](code, args.outfile)
