# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from .insn import *

import inspect
from pprint import pp


def extract_code(insn):
    def pretty(line):
        line = line.replace("model.state.intreg", "reg")
        line = line.replace("self.", "")
        return line

    code = inspect.getsource(insn.execute).splitlines()
    code = [pretty(line) for line in code[1:]]
    return "\n".join(code)


def doc_for_insn(insn):
    doc = {}
    doc["format"] = insn.get_isa_format()["id"]
    doc["description"] = inspect.getdoc(insn)
    doc["asm_signature"] = insn.asm_signature()
    doc["code"] = extract_code(insn)

    return doc


def doc_for_format(insn):
    return insn.get_isa_format(asdict=True)


print("++++ Instruction Formats")
pp(doc_for_format(InstructionLType))
pp(doc_for_format(InstructionLIType))
pp(doc_for_format(InstructionBNAType))
pp(doc_for_format(InstructionBNANType))
pp(doc_for_format(InstructionBNAFType))
pp(doc_for_format(InstructionBNAIType))
pp(doc_for_format(InstructionBNAMType))
pp(doc_for_format(InstructionBNAQType))
pp(doc_for_format(InstructionBNRType))

print("++++ Instructions")
pp(doc_for_insn(InstructionLOOP))
pp(doc_for_insn(InstructionLOOPI))
pp(doc_for_insn(InstructionBNAND))
pp(doc_for_insn(InstructionBNMULQACC))
