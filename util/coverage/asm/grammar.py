# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Module for tokenizing assembly code using pyparsing."""

import pyparsing as pp
from pyparsing import Group, Literal, Opt
from util.coverage.asm.grammar_util import AsSpace


LF = pp.LineEnd()
Space = pp.White(" \t")
LineCont = "\\" + LF
Identifier = pp.Word(pp.alphanums + "._")

Pragma = (
    pp.Regex("// *PRAGMA_COVERAGE *: *") +
    Identifier("mnemonic") +
    pp.rest_of_line("args")
)

BlockComment = Literal("/*") + ... + "*/"
LineComment = Literal("//") + pp.rest_of_line
SharpComment = Literal("#") + pp.rest_of_line
Comment = BlockComment | LineComment | SharpComment

DoubleQuotedString = pp.QuotedString('"', multiline=True, unquote_results=False)
SingleQuotedString = pp.QuotedString("'", multiline=True, unquote_results=False)
String = DoubleQuotedString | SingleQuotedString

InstrOprands = pp.ZeroOrMore(
    AsSpace(Space) |
    AsSpace(Comment) |
    AsSpace(LineCont) |
    String |
    pp.Char(pp.printables)
)

Instr = Identifier("mnemonic") + InstrOprands("args")

Label = Identifier("args") + Literal(":")

EmptyLine = Opt(Space) + Group(Group(LF)("comment"))("body")

Statement = Group(
    (
        Opt(Space) +
        (
            Group(Pragma)("pragma") |
            Group(Comment)("comment") |
            Group(Label)("label") |
            Group(Instr)("instr")
        )("body") +
        Opt(LineComment) +
        Opt(Space) +
        Opt(LF)
    ) |
    EmptyLine
)

Grammar = pp.ZeroOrMore(Statement).leaveWhitespace()
