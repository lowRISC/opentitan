#!/usr/bin/env python3

# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Test for the tokenizer module."""

import textwrap
import unittest

from util.coverage.asm.tokenizer import (
    Statement,
    StmtType,
    cleanup_comments,
    cleanup_escape_sequences,
    parse_statement,
    run_tokenize_pipeline,
    split_mnemonic,
)


class TestTokenizer(unittest.TestCase):

    def test_cleanup_comments(self) -> None:
        code = textwrap.dedent("""
            // This is a single-line comment
            /* This is a
             * multi-line comment */
            # This is a preprocessor directive
            .global _start // inline comment
            .word 0x1234 # inline preprocessor comment
        """)
        expected_cleaned_code = textwrap.dedent("""
            ################################
            #####################################
            ##################################
            .global _start #################
            .word 0x1234 #############################
        """).replace("#", " ")

        self.assertEqual(cleanup_comments(code), expected_cleaned_code)

    def test_cleanup_escape_sequences(self) -> None:
        code = textwrap.dedent(r"""
            .string "Hello\nWorld"
            .asciz "Foo\tBar"
            .byte 0x0a \
                  0x0b
        """)
        expected_cleaned_code = textwrap.dedent("""
            .string "HelloxxWorld"
            .asciz "FooxxBar"
            .byte 0x0a         0x0b
        """)
        self.assertEqual(cleanup_escape_sequences(code), expected_cleaned_code)

    def test_split_mnemonic(self) -> None:
        test_cases = [
            # (input, expected_mnemonic, expected_args)
            ("lw  t0,  0(sp)", "lw", "t0,0(sp)"),
            ("call my_func", "call", "my_func"),
            ("addi sp, sp, -16", "addi", "sp,sp,-16"),
            ('.section .data, "aw" ', ".section", '.data,"aw"'),
            ("LABEL_FOR_TEST(name)", "LABEL_FOR_TEST", "name"),
            ("SOME_MACRO(a, b, c)", "SOME_MACRO", "a,b,c"),
        ]

        for text, mnemonic, args in test_cases:
            with self.subTest(text=text):
                self.assertEqual(split_mnemonic(text), (mnemonic, args))

    def test_parse_statement(self) -> None:
        test_cases = [
            # (raw_input, expected_mnemonic, expected_args, expected_type)
            # Comments and empty lines
            ("\n", "//", "", StmtType.COMMENT),
            ("// comment\n", "//", "", StmtType.COMMENT),
            ("#define FOO 1\n", "//", "", StmtType.COMMENT),
            # Labels
            ("my_label:", "label", "my_label", StmtType.LABEL),
            ("  local_label:", "label", "local_label", StmtType.LABEL),
            # Branches
            ("beq t0, t1, target", "beq", "t0,t1,target", StmtType.BRANCH),
            ("jal ra, func", "jal", "ra,func", StmtType.BRANCH),
            ("call func", "call", "func", StmtType.BRANCH),
            ("ret", "ret", "", StmtType.BRANCH),
            ("mret", "mret", "", StmtType.BRANCH),
            ("tail func", "tail", "func", StmtType.BRANCH),
            # Traps
            ("unimp", "unimp", "", StmtType.TRAP),
            # Counters
            (
                "COVERAGE_ASM_AUTOGEN_MARK(t6, 0)",
                "COVERAGE_ASM_AUTOGEN_MARK",
                "t6,0",
                StmtType.COUNTER,
            ),
            (
                "COVERAGE_ASM_MANUAL_MARK(t6, -1)",
                "COVERAGE_ASM_MANUAL_MARK",
                "t6,-1",
                StmtType.COUNTER,
            ),
            # Pragmas
            (
                "  //PRAGMA_COVERAGE: section(name)",
                "section",
                "name",
                StmtType.PRAGMA,
            ),
            (
                "  //PRAGMA_COVERAGE: skip start",
                "skip",
                "start",
                StmtType.PRAGMA,
            ),
            (
                "  //PRAGMA_COVERAGE: autogen start",
                "autogen",
                "start",
                StmtType.PRAGMA,
            ),
            # Functype / Funcend
            (".type label, @function", ".type", "label", StmtType.FUNCTYPE),
            (".size label, .-label", ".size", "label", StmtType.FUNCEND),
            (".size label, 100", ".size", "label,100", StmtType.COMMENT),
            # Other instructions/directives
            ("li t0, 0", "li", "t0,0", StmtType.OTHER),
            (".global _start", ".global", "_start", StmtType.COMMENT),
            ("LABEL_FOR_TEST(x)", "LABEL_FOR_TEST", "x", StmtType.COMMENT),
            (".section .rodata", ".section", ".rodata", StmtType.COMMENT),
        ]

        for raw, mnemonic, args, stmt_type in test_cases:
            with self.subTest(raw=raw):
                code = cleanup_escape_sequences(cleanup_comments(raw))
                res = parse_statement(code, raw)
                self.assertEqual(res.mnemonic, mnemonic)
                self.assertEqual(res.args, args)
                self.assertEqual(res.type, stmt_type)

    def test_run_tokenize_pipeline(self) -> None:
        code = textwrap.dedent(r"""
            # This is a comment.
            // Another comment
            /* Multi
             * line */
            .section .text // inline comment
            .global _start

            _start:
                //PRAGMA_COVERAGE: skip start
                addi sp, sp, -16
                //PRAGMA_COVERAGE: skip stop
                li t0, \
                   123
                COVERAGE_ASM_AUTOGEN_MARK(t6, 0)
                call some_func
                beq t0, t1, _start
            .type func_foo, @function
            func_foo:
                unimp
            .size func_foo, .-func_foo
        """)
        actual = run_tokenize_pipeline(code)

        expected = [
            Statement(
                mnemonic="//",
                args="",
                raw="\n",
                type=StmtType.COMMENT,
                lineno=1,
                colno=1,
            ),
            Statement(
                mnemonic="//",
                args="",
                raw="# This is a comment.\n",
                type=StmtType.COMMENT,
                lineno=2,
                colno=1,
            ),
            Statement(
                mnemonic="//",
                args="",
                raw="// Another comment\n",
                type=StmtType.COMMENT,
                lineno=3,
                colno=1,
            ),
            Statement(
                mnemonic="//",
                args="",
                raw="/* Multi\n * line */\n",
                type=StmtType.COMMENT,
                lineno=4,
                colno=1,
            ),
            Statement(
                mnemonic=".section",
                args=".text",
                raw=".section .text // inline comment\n",
                type=StmtType.COMMENT,
                lineno=6,
                colno=1,
            ),
            Statement(
                mnemonic=".global",
                args="_start",
                raw=".global _start\n",
                type=StmtType.COMMENT,
                lineno=7,
                colno=1,
            ),
            Statement(
                mnemonic="//",
                args="",
                raw="\n",
                type=StmtType.COMMENT,
                lineno=8,
                colno=1,
            ),
            Statement(
                mnemonic="label",
                args="_start",
                raw="_start:\n",
                type=StmtType.LABEL,
                lineno=9,
                colno=1,
            ),
            Statement(
                mnemonic="skip",
                args="start",
                raw="    //PRAGMA_COVERAGE: skip start\n",
                type=StmtType.PRAGMA,
                lineno=10,
                colno=1,
            ),
            Statement(
                mnemonic="addi",
                args="sp,sp,-16",
                raw="    addi sp, sp, -16\n",
                type=StmtType.OTHER,
                lineno=11,
                colno=1,
            ),
            Statement(
                mnemonic="skip",
                args="stop",
                raw="    //PRAGMA_COVERAGE: skip stop\n",
                type=StmtType.PRAGMA,
                lineno=12,
                colno=1,
            ),
            Statement(
                mnemonic="li",
                args="t0,123",
                raw="    li t0, \\\n       123\n",
                type=StmtType.OTHER,
                lineno=13,
                colno=1,
            ),
            Statement(
                mnemonic="COVERAGE_ASM_AUTOGEN_MARK",
                args="t6,0",
                raw="    COVERAGE_ASM_AUTOGEN_MARK(t6, 0)\n",
                type=StmtType.COUNTER,
                lineno=15,
                colno=1,
            ),
            Statement(
                mnemonic="call",
                args="some_func",
                raw="    call some_func\n",
                type=StmtType.BRANCH,
                lineno=16,
                colno=1,
            ),
            Statement(
                mnemonic="beq",
                args="t0,t1,_start",
                raw="    beq t0, t1, _start\n",
                type=StmtType.BRANCH,
                lineno=17,
                colno=1,
            ),
            Statement(
                mnemonic=".type",
                args="func_foo",
                raw=".type func_foo, @function\n",
                type=StmtType.FUNCTYPE,
                lineno=18,
                colno=1,
            ),
            Statement(
                mnemonic="label",
                args="func_foo",
                raw="func_foo:\n",
                type=StmtType.LABEL,
                lineno=19,
                colno=1,
            ),
            Statement(
                mnemonic="unimp",
                args="",
                raw="    unimp\n",
                type=StmtType.TRAP,
                lineno=20,
                colno=1,
            ),
            Statement(
                mnemonic=".size",
                args="func_foo",
                raw=".size func_foo, .-func_foo\n",
                type=StmtType.FUNCEND,
                lineno=21,
                colno=1,
            ),
        ]

        self.assertEqual(actual, expected)

    def test_is_comment_property(self) -> None:
        self.assertTrue(Statement("", "", "", StmtType.COMMENT).is_comment)
        self.assertTrue(Statement("", "", "", StmtType.PRAGMA).is_comment)
        self.assertTrue(Statement("", "", "", StmtType.FUNCTYPE).is_comment)
        self.assertTrue(Statement("", "", "", StmtType.FUNCEND).is_comment)
        self.assertFalse(Statement("", "", "", StmtType.LABEL).is_comment)
        self.assertFalse(Statement("", "", "", StmtType.BRANCH).is_comment)
        self.assertFalse(Statement("", "", "", StmtType.OTHER).is_comment)

    def test_counter_property(self) -> None:
        stmt = Statement("MARK", "t6,123", "raw", StmtType.COUNTER)
        self.assertEqual(stmt.counter, 123)

        with self.assertRaises(ValueError):
            Statement("li", "t0,0", "raw", StmtType.OTHER).counter


if __name__ == "__main__":
    unittest.main()
