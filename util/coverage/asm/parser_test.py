#!/usr/bin/env python3

# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Test for the parser module."""

import textwrap
import unittest

from util.coverage.asm.parser import (
    Statement,
    StmtType,
    run_parsing_pipeline,
)


class TestParser(unittest.TestCase):

    def test_run_parsing_pipeline(self) -> None:
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
        actual = run_parsing_pipeline(code)
        expected = [
            Statement(
                raw='\n',
                type=StmtType.COMMENT,
                mnemonic='',
                args='',
                lineno=1,
                colno=1,
            ),
            Statement(
                raw='# This is a comment.\n',
                type=StmtType.COMMENT,
                mnemonic='',
                args='',
                lineno=2,
                colno=1,
            ),
            Statement(
                raw='// Another comment\n',
                type=StmtType.COMMENT,
                mnemonic='',
                args='',
                lineno=3,
                colno=1,
            ),
            Statement(
                raw='/* Multi\n * line */\n',
                type=StmtType.COMMENT,
                mnemonic='',
                args='',
                lineno=4,
                colno=1,
            ),
            Statement(
                raw='.section .text // inline comment\n',
                type=StmtType.COMMENT,
                mnemonic='.section',
                args='.text',
                lineno=6,
                colno=1,
            ),
            Statement(
                raw='.global _start\n',
                type=StmtType.COMMENT,
                mnemonic='.global',
                args='_start',
                lineno=7,
                colno=1,
            ),
            Statement(
                raw='\n',
                type=StmtType.COMMENT,
                mnemonic='',
                args='',
                lineno=8,
                colno=1,
            ),
            Statement(
                raw='_start:\n',
                type=StmtType.LABEL,
                mnemonic='',
                args='_start',
                lineno=9,
                colno=1,
            ),
            Statement(
                raw='    //PRAGMA_COVERAGE: skip start\n',
                type=StmtType.PRAGMA,
                mnemonic='skip',
                args='start',
                lineno=10,
                colno=1,
            ),
            Statement(
                raw='    addi sp, sp, -16\n',
                type=StmtType.INSTR,
                mnemonic='addi',
                args='sp,sp,-16',
                lineno=11,
                colno=1,
            ),
            Statement(
                raw='    //PRAGMA_COVERAGE: skip stop\n',
                type=StmtType.PRAGMA,
                mnemonic='skip',
                args='stop',
                lineno=12,
                colno=1,
            ),
            Statement(
                raw='    li t0, \\\n       123\n',
                type=StmtType.INSTR,
                mnemonic='li',
                args='t0,123',
                lineno=13,
                colno=1,
            ),
            Statement(
                raw='    COVERAGE_ASM_AUTOGEN_MARK(t6, 0)\n',
                type=StmtType.COUNTER,
                mnemonic='COVERAGE_ASM_AUTOGEN_MARK',
                args='t6,0',
                lineno=15,
                colno=1,
            ),
            Statement(
                raw='    call some_func\n',
                type=StmtType.BRANCH,
                mnemonic='call',
                args='some_func',
                lineno=16,
                colno=1,
            ),
            Statement(
                raw='    beq t0, t1, _start\n',
                type=StmtType.BRANCH,
                mnemonic='beq',
                args='t0,t1,_start',
                lineno=17,
                colno=1,
            ),
            Statement(
                raw='.type func_foo, @function\n',
                type=StmtType.FUNCTYPE,
                mnemonic='.type',
                args='func_foo',
                lineno=18,
                colno=1,
            ),
            Statement(
                raw='func_foo:\n',
                type=StmtType.LABEL,
                mnemonic='',
                args='func_foo',
                lineno=19,
                colno=1,
            ),
            Statement(
                raw='    unimp\n',
                type=StmtType.TRAP,
                mnemonic='unimp',
                args='',
                lineno=20,
                colno=1,
            ),
            Statement(
                raw='.size func_foo, .-func_foo\n',
                type=StmtType.FUNCEND,
                mnemonic='.size',
                args='func_foo',
                lineno=21,
                colno=1,
            ),
        ]

        self.assertEqual(len(actual), len(expected))
        for i, (actual_stmt, expected_stmt) in enumerate(zip(actual, expected)):
            self.assertEqual(actual_stmt, expected_stmt)


if __name__ == '__main__':
    unittest.main()
