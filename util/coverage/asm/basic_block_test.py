#!/usr/bin/env python3

# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Test for the basic block module."""

import re
import textwrap
import unittest

from util.coverage.asm.basic_block import (
    apply_block_counter,
    apply_skip_pragma,
    ignore_data_section,
    ignore_unreachable_code,
    propagate_counter,
    split_basic_blocks,
)
from util.coverage.asm.parser import (
    StmtType,
    run_parsing_pipeline,
)


def _remove_block_boundary(text: str) -> str:
    return re.sub(r'====.*====\n', '', text)


class TestBasicBlock(unittest.TestCase):

    def test_apply_skip_pragma(self) -> None:
        testcase = [
            # (code, expected_type)
            ('li t0, 0', StmtType.INSTR),
            ('//PRAGMA_COVERAGE: skip start', StmtType.COMMENT),
            ('addi t0, t0, 1', StmtType.COMMENT),
            ('//PRAGMA_COVERAGE: skip stop', StmtType.COMMENT),
            ('li t1, 0', StmtType.INSTR),
        ]
        code_list, expected_types = zip(*testcase)
        code = '\n'.join(code_list)
        statements = run_parsing_pipeline(code)
        actual = apply_skip_pragma(statements)
        actual_types = tuple(stmt.type for stmt in actual)
        self.assertEqual(actual_types, expected_types)

    def test_ignore_data_section(self) -> None:
        testcase = [
            # (code, expected_type)
            ('.section .rodata, "a"', StmtType.COMMENT),
            ('label_rodata:', StmtType.COMMENT),
            ('.section .text, "ax"', StmtType.COMMENT),
            ('li t0, 0', StmtType.INSTR),
            ('.section .data, "aw"', StmtType.COMMENT),
            ('label_data:', StmtType.COMMENT),
            ('.section .bss', StmtType.COMMENT),
            ('label_bss:', StmtType.COMMENT),
        ]
        code_list, expected_types = zip(*testcase)
        code = '\n'.join(code_list)
        statements = run_parsing_pipeline(code)
        acutal = ignore_data_section(statements)
        actual_types = tuple(stmt.type for stmt in acutal)
        self.assertEqual(actual_types, expected_types)

    def test_ignore_unreachable_code(self) -> None:
        testcase = (
            # (input, is_comment)
            # ====================================
            # Lines after unimp should be ignored
            ('test_unimp:', False),
            ('// passthrough', True),
            ('unimp', False),
            ('li t0, 0', True),
            ('// passthrough', True),
            ('li t0, 1', True),
            # ====================================
            # Lines after unconditional jump should be ignored
            ('test_j:', False),
            ('j somewhere', False),
            ('li t0, 0', True),
            # ====================================
            # Lines after unconditional jump (jal to x0) should be ignored
            ('test_jal_x0:', False),
            ('jal x0, somewhere', False),
            ('li t0, 0', True),
            ('test_jalr_x0:', False),
            ('jalr x0, 0(ra)', False),
            ('li t0, 0', True),
            # ====================================
            # Lines after ret/mret should be ignored
            ('test_ret:', False),
            ('ret', False),
            ('li t0, 0', True),
            ('test_mret:', False),
            ('mret', False),
            ('li t0, 0', True),
            # ====================================
            # Conditional branches should not make code unreachable
            ('test_conditional:', False),
            ('bne t0, t1, somewhere', False),
            ('li t0, 0', False),  # This should still be reachable
            # ====================================
            # .section directive should make code reachable again.
            ('test_section_reachable:', False),
            ('unimp', False),
            ('.section .vector,"ax"', True),  # This makes it reachable again
            ('li t0, 1', False),
        )
        code_list, _ = zip(*testcase)
        code = '\n'.join(code_list)
        statements = run_parsing_pipeline(code)
        statements = ignore_unreachable_code(statements)
        actual = tuple(
            (stmt.raw.strip(), stmt.type == StmtType.COMMENT)
            for stmt in statements
        )
        self.assertEqual(actual, testcase)

    def test_split_basic_blocks(self) -> None:
        self.maxDiff = None
        expected = textwrap.dedent("""\
            ========== Block(counter=None, up=False, down=False) ==========
            _start:
                li t0, 0
                call some_func
            ========== Block(counter=None, up=True, down=False) ==========
                beq t0, t1, _start
            ========== Block(counter=None, up=False, down=False) ==========
            another_label:
                addi sp, sp, -16
                j next_block
            ========== Block(counter=None, up=True, down=False) ==========
                unimp
            ========== Block(counter=None, up=False, down=True) ==========
            final_block:
                nop
        """)

        code = _remove_block_boundary(expected)
        statements = run_parsing_pipeline(code)
        blocks = split_basic_blocks(statements)
        actual = ''.join(map(str, blocks))
        self.assertEqual(actual, expected)

    def test_apply_block_counter(self) -> None:
        self.maxDiff = None
        expected = textwrap.dedent("""\
            ========== Block(counter=100, up=False, down=False) ==========
            _start:
                COVERAGE_ASM_MANUAL_MARK(t6, 100)
                li t0, 0
                call some_func
            ========== Block(counter=200, up=False, down=False) ==========
            another_block:
                li t0, 0
                COVERAGE_ASM_AUTOGEN_MARK(t6, 200)
                ret
            ========== Block(counter=None, up=False, down=True) ==========
            final_block:
                nop
        """)

        code = _remove_block_boundary(expected)
        statements = run_parsing_pipeline(code)
        blocks = split_basic_blocks(statements)
        blocks = apply_block_counter(blocks)
        actual = ''.join(map(str, blocks))
        self.assertEqual(actual, expected)

    def test_propagate_counter(self) -> None:
        self.maxDiff = None
        expected = textwrap.dedent("""\
            ========== Block(counter=0, up=False, down=True) ==========
            COVERAGE_ASM_MANUAL_MARK(t6, 0)
            addi t0, t0, 1
            ========== Block(counter=0, up=False, down=True) ==========
            block_1:
            // fall-through from Block 0
            li t1, 0
            ========== Block(counter=1, up=False, down=False) ==========
            block_2:
            COVERAGE_ASM_MANUAL_MARK(t6, 1)
            beq t0, t1, some_label
            ========== Block(counter=None, up=True, down=True) ==========
            // no counter
            nop
            ========== Block(counter=2, up=False, down=False) ==========
            block_4:
            // backward propagation stop.
            beq t0, t1, block_2
            ========== Block(counter=2, up=True, down=False) ==========
            // propagate up.
            call func_a
            ========== Block(counter=2, up=True, down=True) ==========
            // propagate up.
            COVERAGE_ASM_MANUAL_MARK(t6, 2)
        """)

        code = _remove_block_boundary(expected)
        statements = run_parsing_pipeline(code)
        blocks = split_basic_blocks(statements)
        blocks = apply_block_counter(blocks)
        blocks = propagate_counter(blocks)
        actual = ''.join(map(str, blocks))
        self.assertEqual(actual, expected)


if __name__ == '__main__':
    unittest.main()
