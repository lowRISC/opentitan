# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Module for parsing assembly code into statements."""

import copy
import dataclasses
import enum

from rich.console import Console
from rich.text import Text
from typing import List, Optional

from util.coverage.asm.grammar import Grammar
from util.coverage.asm.grammar_util import get_raw_text, get_text


console = Console()


class StmtType(enum.Enum):
    COMMENT = enum.auto()
    LABEL = enum.auto()
    BRANCH = enum.auto()
    TRAP = enum.auto()
    COUNTER = enum.auto()
    PRAGMA = enum.auto()
    FUNCTYPE = enum.auto()
    FUNCEND = enum.auto()
    INSTR = enum.auto()


COMMENT_TYPES: set[StmtType] = {
    StmtType.COMMENT,
    StmtType.FUNCTYPE,
    StmtType.FUNCEND,
    StmtType.PRAGMA,
}


CODE_TYPES: set[StmtType] = {
    StmtType.BRANCH,
    StmtType.TRAP,
    StmtType.COUNTER,
    StmtType.INSTR,
}


STMT_COLORS: dict[StmtType, str] = {
    StmtType.COMMENT: 'magenta',
    StmtType.LABEL: 'cyan',
    StmtType.BRANCH: 'red',
    StmtType.TRAP: 'red',
    StmtType.COUNTER: 'green',
    StmtType.PRAGMA: 'magenta',
    StmtType.FUNCTYPE: 'blue',
    StmtType.FUNCEND: 'blue',
    StmtType.INSTR: '',
}


@dataclasses.dataclass
class Statement:
    raw: str
    type: StmtType
    mnemonic: str
    args: str
    lineno: int
    colno: int
    block_counter: Optional[int] = None

    """Represents a single statement in the assembly code.

    Attributes:
        raw: The original raw text of the statement, including whitespace
             and comments.
        type: The classified type of the statement (e.g., COMMENT, LABEL, INSTR).
        mnemonic: The primary instruction or directive keyword (e.g., 'addi',
                  '.section'). Empty for comments or labels.
        args: The arguments or operands of the instruction/directive,
              normalized with no space (e.g., 'sp,sp,-16').
        lineno: The 1-based line number where the statement starts.
        colno: The 1-based column number where the statement starts.
        block_counter: An optional integer indicating the basic block ID this
                       statement belongs to, used for coverage analysis.
    """

    @property
    def counter(self) -> int:
        """Returns the counter value if the statement is a counter."""
        if self.type == StmtType.COUNTER:
            # e.g. COVERAGE_ASM_MANUAL_MARK(t6,0)
            return int(self.args.split(',')[1].strip())
        raise ValueError('Statement is not a counter type')

    @property
    def is_comment(self) -> bool:
        return self.type in COMMENT_TYPES

    @property
    def is_code(self) -> bool:
        return self.type in CODE_TYPES

    def pretty_print(self) -> None:
        text = Text(self.raw, style=STMT_COLORS[self.type])
        console.print(text, end='')


def classify_instruction(stmt: Statement) -> Statement:
    """Classifies an instruction statement based on its mnemonic and arguments.

    This function examines an `instr` type statement and reclassifies it
    into more specific types like BRANCH, TRAP, COUNTER, etc. based on common
    assembly patterns and special macros.

    Args:
        stmt: The `Statement` object to classify.

    Returns:
        A new `Statement` object with the potentially updated type. If the
        input statement's type is not 'instr', it is returned unchanged.
    """
    stmt = copy.deepcopy(stmt)

    if stmt.type != StmtType.INSTR:
        return stmt

    mnemonic = stmt.mnemonic

    if mnemonic.startswith('b') or mnemonic.startswith('j'):
        stmt.type = StmtType.BRANCH
    elif mnemonic in {'tail', 'call', 'ret', 'mret'}:
        stmt.type = StmtType.BRANCH
    elif mnemonic in {'unimp'}:
        stmt.type = StmtType.TRAP
    elif mnemonic in {'COVERAGE_ASM_AUTOGEN_MARK', 'COVERAGE_ASM_MANUAL_MARK'}:
        stmt.type = StmtType.COUNTER
    elif mnemonic in {'LABEL_FOR_TEST'}:
        # Treat LABEL_FOR_TEST as a comment. These are special macros for
        # testing with OpenOCD and do not impact the ROM's execution flow.
        stmt.type = StmtType.COMMENT
    elif mnemonic in {'.type'} and stmt.args.endswith(',@function'):
        # .type _rom_interrupt_vector_asm, @function
        stmt.args = stmt.args.removesuffix(',@function')
        stmt.type = StmtType.FUNCTYPE
    elif mnemonic in {'.size'} and '.-' in stmt.args:
        # .size _rom_interrupt_vector_asm, .-_rom_interrupt_vector_asm
        label = stmt.args.split(',', 1)[0]
        if stmt.args == f'{label},.-{label}':
            stmt.args = label
            stmt.type = StmtType.FUNCEND
        else:
            stmt.type = StmtType.COMMENT
    elif mnemonic.startswith('.'):
        stmt.type = StmtType.COMMENT

    return stmt


def run_parsing_pipeline(code: str):
    parsed = Grammar.parseString(code, parseAll=True)
    result: List[Statement] = []
    lineno: int = 1
    colno: int = 1
    for node in parsed:
        raw = get_raw_text(node)
        if not raw:  # Empty line end
            continue
        body = node.body[0]

        # Normalize operand string
        args = get_text(body.args).strip().replace(' ', '')
        if args.startswith('(') and args.endswith(')'):
            args = args[1:-1]

        result.append(
            classify_instruction(
                Statement(
                    raw=raw,
                    type=StmtType[body.get_name().upper()],
                    mnemonic=body.mnemonic,
                    args=args,
                    lineno=lineno,
                    colno=colno,
                )
            )
        )

        # Update location info
        if '\n' in raw:
            lineno += raw.count('\n')
            colno = 1
        colno += len(raw.rsplit('\n', 1)[-1])

    # Reconstruction sanity check
    reconstruction = ''.join(s.raw for s in result)
    assert reconstruction == code, 'Reconstruction failed'

    return result
