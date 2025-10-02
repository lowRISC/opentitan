# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Module for tokenizing assembly code into statements."""

import dataclasses
import enum
import re

from rich.console import Console
from rich.text import Text
from typing import List, Optional, Tuple


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
    OTHER = enum.auto()


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
    StmtType.OTHER,
}


STMT_COLORS: dict[StmtType, str] = {
    StmtType.COMMENT: "magenta",
    StmtType.LABEL: "cyan",
    StmtType.BRANCH: "red",
    StmtType.TRAP: "red",
    StmtType.COUNTER: "green",
    StmtType.PRAGMA: "magenta",
    StmtType.FUNCTYPE: "blue",
    StmtType.FUNCEND: "blue",
    StmtType.OTHER: "",
}


@dataclasses.dataclass
class Statement:
    mnemonic: str
    args: str
    raw: str
    type: StmtType

    lineno: int = -1
    colno: int = -1
    block_counter: Optional[int] = None

    @property
    def counter(self) -> int:
        """Returns the counter value if the statement is a counter."""
        if self.type == StmtType.COUNTER:
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


def cleanup_comments(code: str) -> str:
    """Replaces comments with an equivalent number of spaces."""

    def replace_with_spaces(m: re.Match[str]) -> str:
        return ' ' * len(m.group(0))

    # Replace single-line comments (//...)
    code = re.sub(r'//.*', replace_with_spaces, code)
    # Replace C-preprocessor pragmas (#...)
    code = re.sub(r'#.*', replace_with_spaces, code)
    # Replace multi-line comments (/*...*/)
    code = re.sub(r'/\*.*?\*/', replace_with_spaces, code, flags=re.DOTALL)
    return code


def cleanup_escape_sequences(code: str) -> str:
    """Replaces common escape sequences with 'x' characters.

    Specifically handles newline escapes to preserve line structure.
    """

    def replace_with_xs(m: re.Match[str]) -> str:
        if m.group(0) == '\\\n':
            return ' ' * len(m.group(0))
        return 'x' * len(m.group(0))

    code = re.sub(r'\\.', replace_with_xs, code, flags=re.DOTALL)
    return code


def split_mnemonic(text: str) -> Tuple[str, str]:
    """Split at the first space or opening parenthesis"""
    text = text.strip()
    mnemonic, *remainder = re.split(r' |(?=\()', text, maxsplit=1)
    args = remainder[0] if remainder else ''
    mnemonic = re.sub(r'\s', '', mnemonic)
    args = re.sub(r'\s', '', args)

    if args.startswith('('):
        assert (
            args.endswith(')')
        ), f'Malformed args for mnemonic {mnemonic}: {args}'
        args = args[1:-1]

    return mnemonic, args


def parse_statement(code: str, raw: str) -> Statement:
    code = code.strip()

    # Empty or comment lines
    if code == '':
        # Check for special pragmas in the original raw line.
        if raw.strip().replace(' ', '').startswith('//PRAGMA_COVERAGE:'):
            args = raw.split(':', 1)[1].strip()
            mnemonic, args = split_mnemonic(args)
            return Statement(mnemonic, args, raw, StmtType.PRAGMA)

        return Statement('//', '', raw, StmtType.COMMENT)

    # Check for labels (lines ending with ':')
    if code.endswith(':'):
        label_text = code.removesuffix(':')
        return Statement('label', label_text, raw, StmtType.LABEL)

    # Handle instruction, directive and macro.
    mnemonic, args = split_mnemonic(code)

    line_type: StmtType = StmtType.OTHER
    if mnemonic.startswith('b') or mnemonic.startswith('j'):
        line_type = StmtType.BRANCH
    elif mnemonic in {'tail', 'call', 'ret', 'mret'}:
        line_type = StmtType.BRANCH
    elif mnemonic in {'unimp'}:
        line_type = StmtType.TRAP
    elif mnemonic in {'COVERAGE_ASM_AUTOGEN_MARK', 'COVERAGE_ASM_MANUAL_MARK'}:
        line_type = StmtType.COUNTER
    elif mnemonic in {'LABEL_FOR_TEST'}:
        # Treat LABEL_FOR_TEST as a comment. These are special macros for
        # testing with OpenOCD and do not impact the ROM's execution flow.
        line_type = StmtType.COMMENT
    elif mnemonic in {'.type'} and args.endswith(',@function'):
        # .type _rom_interrupt_vector_asm, @function
        args = args.removesuffix(',@function')
        line_type = StmtType.FUNCTYPE
    elif mnemonic in {'.size'} and '.-' in args:
        # .size _rom_interrupt_vector_asm, .-_rom_interrupt_vector_asm
        label = args.split(',', 1)[0]
        if args == f'{label},.-{label}':
            args = label
            line_type = StmtType.FUNCEND
        else:
            line_type = StmtType.COMMENT
    elif mnemonic.startswith('.'):
        line_type = StmtType.COMMENT

    return Statement(mnemonic, args, raw, line_type)


def split_statements(code: str, raw: str) -> List[Statement]:
    offset: int = 0
    lineno: int = 1
    colno: int = 1
    result: List[Statement] = []
    for line in code.splitlines(keepends=True):
        # Split line with ':\n?' but keep the separator.
        sep: List[int] = [0]
        sep.extend(m.end() for m in re.finditer(r':\n?', line))
        sep.append(len(line))
        segments: List[str] = [line[a:b] for a, b in zip(sep, sep[1:])]

        # Parse each segments.
        for text in segments:
            if text:
                raw_stmt: str = raw[offset: offset + len(text)]
                stmt: Statement = parse_statement(text, raw_stmt)
                stmt.lineno = lineno
                stmt.colno = colno
                result.append(stmt)
                offset += len(raw_stmt)
                if '\n' in raw_stmt:
                    lineno += raw_stmt.count('\n')
                    colno = 1
                colno += len(raw_stmt.rsplit('\n', 1)[-1])
    return result


def run_tokenize_pipeline(raw: str) -> List[Statement]:
    code: str = raw
    code = cleanup_comments(code)
    code = cleanup_escape_sequences(code)
    statements: List[Statement] = split_statements(code, raw)
    return statements
