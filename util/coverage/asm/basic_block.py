# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Module for basic block analysis."""

import copy
import dataclasses

from typing import List, Optional

from util.coverage.asm.parser import Statement, StmtType


def apply_skip_pragma(statements: List[Statement]) -> List[Statement]:
    """Mark statement inside skip blocks as comments."""
    statements = copy.deepcopy(statements)
    skip = False
    for stmt in statements:
        if stmt.type == StmtType.PRAGMA:
            if stmt.mnemonic == 'skip' and stmt.args == 'start':
                skip = True
                stmt.type = StmtType.COMMENT
            elif stmt.mnemonic == 'skip' and stmt.args == 'stop':
                skip = False
                stmt.type = StmtType.COMMENT

        if skip:
            stmt.type = StmtType.COMMENT

    return statements


def ignore_data_section(statements: List[Statement]) -> List[Statement]:
    """Mark statement inside data sections as comments."""
    statements = copy.deepcopy(statements)
    skip = False
    for stmt in statements:
        if stmt.mnemonic == '.section':
            args = stmt.args.split(',', 1)
            if len(args) < 2 or not args[1].startswith('"'):
                # Unquoted second argument is subsection
                #     .section name[, "flags"]
                #     .section name[, subsection]
                skip = True
                continue

            skip = 'x' not in args[1]

        if skip:
            stmt.type = StmtType.COMMENT

    return statements


def ignore_unreachable_code(statements: List[Statement]) -> List[Statement]:
    """Mark statically unreachable code as comments.

    Code are considered unreachable if:
    * After another trap (e.g. `unimp`)
    * After unconditional jumps (e.g. `j`, `tail`)
    * After return (e.g. `ret`, `mret`)
    """
    statements = copy.deepcopy(statements)
    # maybe_reachable:
    # * True when the line MAY be reachable.
    # * False when the line MUST be unconditionally unreachable.
    maybe_reachable = True
    for stmt in statements:
        last_reachable = maybe_reachable

        # Update reachable status.
        if stmt.type == StmtType.TRAP:
            maybe_reachable = False
        elif stmt.type == StmtType.LABEL:
            maybe_reachable = True
        elif stmt.type == StmtType.BRANCH:
            if stmt.mnemonic in {'j', 'jr', 'tail', 'ret', 'mret'}:
                maybe_reachable = False
            # Expanded form of unconditional jump.
            if stmt.mnemonic in {'jal', 'jalr'}:
                rd = stmt.args.split(',', 1)[0]
                if rd in {'x0', 'zero'}:
                    maybe_reachable = False
        elif stmt.type == StmtType.COMMENT:
            if stmt.mnemonic in {'.section'}:
                maybe_reachable = True

        if not last_reachable and not maybe_reachable and stmt.is_code:
            stmt.type = StmtType.COMMENT

    return statements


@dataclasses.dataclass
class Block:
    """Basic block for code coverage.

    Properties:
        statements: A list of `Statement` objects within this block.
        counter: The counter ID associated with this block, or None if not
        assigned.
        up: True if the block above is executed when this block is executed.
        down: True if the block below is executed when this block is executed.
    """

    statements: List[Statement]
    counter: Optional[int] = None
    up: bool = False
    down: bool = True

    def banner(self) -> str:
        return (
            '=' * 10 +
            f' Block(counter={self.counter}, up={self.up}, down={self.down}) ' +
            '=' * 10
        )

    def __str__(self) -> str:
        out = [self.banner() + '\n']
        for stmt in self.statements:
            out.append(stmt.raw)
        return ''.join(out)

    def pretty_print(self) -> None:
        print(self.banner())
        for stmt in self.statements:
            stmt.pretty_print()


def split_basic_blocks(statements: List[Statement]) -> List[Block]:
    """Splits a list of statements into basic blocks.

    A new basic block is created under the following conditions:
    - After a branch or trap instruction.
    - Before a label.

    Args:
        statements: A list of `Statement` objects.

    Returns:
        A list of `Block` objects.
    """
    statements = copy.deepcopy(statements)
    blocks = [Block(statements=[], up=False, down=True)]

    for stmt in statements:
        if stmt.type == StmtType.LABEL:
            # A new block starts before a label.
            blocks.append(Block(statements=[], counter=None, up=False, down=True))

        blocks[-1].statements.append(stmt)

        # A new block starts after a branch or trap.
        if stmt.type in {StmtType.BRANCH, StmtType.TRAP}:
            blocks[-1].down = False
            blocks.append(Block(statements=[], up=True, down=True))

    # Remove empty blocks.
    return [b for b in blocks if b.statements]


def apply_block_counter(blocks: List[Block]) -> List[Block]:
    """Sets the counter ID if a counter statement is found within the block."""
    blocks = copy.deepcopy(blocks)
    for block in blocks:
        for stmt in block.statements:
            if stmt.type == StmtType.COUNTER:
                block.counter = stmt.counter
                break

    return blocks


def propagate_counter(blocks: List[Block]) -> List[Block]:
    """Propagate passthrough counters."""
    blocks = copy.deepcopy(blocks)

    # Forward propagation.
    # If a block doesn't have a counter but the previous block had one and there
    # is a 'down' connection, propagate the counter.
    # This handles fall-through blocks.
    last_counter: Optional[int] = None
    for block in blocks:
        if block.counter is None and last_counter is not None:
            block.counter = last_counter
        last_counter = block.counter if block.down else None

    # Backward propagation.
    # If a block doesn't have a counter but the next block had one and there is
    # an 'up' connection, propagate the counter.
    # This handles blocks that are reachable from a previous block without a
    # dedicate label.
    last_counter = None
    for block in reversed(blocks):
        if block.counter is None and last_counter is not None:
            block.counter = last_counter
        last_counter = block.counter if block.up else None

    return blocks


def set_statement_counter(blocks: List[Block]) -> List[Block]:
    """Set statement counters to the block counter."""
    blocks = copy.deepcopy(blocks)
    for block in blocks:
        for stmt in block.statements:
            stmt.block_counter = block.counter
    return blocks


def flatten_blocks(blocks: List[Block]) -> List[Statement]:
    """Flattens a list of blocks into a single list of statements."""
    statements: List[Statement] = []
    for block in blocks:
        statements.extend(block.statements)
    return statements


def run_analyze_pipeline(statements: List[Statement]) -> List[Block]:
    statements = apply_skip_pragma(statements)
    statements = ignore_data_section(statements)
    statements = ignore_unreachable_code(statements)
    blocks = split_basic_blocks(statements)
    blocks = apply_block_counter(blocks)
    return blocks
