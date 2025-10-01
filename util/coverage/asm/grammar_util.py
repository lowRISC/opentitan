# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Utility functions for pyparsing grammar."""

import dataclasses
import pyparsing as pp
from typing import Union


@dataclasses.dataclass
class AsSpaceAction:
    raw: Union[pp.ParseResults, str]

    def __str__(self):
        return ' '

    def __repr__(self):
        return repr(str(self))


def AsSpace(expr):
    """Converts the matched parse result into a single space character.

    This is useful for suppressing the output of the matched expression,
    while retaining its original raw content for potential later use.
    """
    return expr.copy().set_parse_action(AsSpaceAction)


def get_raw_text(expr: Union[str, AsSpaceAction, pp.ParseResults]) -> str:
    """Extracts the raw text content from a parsed result.

    This function recursively traverses the parse result structure,
    reconstructing the original text.

    Args:
        expr: The element to extract raw text from.

    Returns:
        A string representing the raw text content.
    """

    if isinstance(expr, str):
        return expr
    elif isinstance(expr, AsSpaceAction):
        return get_raw_text(expr.raw)
    else:
        return ''.join(map(get_raw_text, expr))


def get_text(expr: Union[str, AsSpaceAction, pp.ParseResults]) -> str:
    """Extracts the processed text content from a parsed result.

    This function recursively traverses the parse result structure,
    reconstructing the text with replacements.

    Args:
        expr: The element to extract text from.

    Returns:
        A string representing the text content.
    """

    if isinstance(expr, str):
        return expr
    elif isinstance(expr, AsSpaceAction):
        return str(expr)
    else:
        return ''.join(map(get_text, expr))
