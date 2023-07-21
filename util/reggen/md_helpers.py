# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""A collection of functions that aid in generating markdown."""

import re
from typing import List, Match, Union, Optional

import tabulate
from reggen.signal import Signal


def name_width(x: Signal) -> str:
    '''Returns the name of the given signal followed by it's width.'''
    return (
        '{}[{}:0]'.format(x.name, x.bits.msb)
        if x.bits.width() != 1 else x.name
    )


def coderef(s: str) -> str:
    '''Return markdown code to refer to some element in the code'''
    return f"**`{s}`**"


def mono(s: str) -> str:
    '''Return markdown code to put a string in monospace'''
    return f"`{s}`"


def list_item(s: str) -> str:
    '''Return markdown code to put a string as a list item.

    Make sure to use succeeding a new line.
    '''
    return f"- {s}\n"


def italic(s: str) -> str:
    '''Return markdown code to put a string in italic'''
    return f"*{s}*"


def bold(s: str) -> str:
    '''Return markdown code to put a string in bold'''
    return f"**{s}**"


def url(text: str, url: str) -> str:
    '''Return a markdown link to a URL'''
    return f"[{text}]({url})"


def title(title: str, level: int) -> str:
    '''Return the markdown string that corresponds to a title of a certain level'''
    assert level <= 6, "commonmark does not handle more than 6 levels of title"
    return ('#' * level) + " " + title + '\n'


def wavejson(json: str) -> str:
    '''Return the markdown code to embed a wavedrom bit-field register picture'''
    return f"\n```wavejson\n{json}\n```\n"


def first_line(s: str) -> str:
    """Returns the first line of a string."""
    try:
        return s.split("\n")[0]
    except IndexError:
        # only one line so return the string.
        return s


def regref_to_link(s: str, file: Optional[str] = None) -> str:
    '''Replaces the register reference markup in the data files with markdown links.

    The markup used in data files is '!!REG_NAME.field'
    which is translated to '[`REG_NAME.field`](file#reg_name)'.

    Args:
        s (str): The content in which to substitute register links.
        file (str | None): An optional link to the file holding registers.

    Returns:
        str: The content after the substitutions have been performed.
    '''
    def linkify(match: Match[str]) -> str:
        name = match.group(1)
        register = match.group(1).partition('.')[0].lower()  # remove field
        return f"[`{name}`]({file if file else ''}#{register})"

    return re.sub(r"!!([A-Za-z0-9_.]+)", linkify, s)


def sanitise_for_md_table(s: str) -> str:
    '''Transform (a subset of) markdown into something that can be put
    in a markdown table cell.

    Specifically, this function handle two corner cases:
    - new lines, which are converted to spaces.
    - vertical bars, which are escaped.
    '''
    s = re.sub(r"\n", " ", s)
    s = re.sub(r"\|", r"\\\|", s)
    return s


def table(header: List[str],
          rows: List[List[str]],
          colalign: Union[None, List[str]] = None) -> str:
    '''Return the markdown code for a table given a header and the rows.

    The content is sanitised for use in a markdown table using `sanitise_for_md_table`.
    If `colalign` is not None, each entry is the list specifies the alignment of a
    column and can be either 'left', 'right' or 'center'.
    '''
    header = [sanitise_for_md_table(x) for x in header]
    rows = [[sanitise_for_md_table(x) for x in row] for row in rows]
    # For some unknown reason,
    # the "github" format of tabulate is "pipe" without the align specifiers,
    # despite alignment being part of the GitHub Markdown format.
    return "\n" + tabulate.tabulate(rows, header, "pipe", colalign=colalign) + "\n\n"
