# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log
import re
from typing import List, Match, Optional, Set, Union

import tabulate
from reggen.signal import Signal


def name_width(x: Signal) -> str:
    if x.bits.width() == 1:
        return x.name

    return '{}[{}:0]'.format(x.name, x.bits.msb)


def coderef(s: str) -> str:
    '''Return markdown code to refer to some element in the code'''
    return f"**`{s}`**"


def italic(s: str) -> str:
    '''Return markdown code to put a string in italic'''
    return f"*{s}*"


def bold(s: str) -> str:
    '''Return markdown code to put a string in bold'''
    return f"**{s}**"


def url(text: str, url: str) -> str:
    '''Return a markdown link to a URL'''
    return f"[{text}]({url})"


def get_reg_link(rname: str) -> str:
    '''Return regname with a link to itself'''
    return url(rname, "#" + rname.lower())


def title(title: str, level: int) -> str:
    '''return the markdown string that corresponds to a title of a certain level'''
    assert level <= 6, "commonmark does not handle more than 6 levels of title"
    return ('#' * level) + " " + title + '\n'


def wavejson(json: str) -> str:
    '''return the markdown code to embed a wavedrom bit-field register picture'''
    return f"\n```wavejson\n{json}\n```\n"


def split_paragraphs(s: str) -> List[str]:
    '''split a pseudo-markdown code into paragraphs'''
    return [paragraph.strip() for paragraph in re.split(r'\n(?:\s*\n)+', s)]


def md_safe_for_table(s: Union[str, List[str]]) -> str:
    '''
    Transform (a subset of) markdown into something that can be put
    in a markdown table cell. The input can either be a string (unsegmented
    markdown code) or a list of paragraphs

    Specifically, this function handle two corner cases:
    - muliline paragraph: line returns are transformed in spaces
    - paragraphs: new paragraphs are introduced using <br /> since it cannot be
      done in standard CommonMark
    '''
    # Start by splitting into paragraphs. The regex matches a newline followed
    # by one or more lines that just contain whitespace. Then in each
    # paragraph, line returns (ie not empty lines) are replace with a space
    # since they are a problem in tables where we must put everything on one line
    paras = split_paragraphs(s) if isinstance(s, str) else s

    paras = [re.sub(r"\n", " ", p) for p in paras]
    return "<br />".join(paras)


def table(header: List[str],
          rows: List[List[str]],
          colalign: Union[None, List[str]] = None) -> str:
    '''
    Return the markdown code for a table given a header and the rows.

    This function handles markdown idiocracies like not being able to
    handle multilines in tables and line braks (which are convert to <br />).
    Ff colalign is not None, each entry is the list specifies the align of a
    column and can be one of 'left', 'right' or 'center'
    '''
    header = [md_safe_for_table(x) for x in header]
    rows = [[md_safe_for_table(x) for x in row] for row in rows]
    # for some unknown reason, the "github" format of tabulate is "pipe" without
    # the align specifiers, but alignment is part of the GitHub Markdown format...
    return "\n" + tabulate.tabulate(rows, header, "pipe",
                                    colalign=colalign) + "\n\n"


def expand_paras(s: str, rnames: Set[str]) -> List[str]:
    '''
    Expand a description field to markdown.

    We also generate links to registers when a name is prefixed with a double
    exclamation mark. For example, if there is a register FOO then !!FOO or
    !!FOO.field will generate a link to that register.

    Returns a list of rendered paragraphs
    '''

    def fieldsub(match: Match[str]) -> str:
        base = match.group(1).partition('.')[0].lower()
        # If we do not find the register name, there is a chance that this
        # is a multireg that spans more than one register entry.
        # We check whether at least _0 and _1 exist (via a set intersection),
        # and still insert the link if these names exist.
        # Note that we do not have to modify the link name since we insert
        # a link target without the index suffix right before the first multireg
        # entry in the register table.
        mr_names = set([base + "_0", base + "_1"])
        if base in rnames or len(rnames & mr_names) == 2:
            if match.group(1)[-1] == ".":
                return ('<a href="#' + base + '"><code class=\"reg\">' +
                        match.group(1)[:-1] + '</code></a>.')
            else:
                return ('<a href="#' + base + '"><code class=\"reg\">' +
                        match.group(1) + '</code></a>')
        log.warn('!!' + match.group(1).partition('.')[0] +
                 ' not found in register list.')
        return match.group(0)

    # substitute reference to registers and fields
    return [
        re.sub(r"!!([A-Za-z0-9_.]+)", fieldsub, p) for p in split_paragraphs(s)
    ]


def render_td(s: str, rnames: Set[str]) -> str:
    '''Expand a description field for use in a markdown table. See expand_paras for
    details about the supported format.
    '''
    return md_safe_for_table(expand_paras(s, rnames))
