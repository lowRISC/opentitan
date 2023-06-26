#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""mdbook preprocessor that inserts definitions from C header files.
"""

import json
import sys
import re
from pathlib import Path

from mdbook import utils as md_utils

REPO_TOP = Path(__file__).resolve().parents[1]

# Matching: {{#header-snippet filename defn }}
HEADER_SNIPPET = re.compile(r'\{\{#header-snippet\s+?(.+?)\s+?(.+?)\s*?\}\}')

# Path to REPO_TOP on GitHub.
REPO_TOP_GH = "https://github.com/lowRISC/opentitan/tree/master/"


def is_struct(line: str, defn: str) -> bool:
    '''Returns true if `line` contains the start of a struct named `defn`.'''
    return (f'struct {defn} ' + '{') in line


def is_func(line: str, defn: str) -> bool:
    '''Returns true if `line` contains the start of a function named `defn`.'''
    return f' {defn}(' in line


def is_enum(line: str, defn: str) -> bool:
    '''Returns true if `line` contains the start of an enum named `defn`.'''
    return (f'enum {defn} ' + '{') in line


def is_typedef(line: str, defn: str) -> bool:
    '''Returns true if `line` contains the start of a typedef named `defn`.'''
    return line.startswith('typedef ') and line.endswith(f' {defn};\n')


def is_declaration(line: str, defn: str) -> bool:
    '''Returns true if `line` contains any declaration named `defn`.'''
    return (is_struct(line, defn) or is_enum(line, defn) or
            is_func(line, defn) or is_typedef(line, defn))


def get_header_snippet(m: re.Match) -> str:
    '''Given the filename and defintion name, create a Markdown snippet.

    This function uses a very simplistic method to get the declaration from the
    header file plus the comment above it, if available:
      - Find a mention of the definition that's not in a comment and matches a
        function, struct, enum, or typedef declaration pattern
      - Find the next ';' after that declaration pattern and end the snippet there
      - If the declaration is immediately preceded by a multi-line comment,
        include it in the snippet.
    '''
    filename = m.group(1)
    defn = m.group(2)
    if not Path.is_file(REPO_TOP / filename):
        raise RuntimeError(f'Could not locate {filename}')

    # Extract the code snippet along with the preceding docstring, if present.
    lineno = 1
    lines = []
    in_comment = False
    in_defn = False
    start_lineno = None
    end_token = None
    with open(REPO_TOP / filename) as header:
        for raw_line in header:
            # If the line has a //-style comment in it, don't match keywords
            # past it.
            if '//' in raw_line:
                line = raw_line.split('//')[0] + '\n'
            else:
                line = raw_line

            # Look for the start of a comment.
            if '/*' in line:
                in_comment = True

            # Look for the declaration.
            if not in_defn and not in_comment and is_declaration(line, defn):
                in_defn = True
                start_lineno = lineno
                if is_struct(line, defn):
                    # Structs use `;` to delimit members, so end on }.
                    end_token = '}'
                else:
                    # Everything else ends at the next `;` token.
                    end_token = ';'

            # Accumulate comments by default in case we hit the declaration
            # afterwards. If we've already found the declaration, append all
            # lines until we hit the end token.
            if in_comment or in_defn:
                lines.append(raw_line)
                if not in_comment and end_token in line:
                    break

            # Clear lines if we're not in a relevant block (e.g. newline or
            # unrelated declaration). Special-case ignore a macro that often
            # appears right before function declarations.
            if not in_defn and not in_comment:
                if not line.strip() == 'OT_WARN_UNUSED_RESULT':
                    lines = []

            # Look for the end of a comment.
            if in_comment and '*/' in line:
                in_comment = False

            lineno += 1

    if start_lineno is None:
        raise RuntimeError(f'Could not locate declaration of {defn} in {filename}')

    gh_link = f'{REPO_TOP_GH}{filename}#L{start_lineno}'
    link_text = f'{filename}#L{start_lineno}'
    lines_prefix = [f'[{link_text}]({gh_link}):\n', '```c\n']
    lines_suffix = ['```\n']
    return ''.join(lines_prefix + lines + lines_suffix)


if __name__ == "__main__":
    md_utils.supports_html_only()

    # Load both the context and the book from stdin.
    context, book = json.load(sys.stdin)

    # Insert the requested header snippets.
    for chapter in md_utils.chapters(book["sections"]):
        chapter["content"] = \
            HEADER_SNIPPET.sub(
                get_header_snippet,
                chapter["content"],
        )

    # Dump the book into stdout.
    print(json.dumps(book))
