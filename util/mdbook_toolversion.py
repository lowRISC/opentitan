#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
import json
import sys
import re

from mdbook import utils as md_utils
import check_tool_requirements

# We are looking to match on the following example strings
# {{#tool-version verible }}
TOOLVERSION_PATTERN = re.compile(r'\{\{#tool-version\s+(.+?)\s*\}\}')


def main() -> None:
    md_utils.supports_html_only()

    tool_requirements = check_tool_requirements.read_tool_requirements()

    # load both the context and the book from stdin
    context, book = json.load(sys.stdin)

    for chapter in md_utils.chapters(book["sections"]):
        # Add in the minimum tool version
        chapter['content'] = TOOLVERSION_PATTERN.sub(
            repl=lambda m: tool_requirements.get(m.group(1)).min_version,
            string=chapter['content'])

    # dump the book into stdout
    print(json.dumps(book))


if __name__ == "__main__":
    main()
