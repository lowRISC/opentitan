#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
import json
import sys
import re

from mdbook import utils as md_utils

BLOCK_DASHBOARD_PATTERN = re.compile(r'{{#block-dashboard\s+(\w+)\s*}}')
BLOCK_DASHBOARD_TEMPLATE = \
    r"<div class='dv-dashboard block-dashboard-compact' data-block-name='\1'></div>"


def main() -> None:
    md_utils.supports_html_only()

    # load both the context and the book from stdin
    context, book = json.load(sys.stdin)

    for chapter in md_utils.chapters(book["sections"]):
        chapter["content"] = \
            BLOCK_DASHBOARD_PATTERN.sub(BLOCK_DASHBOARD_TEMPLATE, chapter["content"])

    # dump the book into stdout
    print(json.dumps(book))


if __name__ == "__main__":
    main()
