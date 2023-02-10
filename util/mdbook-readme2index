#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""mdbook preprocessor that converts README.md to index.md

We use the built-in `index` preprocessor to rename our `README.md` files to `index.md`,
but it doesn't currently fixup links: https://github.com/rust-lang/mdBook/issues/984.
This is a temporary preprocessor to regex replace those links until upstream gets fixed.
"""

import json
import sys
import re

import mdbook

# Finds all markdown links, `[...](...)`,
# which link to a file called readme.md
# To check it isn't a link no colon, `:`, is allowed before the readme.md .
# `#` and '?' also aren't allowed before the readme.md,
# in case `readme.md` is not the filename but in fact a fragment or selector.
# It matches the link content before and after the readme into groups
# so that it can be substituted back into the file.
RM2IDX_PATTERN = re.compile(
    r"(\[[^\]]*\]\([^\)|#|:|\?]*)readme(\.md[^\)]*\))",
    re.IGNORECASE,
)


def main() -> None:
    if len(sys.argv) > 2:
        if (sys.argv[1], sys.argv[2]) == ("supports", "html"):
            sys.exit(0)
        else:
            sys.exit(1)

    # load both the context and the book from stdin
    context, book = json.load(sys.stdin)

    chapters_gen = mdbook.chapters(book["sections"])
    for chapter in chapters_gen:
        chapter["content"] = RM2IDX_PATTERN.sub(r"\1index\2", chapter["content"])

    # dump the book into stdout
    print(json.dumps(book))


if __name__ == "__main__":
    main()
