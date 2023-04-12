#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""mdbook preprocessor for wavejson code-blocks.

It surrounds wavejson code-blocks with script tags of type WaveDrom.
"""

import json
import sys
import re

from mdbook import utils as md_utils

WAVEJSON_PATTERN = re.compile("```wavejson\n(.+?)\n```", re.DOTALL)
WAVEJSON_REPLACE = r'<script type="WaveDrom">\1</script>'


def main() -> None:
    if len(sys.argv) > 2:
        if (sys.argv[1], sys.argv[2]) == ("supports", "html"):
            sys.exit(0)
        else:
            sys.exit(1)

    # load both the context and the book from stdin
    context, book = json.load(sys.stdin)

    for chapter in md_utils.chapters(book["sections"]):
        chapter["content"] = \
            WAVEJSON_PATTERN.sub(WAVEJSON_REPLACE, chapter["content"])

    # dump the book into stdout
    print(json.dumps(book))


if __name__ == "__main__":
    main()
