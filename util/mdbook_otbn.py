#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""mdbook preprocessor that generates ISA tables for the OTBN.

The preprocessor also handles `{{#otbn-insn-ref ... }}` links to the ISA Table.
"""

import json
import sys
import re
from pathlib import Path
import tempfile
import subprocess

from mdbook import utils as md_utils

REPO_TOP = Path(__file__).resolve().parents[1]

# We are looking to match on the following example strings
# {{#otbn-isa base }}
OTBN_ISA_BASE_PATTERN = re.compile(r'\{\{#otbn-isa\s+base\s*\}\}')
OTBN_ISA_BASE_ENCODING_PATTERN = re.compile(r'\{\{#otbn-isa\s+base_encoding\s*\}\}')
OTBN_ISA_BIGNUM_PATTERN = re.compile(r'\{\{#otbn-isa\s+bignum\s*\}\}')
OTBN_ISA_BIGNUM_ENCODING_PATTERN = re.compile(r'\{\{#otbn-isa\s+bignum_encoding\s*\}\}')

# {{#otbn-insn-ref insn }}
OTBN_INSNREF_PATTERN = re.compile(r'\{\{#otbn-insn-ref\s+?(.+?)\s*?\}\}')

OTBN_SCRIPT = REPO_TOP / 'hw/ip/otbn/util/yaml_to_doc.py'
OTBN_CFG = REPO_TOP / 'hw/ip/otbn/data/insns.yml'
OTBN_IMPL = REPO_TOP / 'hw/ip/otbn/dv/otbnsim/sim/insn.py'


def main() -> None:
    md_utils.supports_html_only()

    (base_content, bignum_content, base_enc_content, bignum_enc_content) = get_listings()

    # load both the context and the book from stdin
    _context, book = json.load(sys.stdin)

    # Insert the instruction description / encoding tables where requested.
    # These descriptions must reside in the same file to then generate the instruction links
    # in other files pointing to the actual instructions.
    # If these details are present in multiple files, then:
    #   1) There would be redundant information in the documentation.
    #   2) Which one should we link to?
    isa_book_path = None
    for chapter in md_utils.chapters(book["sections"]):
        if chapter["source_path"] is None:
            continue

        if ((OTBN_ISA_BASE_PATTERN.search(chapter["content"])
             and OTBN_ISA_BIGNUM_PATTERN.search(chapter["content"])
             and OTBN_ISA_BASE_ENCODING_PATTERN.search(chapter["content"])
             and OTBN_ISA_BIGNUM_ENCODING_PATTERN.search(chapter["content"]))):

            chapter["content"] = OTBN_ISA_BASE_PATTERN.sub(base_content, chapter["content"])
            chapter["content"] = OTBN_ISA_BIGNUM_PATTERN.sub(bignum_content, chapter["content"])
            chapter["content"] = OTBN_ISA_BASE_ENCODING_PATTERN.sub(base_enc_content,
                                                                    chapter["content"])
            chapter["content"] = OTBN_ISA_BIGNUM_ENCODING_PATTERN.sub(bignum_enc_content,
                                                                      chapter["content"])

            # Remember the path to this chapter to generate the instruction links
            isa_book_path = chapter["source_path"]
            break

    # Abort if we cannot resolve the instruction links
    if isa_book_path is None:
        sys.exit("No file was found with {{#otbn-isa base}}, {{#otbn-isa bignum}}, "
                 "{{#otbn-isa base_encoding}} and {{#otbn-isa bignum_encoding}}")

    def ref_to_link(m: re.Match):
        instr = m.group(1)
        ref = instr.replace(".", "").lower()
        return '<a href="/book/{}#{}"><code>{}</code></a>'.format(isa_book_path, ref, instr)

    # Resolve any links to an instruction in all chapters.
    for chapter in md_utils.chapters(book["sections"]):
        chapter["content"] = \
            OTBN_INSNREF_PATTERN.sub(
                ref_to_link,
                chapter["content"],
        )

    # dump the book into stdout
    print(json.dumps(book))


def get_listings() -> (str, str):
    """Use the otbn utility scripts to generate the ISA listings."""
    with tempfile.TemporaryDirectory() as tmpdir:
        subprocess.run(
            [str(OTBN_SCRIPT), str(OTBN_CFG), str(OTBN_IMPL), tmpdir],
            check=True,
        )
        tmpdir = Path(tmpdir)
        with open(tmpdir / "base.md") as f:
            base_content = f.read()

        with open(tmpdir / "bignum.md") as f:
            bignum_content = f.read()

        with open(tmpdir / "base_encoding.md") as f:
            base_enc_content = f.read()

        with open(tmpdir / "bignum_encoding.md") as f:
            bignum_enc_content = f.read()

    return (base_content, bignum_content, base_enc_content, bignum_enc_content)


if __name__ == "__main__":
    main()
