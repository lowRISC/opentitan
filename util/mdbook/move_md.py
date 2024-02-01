#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
'''Copies a markdown file, recalculating the relative links for the new location

KNOWN_ISSUES
- If you move a file to the same dir an existing relative link points to, the path
  won't be canonicalized (you will get '../<dir>' rather than '.')
- Doesn't check if link to anchor is correct, just check that file exists
- Would be nice to re-render the markdown straight from the AST, but I found other
  formatting changes when trying this.
'''

import validators
from markdown_it import MarkdownIt
from markdown_it.tree import SyntaxTreeNode

import argparse
import pathlib
from pathlib import Path
from typing import Tuple, Optional

import logging
logging.basicConfig()
logging.getLogger().setLevel(logging.DEBUG)  # set root-logger to most-permissive
logger = logging.getLogger(__name__)

logging.getLogger('markdown_it').setLevel(logging.WARNING)


# https://stackoverflow.com/a/71874881
def relative(target: Path, origin: Path) -> Path:
    """Return the path of target relative to origin.
    i.e. --> pathlib equivalent of os.path.relpath'
    """
    try:
        return Path(target).resolve().relative_to(Path(origin).resolve())
    except ValueError:  # target does not start with origin
        # recursion with origin (eventually origin is root so try will succeed)
        return Path('..').joinpath(relative(target, Path(origin).parent))


def split_on_frag(link: str) -> Tuple[Optional[str], Optional[str]]:
    # Strip fragment/anchor if present
    l_path, l_frag = None, None
    if "#" in link:
        l_path, l_frag = link.split("#")
    else:
        l_path, l_frag = link, None
    return (l_path, l_frag)


def should_update(link: str) -> bool:
    """Do some checking to decide if we should update the link.

    Return 'False' if we don't need to recalculate it.
    """

    # Don't update link if it is a URL
    if validators.url(link):
        logger.debug(f"IsUrl : {link}")
        return False

    path, _ = split_on_frag(link)
    if not path:
        # Must be a local anchor in the same file
        # We don't need to update this one.
        return False

    return True


def move_md(old_path: pathlib.Path, new_path: pathlib.Path) -> None:
    '''Main link rewriter'''
    if new_path.suffix != '.md':
        raise NameError(f"new_path does not end in .md : {new_path}")
    if old_path.suffix != '.md':
        raise NameError(f"old_path does not end in .md : {old_path}")
    if not old_path.exists():
        raise FileNotFoundError(f"old_path does not exist! : {old_path}")

    rel = relative(old_path.parent, new_path.parent)
    logger.info(f"OLD path : {old_path}")
    logger.info(f"NEW path : {new_path}")
    logger.info(f"relative path to recalculate links from NEW to OLD : {rel}")

    old_markdown = old_path.read_text()
    new_md = old_markdown  # Copy old file, then modify file in-memory

    # Extract all links from the old markdown file
    ast = SyntaxTreeNode(MarkdownIt().parse(old_markdown))
    links = []  # Ensure list is in-order
    for t in ast.walk():
        if getattr(t, 'type') in ('link'):
            links.append(str(t.attrs['href']))
        if getattr(t, 'type') in ('image'):
            links.append(str(t.attrs['src']))

    # Create new markdown with all relative links recalculated
    idx = 0
    for link in links:
        if not should_update(link):
            continue

        # Assuming the link is relative, check that it was valid to begin with.
        path, _ = split_on_frag(link)
        link_target = (old_path.parent / Path(path or "")).resolve()
        if not link_target.exists():
            logger.warning("Link in old_path points to non-existent file.")
            logger.warning(f"  OLD_PATH       : {old_path}")
            logger.warning(f"  REL_LINK       : {link}")
            logger.warning(f"  TARGET   (BAD) : {link_target}")
            continue

        # Update the old markdown with the new link
        link_new = str(rel / link)  # Join the common relative part with the old link
        idx = new_md.find(link, idx)
        logger.debug("|" + 88 * "-" + "|")
        logger.debug(f"| idx = {idx} | match = {new_md[idx:idx + len(link)]} |")
        logger.debug(f"| OLD : {link:>80} |")
        logger.debug(f"| NEW : {link_new:>80} |")
        logger.debug("|" + 88 * "-" + "|")
        new_md = new_md[:idx] + link_new + new_md[idx + len(link):]
        idx += len(link_new)

    new_path.parent.mkdir(parents=True, exist_ok=True)
    new_path.write_text(new_md)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('-O', '--old-path', required=True)
    parser.add_argument('-N', '--new-path', required=True)
    parser.add_argument('--quiet', action='store_true', required=False)
    parser.add_argument('--verbose', action='store_true', required=False)
    args = parser.parse_args()

    logger.setLevel(logging.INFO)
    if args.quiet:
        logger.setLevel(logging.WARNING)
    if args.verbose:
        logger.setLevel(logging.DEBUG)

    # Sanitize args, and call the core function
    move_md(old_path=pathlib.Path(args.old_path).resolve(),
            new_path=pathlib.Path(args.new_path).resolve())


if __name__ == "__main__":
    main()
