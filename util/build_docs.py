#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# pip3 install --user livereload
# Usage:
#   run './build_docs.py' to generate the documentation and keep it updated
#   open 'http://localhost:5500/' to check live update (this opens the top
#   level index page). you can also directly access a specific document by
#   accessing 'http://localhost:5500/path/to/doc.html',
#       e.g. http://localhost:5500/hw/ip/uart/doc/uart.html

import argparse
import logging
import os
import shutil
from pathlib import Path

import livereload

import docgen.generate

USAGE = """
  build_docs [options]
"""

MARKDOWN_EXTENSIONS = [
    '.md',
    '.mkd',
]
STATIC_ASSET_EXTENSIONS = [
    '.svg',
    '.png',
    '.jpg',
    '.css',
]
HJSON_EXTENSIONS = ['.hjson']

# Configurations
# TODO: Move to config.yaml
SRCTREE_TOP = Path(__file__).parent.joinpath('..').resolve()
config = {
    # Toplevel source directory
    "topdir": SRCTREE_TOP,

    # A list of directories containing documentation within topdir. To ensure
    # the top-level sitemap doesn't have broken links, this should be kept
    # in-sync with the doctree tag in sitemap.md.
    "incdirs": ['./doc', './hw', './sw', './util'],

    # Output directory for documents
    "outdir": SRCTREE_TOP.joinpath('opentitan-docs'),
    "verbose": False,
}


def get_doc_files(extensions=MARKDOWN_EXTENSIONS + STATIC_ASSET_EXTENSIONS):
    """Get the absolute path of files containing documentation
    """
    file_list = []
    # doc files on toplevel
    for ext in extensions:
        file_list += config["topdir"].glob('*' + ext)
    # doc files in include dirs
    for incdir in config['incdirs']:
        for ext in extensions:
            file_list += config["topdir"].joinpath(incdir).rglob('*' + ext)
    return file_list


def ensure_dest_dir(dest_pathname):
    os.makedirs(dest_pathname.parent, exist_ok=True)


def path_src_to_dest(src_pathname, dest_filename_suffix=None):
    """Get the destination pathname from a source pathname
    """
    src_relpath = Path(src_pathname).relative_to(config["topdir"])
    dest_pathname = Path(config["outdir"]).joinpath(src_relpath)
    if dest_filename_suffix:
        dest_pathname = dest_pathname.with_suffix(dest_filename_suffix)
    return dest_pathname


def process_file_markdown(src_pathname):
    """Process a markdown file and copy it to the destination
    """
    dest_pathname = path_src_to_dest(src_pathname, '.html')

    logging.info("Processing Markdown file: %s -> %s" %
                 (str(src_pathname), str(dest_pathname)))

    ensure_dest_dir(dest_pathname)

    with open(dest_pathname, 'w', encoding='UTF-8') as f:
        outstr = docgen.generate.generate_doc(str(src_pathname),
                                              verbose=config['verbose'],
                                              inlinecss=True,
                                              inlinewave=True,
                                              asdiv=False)
        f.write(outstr)

    return dest_pathname


def process_file_copytodest(src_pathname):
    """Copy a file to the destination directory with no further processing
    """
    dest_pathname = path_src_to_dest(src_pathname)

    logging.info("Copying %s -> %s" % (str(src_pathname), str(dest_pathname)))

    ensure_dest_dir(dest_pathname)
    shutil.copy(src_pathname, dest_pathname)


def process_all_files():
    """Process all files

    The specific processing action depends on the file type.
    """
    src_files = get_doc_files()

    for src_pathname in src_files:
        if src_pathname.suffix in MARKDOWN_EXTENSIONS:
            process_file_markdown(src_pathname)
        elif src_pathname.suffix in STATIC_ASSET_EXTENSIONS:
            process_file_copytodest(src_pathname)


def main():
    logging.basicConfig(level=logging.INFO,
                        format="%(asctime)s - %(message)s",
                        datefmt="%Y-%m-%d %H:%M")

    parser = argparse.ArgumentParser(
        prog="build_docs",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        usage=USAGE)
    parser.add_argument(
        '--preview',
        action='store_true',
        help="""starts a local server with live reload (updates triggered upon
             changes in the documentation files). this feature is intended
             to preview the documentation locally.""")

    args = parser.parse_args()

    # Initial processing of all files
    process_all_files()

    if args.preview:
        # Setup livereload watcher
        server = livereload.Server()
        exts_to_watch = MARKDOWN_EXTENSIONS +       \
                        STATIC_ASSET_EXTENSIONS +   \
                        HJSON_EXTENSIONS
        for src_pathname in get_doc_files(exts_to_watch):
            server.watch(str(src_pathname), process_all_files)
        server.serve(root=config['topdir'].joinpath(config['outdir']))


if __name__ == "__main__":
    main()
