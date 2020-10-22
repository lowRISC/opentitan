#!/usr/bin/env python3
#
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import fnmatch
import logging
import subprocess
from pathlib import Path
from types import SimpleNamespace

import hjson
from tabulate import tabulate


class LicenceHeader(object):
    """Represents the licence header we want to insert"""
    def __init__(self, text):
        self._lines = text.strip().splitlines()

    def __getitem__(self, idx):
        return self._lines.__getitem__(idx)

    def __len__(self):
        return self._lines.__len__()

    def numbered_lines(self, skip=0):
        """Returns an iterator of (line_no, line_text).

        `line_no` counts from 1, and is for humans to count line numbers with.
        use `skip_lines` to skip enumerating the first few lines.
        """
        return enumerate(self._lines[skip:], start=1 + skip)

    @property
    def first_word(self):
        (first_word, _) = self._lines[0].split(' ', 1)
        return first_word


class LineCommentStyle(object):
    """Helpers for line-style comments."""
    def __init__(self, prefix):
        self.comment_prefix = str(prefix)
        self.first_line_prefix = self.comment_prefix

    def search_line(self, licence_first_word):
        return self.comment_prefix + ' ' + licence_first_word

    def expected_full_line(self, licence_line):
        return self.comment_prefix + ' ' + licence_line


class DifferentFirstLineCommentStyle(LineCommentStyle):
    """Some files have a different allowable prefix for their first line."""
    def __init__(self, prefix, first_line_prefix):
        LineCommentStyle.__init__(self, prefix)
        self.first_line_prefix = first_line_prefix


class BlockCommentStyle(object):
    """Helpers for block-style comments."""
    def __init__(self, prefix, suffix):
        self.comment_prefix = str(prefix)
        self.comment_suffix = str(suffix)
        self.first_line_prefix = self.comment_prefix

    def search_line(self, licence_first_word):
        return self.comment_prefix + ' ' + licence_first_word

    def expected_full_line(self, licence_line):
        return self.comment_prefix + ' ' + licence_line + ' ' + self.comment_suffix


SLASH_SLASH = LineCommentStyle("//")
HASH = LineCommentStyle("#")
SLASH_STAR = BlockCommentStyle("/*", "*/")

# (Priortised) Mapping of file name suffixes to comment style. If the suffix of
# your file does not match one of these, it will not be checked.
#
# The value in a pair should be one of:
#
#    None:                            Skip this file type
#    A CommentStyle object:           Use this comment style
#    A list of CommentStyle objects:  Try each comment style in turn
#
# These rules are given in priority order. Tuples of (extensions, style) higher
# in the list are matched before those later in the list, on purpose.
#
# Files that do not match any extension, or which have a style of `None` are
# not checked for a licence.
COMMENT_CHARS = [
    # Hardware Files
    ([".svh", ".sv", ".sv.tpl"], SLASH_SLASH),  # SystemVerilog

    # Hardware Build Systems
    ([".tcl", ".sdc"], HASH),  # tcl
    ([".core", ".core.tpl"],
     DifferentFirstLineCommentStyle("#", "CAPI=2")),  # FuseSoC Core Files
    (["Makefile", ".mk"], HASH),  # Makefiles
    ([".ys"], HASH),  # Yosys script
    ([".waiver"], HASH),  # AscentLint waiver files
    ([".vlt"], SLASH_SLASH),  # Verilator configuration (waiver) files
    ([".vbl"], HASH),  # Verible configuration files
    ([".el", ".el.tpl"], SLASH_SLASH),  # Exclusion list
    ([".f"], None),  # File lists

    # The following two rules will inevitably bite us.
    (["riviera_run.do"], HASH),  # Riviera dofile
    ([".do"], SLASH_SLASH),  # Cadence LEC dofile

    # Software Files
    ([".c", ".c.tpl", ".h", ".h.tpl", ".cc", ".cpp"], SLASH_SLASH),  # C, C++
    ([".def"], SLASH_SLASH),  # C, C++ X-Include List Declaration Files
    ([".S"], [SLASH_SLASH, SLASH_STAR]),  # Assembly (With Preprocessing)
    ([".s"], SLASH_STAR),  # Assembly (Without Preprocessing)
    ([".ld", ".ld.tpl"], SLASH_STAR),  # Linker Scripts
    ([".rs"], SLASH_SLASH),  # Rust

    # Software Build Systems
    (["meson.build", "toolchain.txt", "meson_options.txt"], HASH),  # Meson

    # General Tooling
    ([".py"], HASH),  # Python
    ([".sh"], HASH),  # Shell Scripts
    (["Dockerfile"], HASH),  # Dockerfiles

    # Configuration
    ([".hjson", ".hjson.tpl"], SLASH_SLASH),  # hjson
    ([".yml", ".yaml"], HASH),  # YAML
    ([".toml"], HASH),  # TOML
    (["-requirements.txt"], HASH),  # Apt and Python requirements files
    (["redirector.conf"], HASH),  # nginx config

    # Documentation
    ([".md", ".md.tpl", ".html"], None),  # Markdown and HTML
    ([".css"], SLASH_STAR),  # CSS
    ([".scss"], SLASH_SLASH),  # SCSS

    # Templates (Last because there are overlaps with extensions above)
    ([".tpl"], HASH),  # Mako templates
]


def detect_comment_char(filename):
    for (suffixes, commentstyle) in COMMENT_CHARS:
        for suffix in suffixes:
            if filename.endswith(suffix):
                return commentstyle

    return None


def git_find_repo_toplevel():
    git_output = subprocess.check_output(
        ['git', 'rev-parse', '--show-toplevel'])
    return Path(git_output.decode().strip()).resolve()


def git_find_all_file_paths(top_level, search_paths):
    git_output = subprocess.check_output(
        ["git", "-C",
         str(top_level), "ls-files", "-z", "--", *search_paths])
    for path in git_output.rstrip(b"\0").split(b"\0"):
        yield Path(top_level, path.decode())


class ResultsTracker(object):
    """Helper for tracking results"""
    def __init__(self, base_dir):
        self.base_dir = base_dir

    passed_count = 0
    failed_count = 0
    excluded_count = 0
    skipped_count = 0

    failing_paths = set()

    @property
    def total_count(self):
        return self.passed_count + self.failed_count + self.skipped_count + self.excluded_count

    def passed(self, path, line_no, reason):
        rel_path = path.relative_to(self.base_dir)
        logging.debug("%s:%d PASSED: %s", str(rel_path), line_no, reason)
        self.passed_count += 1

    def failed(self, path, line_no, reason):
        rel_path = path.relative_to(self.base_dir)
        logging.error("%s:%d FAILED: %s", str(rel_path), line_no, reason)
        self.failing_paths.add(rel_path)
        self.failed_count += 1

    def skipped(self, path, reason):
        rel_path = path.relative_to(self.base_dir)
        logging.info("%s: SKIPPED: %s", str(rel_path), reason)
        self.skipped_count += 1

    def excluded(self, path, reason):
        rel_path = path.relative_to(self.base_dir)
        logging.debug("%s: EXCLUDED: %s", str(rel_path), reason)
        self.excluded_count += 1

    def any_failed(self):
        return self.failed_count > 0

    def display_nicely(self):
        headers = ["Results:", "Files"]
        results = [["Passed", self.passed_count],
                   ["Failed", self.failed_count],
                   ["Skipped", self.skipped_count],
                   ["Excluded", self.excluded_count],
                   ["Total", self.total_count]]

        return tabulate(results, headers, tablefmt="simple")


def matches_exclude_pattern(config, file_path):
    rel_path = str(file_path.relative_to(config.base_dir))
    for exclude_pattern in config.exclude_paths:
        if fnmatch.fnmatch(rel_path, exclude_pattern):
            return True
    return False


def check_paths(config, git_paths):
    results = ResultsTracker(config.base_dir)

    for filepath in git_find_all_file_paths(config.base_dir, git_paths):
        # Skip symlinks (with message)
        if filepath.is_symlink():
            results.excluded(filepath, "File is a symlink")
            continue

        # Skip non-file
        if not filepath.is_file():
            continue

        # Skip exclude patterns
        if matches_exclude_pattern(config, filepath):
            results.excluded(filepath, "Path matches exclude pattern")
            continue

        check_file_for_licence(config.licence, results, filepath)

    return results


def check_file_for_licence(licence, results, filepath):
    styles = detect_comment_char(filepath.name)

    if styles is None:
        results.skipped(filepath, "Unknown comment style")
        return

    if filepath.stat().st_size == 0:
        results.skipped(filepath, "Empty file")
        return

    if not isinstance(styles, list):
        assert (isinstance(styles, LineCommentStyle) or
                isinstance(styles, BlockCommentStyle))
        styles = [styles]

    problems = []
    for style in styles:
        good, line_num, msg = check_file_with_style(licence, filepath, style)
        if good:
            results.passed(filepath, line_num, msg)
            return
        else:
            problems.append((line_num, msg))

    # If we get here, we didn't find a matching licence
    for line_num, msg in problems:
        results.failed(filepath, line_num, msg)


def check_file_with_style(licence, filepath, comment_style):
    '''Check the file at filepath, assuming it uses comment_style.

    Returns a tuple (is_good, line_number, msg). is_good is True on success;
    False on failure. line_number is the position where the licence was found
    (on success) or where we gave up searching for it (on failure). msg is the
    associated success or error message.

    '''
    def next_line(file, line_no):
        return (next(file).rstrip(), line_no + 1)

    with filepath.open() as f:
        licence_assumed_start = None

        # Get first line
        try:
            line, line_no = next_line(f, 0)
        except StopIteration:
            return (False, 1, "Empty file")

        licence_search_marker = comment_style.search_line(licence.first_word)

        # Check first line against the first word of licence, or against a
        # possible different first line.
        if not line.startswith(licence_search_marker):
            if not line.startswith(comment_style.first_line_prefix):
                return (False, line_no, "File does not start with comment")

            try:
                line, line_no = next_line(f, line_no)
            except StopIteration:
                return (False, line_no,
                        "Reached end of file before finding licence")

        # Skip lines that don't seem to be the first line of the licence
        while not line.startswith(licence_search_marker):
            try:
                line, line_no = next_line(f, line_no)
            except StopIteration:
                return (False, line_no,
                        "Reached end of file before finding licence")

            if not line.startswith(comment_style.comment_prefix):
                return (False, line_no,
                        "First comment ended before licence notice")

        # We found the marker, so we found the first line of the licence. The
        # current line is in the first comment, so check the line matches the
        # expected first line:
        licence_assumed_start = line_no
        if line != comment_style.expected_full_line(licence[0]):
            return (False, line_no, "Licence does not match")

        for (licence_line_no, licence_line) in licence.numbered_lines(skip=1):
            try:
                line, line_no = next_line(f, line_no)
            except StopIteration:
                return (False, line_no,
                        "Reached end of file before finding licence")

            # Check against full expected line.
            if line != comment_style.expected_full_line(licence_line):
                return (False, line_no, "Licence did not match")

    return (True, licence_assumed_start, "Licence found")


def main():
    parser = argparse.ArgumentParser(
        description=
        "A tool to check the lowRISC licence header is in each source file")
    parser.add_argument("--config",
                        metavar="config.hjson",
                        type=argparse.FileType('r', encoding='UTF-8'),
                        required=True,
                        help="HJSON file to read for licence configuration.")
    parser.add_argument("paths",
                        metavar="path",
                        nargs='*',
                        default=["."],
                        help="Paths to check for licence headers.")
    parser.add_argument('-v',
                        "--verbose",
                        action='store_true',
                        dest='verbose',
                        help="Verbose output")

    options = parser.parse_args()

    if options.verbose:
        logging.basicConfig(format="%(levelname)s: %(message)s",
                            level=logging.INFO)
    else:
        logging.basicConfig(format="%(levelname)s: %(message)s")

    config = SimpleNamespace()
    config.base_dir = git_find_repo_toplevel()

    parsed_config = hjson.load(options.config)

    config.licence = LicenceHeader(parsed_config['licence'])
    config.exclude_paths = set(parsed_config['exclude_paths'])

    results = check_paths(config, options.paths)

    print(results.display_nicely())

    if results.any_failed():
        print("Failed:")
        for path in results.failing_paths:
            print("  {}".format(str(path)))
        print("")
        exit(1)
    else:
        exit(0)


if __name__ == '__main__':
    main()
