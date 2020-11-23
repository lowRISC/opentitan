#!/usr/bin/env python3
#
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import fnmatch
import logging
import re
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


class CommentStyle:
    '''Base class for comment style objects'''
    def __init__(self, first_line_prefix, comment_prefix):
        self.first_line_prefix = first_line_prefix
        self.comment_prefix = comment_prefix

    def search_line_pattern(self, licence_first_word):
        return re.compile(
            re.escape(self.comment_prefix + ' ' + licence_first_word))

    def full_line_parts(self, licence_line):
        return [re.escape(self.comment_prefix), licence_line]

    def full_line_pattern(self, licence_line):
        '''Returns a regex pattern which matches one line of licence text.'''
        return re.compile(' '.join(self.full_line_parts(licence_line)))


class LineCommentStyle(CommentStyle):
    """Helpers for line-style comments."""
    def __init__(self, prefix):
        super().__init__(prefix, prefix)


class DifferentFirstLineCommentStyle(CommentStyle):
    """Some files have a different allowable prefix for their first line."""
    def __init__(self, first_line_prefix, prefix):
        super().__init__(first_line_prefix, prefix)


class BlockCommentStyle(CommentStyle):
    """Helpers for block-style comments."""
    def __init__(self, prefix, suffix):
        super().__init__(prefix, prefix)
        self.comment_suffix = str(suffix)

    def full_line_parts(self, licence_line):
        return [
            re.escape(self.comment_prefix), licence_line,
            re.escape(self.comment_suffix)
        ]


SLASH_SLASH = '//'
HASH = '#'
SLASH_STAR = '/*'

COMMENT_STYLES = {
    SLASH_SLASH: LineCommentStyle("//"),
    HASH: LineCommentStyle("#"),
    SLASH_STAR: BlockCommentStyle("/*", "*/"),
    'corefile': DifferentFirstLineCommentStyle("CAPI=2", "#")
}

# (Prioritised) Mapping of file name suffixes to comment style. If the suffix
# of your file does not match one of these, it will not be checked.
#
# Each entry is a pair (suffixes, styles). suffixes is a list of file suffixes:
# if a filename matches one of these suffixes, we'll use the styles in styles.
# styles is either a string or a list of strings. If there is one or more
# strings, these strings must all be keys of COMMENT_STYLES and they give the
# different comment styles that are acceptable for the file type.
#
# These rules are given in priority order. Tuples higher in the list are
# matched before those later in the list, on purpose.
#
# Files that either do not match any extension or that have an empty list of
# styles are not checked for a licence.
COMMENT_CHARS = [
    # Hardware Files
    ([".svh", ".sv", ".sv.tpl"], SLASH_SLASH),  # SystemVerilog

    # Hardware Build Systems
    ([".tcl", ".sdc"], HASH),  # tcl
    ([".core", ".core.tpl"], 'corefile'),  # FuseSoC Core Files
    (["Makefile", ".mk"], HASH),  # Makefiles
    ([".ys"], HASH),  # Yosys script
    ([".waiver"], HASH),  # AscentLint waiver files
    ([".vlt"], SLASH_SLASH),  # Verilator configuration (waiver) files
    ([".vbl"], HASH),  # Verible configuration files
    ([".el", ".el.tpl"], SLASH_SLASH),  # Exclusion list
    ([".cfg", ".cfg.tpl"], [SLASH_SLASH,
                            HASH]),  # Kinds of configuration files
    ([".f"], []),  # File lists (not checked)

    # The following two rules will inevitably bite us.
    (["riviera_run.do"], HASH),  # Riviera dofile
    ([".do"], SLASH_SLASH),  # Cadence LEC dofile

    # Software Files
    ([".c", ".c.tpl", ".h", ".h.tpl", ".cc", ".cpp"], SLASH_SLASH),  # C, C++
    ([".def"], SLASH_SLASH),  # C, C++ X-Include List Declaration Files
    ([".S"], [SLASH_SLASH, SLASH_STAR]),  # Assembly (With Preprocessing)
    ([".s"], SLASH_STAR),  # Assembly (Without Preprocessing)
    ([".ld", ".ld.tpl"], SLASH_STAR),  # Linker Scripts
    ([".rs", ".rs.tpl"], SLASH_SLASH),  # Rust

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
    ([".md", ".md.tpl", ".html"], []),  # Markdown and HTML (not checked)
    ([".css"], SLASH_STAR),  # CSS
    ([".scss"], SLASH_SLASH),  # SCSS

    # Templates (Last because there are overlaps with extensions above)
    ([".tpl"], HASH),  # Mako templates
]


class LicenceMatcher:
    '''An object to match a given licence at the start of a file'''
    def __init__(self, comment_style, licence, match_regex):
        self.style = comment_style
        self.expected_lines = list()
        # In case we are using regex matching we can pass the full line "as is"
        if match_regex:
            for i, ll in enumerate(licence):
                try:
                    self.expected_lines.append(
                        comment_style.full_line_pattern(ll))
                    # Catch any regex error here and raise a runtime error.
                except re.error as e:
                    raise RuntimeError(
                        "Can't compile line {} of the licence as a regular expression. Saw `{}`: {}"
                        .format(i, e.pattern[e.pos], e.msg))
            # use the "first line" as a licence marker
            self.search_marker = self.expected_lines[0]
        # For non-regex matching we need to escape everything.
        # This can never throw an exception as everything has been escaped and
        # therefore is always a legal regex.
        else:
            self.search_marker = comment_style.search_line_pattern(
                licence.first_word)
            self.expected_lines = [
                comment_style.full_line_pattern(re.escape(ll))
                for ll in licence
            ]

        self.lines_left = []

    def looks_like_first_line_comment(self, line):
        return line.startswith(self.style.first_line_prefix)

    def looks_like_comment(self, line):
        return line.startswith(self.style.comment_prefix)

    def looks_like_first_line(self, line):
        return self.search_marker.match(line) is not None

    def start(self):
        '''Reset lines_left, to match at the start of the licence'''
        self.lines_left = self.expected_lines

    def take_line(self, line):
        '''Check whether line matches the next line of the licence.

        Returns a pair (matched, done). matched is true if the line matched. If
        this was the last line of the licence, done is true. On a match, this
        increments an internal counter, so the next call to take_line will
        match against the next line of the licence.

        '''
        # If we have no more lines to match, claim a match and that we're done.
        # This shouldn't happen in practice, except if the configuration has an
        # empty licence.
        if not self.lines_left:
            return (True, True)

        next_expected = self.lines_left[0]
        matched = next_expected.fullmatch(line)

        if not matched:
            return (False, False)

        if matched:
            self.lines_left = self.lines_left[1:]
            return (True, not self.lines_left)


def detect_comment_char(all_matchers, filename):
    '''Find zero or more LicenceMatcher objects for filename

    all_matchers should be a dict like COMMENT_STYLES, but where the values are
    the corresponding LicenceMatcher objects.

    '''
    found = None
    for (suffixes, keys) in COMMENT_CHARS:
        if found is not None:
            break
        for suffix in suffixes:
            if filename.endswith(suffix):
                found = keys
                break

    if found is None:
        return []

    if not isinstance(found, list):
        assert isinstance(found, str)
        found = [found]

    return [all_matchers[key] for key in found]


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
        return (self.passed_count + self.failed_count + self.skipped_count +
                self.excluded_count)

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
    try:
        all_matchers = {
            key: LicenceMatcher(style, config.licence, config.match_regex)
            for key, style in COMMENT_STYLES.items()
        }
    except RuntimeError as e:
        exit(e)

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

        check_file_for_licence(all_matchers, results, filepath)

    return results


def check_file_for_licence(all_matchers, results, filepath):
    matchers = detect_comment_char(all_matchers, filepath.name)

    if not matchers:
        results.skipped(filepath, "Unknown comment style")
        return

    if filepath.stat().st_size == 0:
        results.skipped(filepath, "Empty file")
        return

    problems = []
    for matcher in matchers:
        good, line_num, msg = check_file_with_matcher(matcher, filepath)
        if good:
            results.passed(filepath, line_num, msg)
            return
        else:
            problems.append((line_num, msg))

    # If we get here, we didn't find a matching licence
    for line_num, msg in problems:
        results.failed(filepath, line_num, msg)


def check_file_with_matcher(matcher, filepath):
    '''Check the file at filepath against matcher.

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

        # Check first line against the first word of licence, or against a
        # possible different first line.
        if not matcher.looks_like_first_line(line):
            if not matcher.looks_like_first_line_comment(line):
                return (False, line_no, "File does not start with comment")

            try:
                line, line_no = next_line(f, line_no)
            except StopIteration:
                return (False, line_no,
                        "Reached end of file before finding licence")

        # Skip lines that don't seem to be the first line of the licence
        while not matcher.looks_like_first_line(line):
            try:
                line, line_no = next_line(f, line_no)
            except StopIteration:
                return (False, line_no,
                        "Reached end of file before finding licence")

            if not matcher.looks_like_comment(line):
                return (False, line_no,
                        "First comment ended before licence notice")

        # We found the marker, so we found the first line of the licence. The
        # current line is in the first comment, so check the line matches the
        # expected first line:
        licence_assumed_start = line_no
        matcher.start()
        matched, done = matcher.take_line(line)
        if not matched:
            return (False, line_no, "Licence does not match")

        while not done:
            try:
                line, line_no = next_line(f, line_no)
            except StopIteration:
                return (False, line_no,
                        "Reached end of file before finding licence")

            # Check against full expected line.
            matched, done = matcher.take_line(line)
            if not matched:
                return (False, line_no, "Licence did not match")

    return (True, licence_assumed_start, "Licence found")


def main():
    desc = "A tool to check the lowRISC licence header is in each source file"
    parser = argparse.ArgumentParser(description=desc)
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
    # Check whether we should use regex matching or full string matching.
    match_regex = parsed_config.get('match_regex', 'false')
    if match_regex not in ['true', 'false']:
        print('Invalid value for match_regex: {!r}. '
              'Should be "true" or "false".'.format(match_regex))
        exit(1)
    config.match_regex = match_regex == 'true'

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
