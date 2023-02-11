#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from pathlib import Path
import tomli
import re
import argparse


parser = argparse.ArgumentParser()
parser.add_argument("--debug",
                    help = "print debugging information (very verbose)",
                    action="store_true")
parser.add_argument("--debug-only-file",
                    help = "only process a particular file (helpful to debug)",)
parser.add_argument("--debug-only-line",
                    help = "only process a particular file (helpful to debug)",)
parser.add_argument("--apply-suggestions",
                    help = "apply all the fixes suggested by the tools",
                    action="store_true")
parser.add_argument("--pedantic-reldir",
                    help = "be especially pedantic about relative path using ./",
                    action="store_true")
parser.add_argument("root_doc",
                    help = "path to the root of documentation")
parser.add_argument("--warn-internal-weblinks",
                    help = "warn about links to internal documentation using docs.opentitan.org URLs",
                    action=argparse.BooleanOptionalAction,
                    default = True)
parser.add_argument("--warn-unlisted-files",
                    help = "warn about md files that are not listed in SUMMARY.md",
                    action=argparse.BooleanOptionalAction,
                    default = True)
parser.add_argument("--warn-hugo-links",
                    help = "warn about links using the old Hugo format",
                    action=argparse.BooleanOptionalAction,
                    default = True)
parser.add_argument("--move-list-file",
                    help = "provide a list of moved files to help fix the links")
parser.add_argument("--ignore-book",
                    help = "do not search for mdbook and just check all markdown files in a directory",
                    action="store_true")
g_args = parser.parse_args()


def debug(msg):
    if g_args.debug:
        print("[debug] " + msg)


def parse_move_list_file(path):
    if not path.exists() or not path.is_file():
        print(f"error: move file list {path} does not exist or is not a file")
        return None
    with path.open() as f:
        res = {}
        line_nr = 0
        for line in f:
            line_nr += 1
            if line.strip() == "":
                continue
            # ignore empty lines and split at whitespace
            arr = line.strip().split()
            if len(arr) != 2:
                print("move file list f{path}: f{line_nr} has the wrong format and will be ignored")
                continue
            res[arr[0]] = arr[1]
        return res


g_move_list_file = None
if g_args.move_list_file:
    g_move_list_file = parse_move_list_file(Path(g_args.move_list_file))


class Book:
    """
    Represents an mdbook
    """

    def __init__(self, path):
        """
        Load a book by pointing to the directory containing a book.toml
        This is will build the list of files listed in SUMMARY.md
        and also build the list of all md files under this directory
        """
        self.path = path.resolve()
        self.mdbook_defaults = ["README.md", "index.md"]
        self.site_url = "NO_URL"
        global g_args
        if g_args.ignore_book:
            # create a fake book
            self.srcdir = path
        else:
            self._load_book(path)
        # build list of all files that appear in the subdirectory
        # for each file we will eventually set to True if they are listed in summary
        self.allmdfiles = {}

        def addfile(f):
            name = self.local_name(f)
            self.allmdfiles[name] = False
        self.apply_to_all_files(addfile)
        # load summary
        if not g_args.ignore_book:
            self._load_summary()

    def _load_book(self, path):
        toml = self.path / "book.toml"
        assert toml.exists(), "there is not book.toml"
        toml_dict = tomli.loads(toml.read_bytes().decode("utf-8"))
        self.srcdir = (path / toml_dict["book"]["src"]).resolve()
        if "output" in toml_dict and "html" in toml_dict["output"]:
            self.site_url = toml_dict["output"]["html"].get("site-url", self.site_url)

    def _load_summary(self):
        # load summary and mark all links as true, ignore all errors for now
        for (line, _, link) in Book.list_links_in_file(self.srcdir / "SUMMARY.md"):
            name = self.local_name(self.srcdir / link)
            # we only check .md files, SUMMARY.md can include more types of files
            # with preprocessors
            if name.name.endswith(".md"):
                # if ever SUMMARY.md contains an invalid link, ignore it (it will reported by the general check)
                if name in self.allmdfiles:
                    # assert name in self.allmdfiles, f"book at {self.path}: link {link} in summary is invalid (normalized to {str(name)})"
                    self.allmdfiles[name] = True

    def __repr__(self):
        return f"Book({repr(self.path)})"

    def __str__(self):
        return f"book at {str(self.path)}, src at {str(self.srcdir)}, url at {str(self.site_url)}"

    def local_name(self, abspath):
        """
        Given an absolute Path to a file under the source directory of the book,
        return a relative Path to the source directory, return None in case of error
        """
        try:
            return abspath.resolve().relative_to(self.srcdir)
        except ValueError:
            return None

    def apply_to_all_files(self, fn):
        """
        List all files under the directory of the book and call a function on each one
        """
        def apply_rec(path):
            for child in path.iterdir():
                if child.name.endswith(".md"):
                    fn(child)
                if child.is_dir():
                    apply_rec(child.resolve())
        apply_rec(self.path)

    def list_links_in_file(abspath):
        """
        Return a list of all the links in a file (given by its absolute Path)
        Each entry is a tuple of the form (line_nr, (start, end), link)
        indicating the line number, the character range within the line and the link itself
        """
        cm_re = r"\[[^\]]*\]\(\s*(?P<url>[^)]*)\s*\)"
        # we also look for non-markdown-but-Hugo-relref
        hugo_relref_re = r"(?P<hugo>\{\{<\s*relref\s*\"[^\"]*\"\s*>\}\})"
        prog = re.compile(f"{cm_re}|{hugo_relref_re}")
        links = []
        with abspath.open() as f:
            line_nr = 0
            for line in f:
                line_nr += 1
                for x in prog.finditer(line):
                    grp = "url" if x.group("url") is not None else "hugo"
                    posrange = (x.start(grp), x.end(grp))
                    links.append((line_nr, posrange, x[grp]))
        return links

    def is_file_in_summary(self, path):
        """
        Check whether a file (given by its absolute Path) is in the SUMMARY.md file of the book
        """
        # if the file does not exists, it cannot be in summary
        if not path.exists() or not path.is_file():
            return False
        local_name = self.local_name(path)
        # if it points to an md file, it must be in the summary
        assert path.name.endswith(".md"), f"this function only works for md files, called on {path}"
        assert local_name in self.allmdfiles, f"link to \"{path}\" normalised to {local_name} not in list"
        return self.allmdfiles[local_name]

    def path_exists_or_was_moved(self, path, reverse_move=False):
        """
        This function takes a Path and returns a Path to the file, which could be potentially
        different if the file was moved. This function handles file moves as recorded in the
        move file list. It returns None if it cannot resolve it to an *existing* file or directory.
        """
        global g_move_list_file
        move_list_file = g_move_list_file
        if move_list_file is None:
            move_list_file = {}
        # reverse map if asked
        if reverse_move:
            res = {}
            for (from_, to) in move_list_file.items():
                res[to] = from_
            move_list_file = res
        # first check if it was moved because it could be that a file was moved
        # and later replaced by another file with different content: the move takes priority
        local_name = self.local_name(path)
        debug(f"CHECK MOVE {path}, normalized to {local_name}, exists {path.exists()}, reverse {reverse_move}, moved {str(local_name) in move_list_file}")
        if local_name is None:
            return None
        if str(local_name) in move_list_file:
            moved_to = move_list_file[str(local_name)]
            assert moved_to[0] != '/', "the target of a move cannot be an absolute path"
            newpath = self.srcdir / moved_to
            # we only check new path existence for non-reverse moved
            if reverse_move or newpath.exists():
                debug(f"move detected {path}, normalize to {local_name}, now {newpath}")
                return newpath
        if path.exists():
            return path
        return None

    def _resolve_existing_path(self, path, report):
        """
        Given a Path to an existing file/directory, figure out what is the intended markdown target.
        This handles for example a link to a directory that contains an README.md.
        This returns a Path to the intended markdown file, or None if none could be found.
        When retuning None, it will report the error using the report function.
        """
        # if it points to a directory, we try to resolve it to README.md or index.md
        if path.is_dir():
            for subfile in self.mdbook_defaults:
                if (path / subfile).exists():
                    return path / subfile
            report(
                f"link to directory \"{self.local_name(path)}\" but cannot find a valid subfile, tried {self.mdbook_defaults}")
            return None
        else:
            return path

    def resolve_relative_link(self, local_filename, link, relative_to, report):
        """
        Given a link (a string) in a file (represented by its relative Path to the source directory),
        try to find the Path to the intended markdown target and return it.
        If none can be found, returns None. Any error/warning will reporting via the report function.
        This function will handle things like pointing to directories, using index.html instead of README.md
        and other oddities.
        """
        # if the link starts with a '/', this will mess with pathlib because bla / link will just produce bla
        # but we want the link to relative to what was specified, so remove the initial '/' if needed
        while len(link) > 0 and link[0] == '/':
            link = link[1:]
        debug(f"resolving {link} relative to {local_filename}")
        # there are several cases:
        # - points to a file
        # - points to a directory
        path = (relative_to / link).resolve()
        if (newpath := self.path_exists_or_was_moved(path)) is not None:
            return self._resolve_existing_path(newpath, report)
        debug("direct resolution to a moved file has failed")
        # if the link ends with index.html, and the corresponding index.md or README.md file exists
        # then resolve it to that file
        index_html = "index.html"
        if link.endswith(index_html):
            for subfile in self.mdbook_defaults:
                new_link = link[:-len(index_html)] + subfile
                path = (relative_to / new_link).resolve()
                if (newpath := self.path_exists_or_was_moved(path)) is not None:
                    # FIXME should we check that this is in the summary?
                    report(
                        f"link to HTML file \"{link}\", resolved to \"{self.local_name(newpath)}\", which is a local file")
                    return path
        # no solution found
        report(
            f"link to \"{link}\", resolved to \"{self.local_name(path)}\", which does not exists")
        return None

    def resolve_local_link(self, local_filename, link, report):
        return self.resolve_relative_link(local_filename, link, (self.srcdir / local_filename).parent, report)

    def resolve_global_link(self, local_filename, link, report):
        return self.resolve_relative_link(local_filename, link, self.srcdir, report)


def find_all_books(path):
    """
    Return a list of Book constructed from the book.toml files that can be
    found under path (recursively).
    """
    books = []
    for child in path.iterdir():
        if child.is_dir():
            books.extend(find_all_books(child))
        if child.is_file() and child.name == "book.toml":
            books.append(Book(path))
    return books


def relative_link_to(relpath, relative_to_dir):
    """
    Given an absolute Path to a file (or directory) and an absolute Path to a directory,
    return a relative path to reach the file from the directory.
    For example relative_link_to(/path/to/some/very/deep/file/hello.md, /path/to/a/shallow/dir)
    returns ../../../some/very/deep/file/hello.md
    """
    parent = relative_to_dir.resolve()
    pref = "./"
    while True:
        try:
            out = relpath.relative_to(parent)
            return pref + str(out)
        except ValueError:
            parent = parent.parent
            if pref == "./":
                pref = "../"
            else:
                pref += "../"
    print(
        f"ERROR couldn't create link for {relpath} relative to {relative_to_dir.resolve()}, this should never happen")
    return None

# decide when to suggest a link rewriting
# the main to detect here is that some links are of theform x
# but the canonical link would be just "./x"
# at this stage we don't want to bother the use with such nonsense


def should_rewrite_link(newlink, oldlink):
    if oldlink == newlink:
        return False
    if newlink == "./" + oldlink and not g_args.pedantic_reldir:
        return False
    return True


def try_several_resolutions(book, local_filename, link, process_list, report):
    """
    This function tries to resolve a link is several different ways by
    calling the various functions in the processing list. To make the
    user output readable, it will not forward any of the report/suggestions
    unless the list has size 1 or the function suceeds. If no function suceeds,
    it will print error message saying that
    no rule applied.
    """
    if (process_list) == 1:
        return process_list[0](book, local_filename, link, report)
    # try them one by one
    for fn in process_list:
        action_list = []

        def store_report(*args):
            action_list.append(("report", *args))
        out = fn(book, local_filename, link, store_report)
        if out is None:
            continue
        # do actions
        for act in action_list:
            if act[0] == "report":
                report(*act[1:])
            else:
                assert False
        return out
    report(f"could not resolve \"{link}\"")
    return None


def process_path(book, local_filename, path, report):
    # check that path is in the summary (for md files)
    global g_args
    if path.name.endswith(".md") and not book.is_file_in_summary(path) and not g_args.ignore_book:
        report(f"link to \"{book.local_name(path)}\", which is not listed in SUMMARY.md")
        # at the moment, report the error but consider this a good link nonetheless
    return path  # this link is ok


def _process_relative_link(book, local_filename, link, report):
    # at this point, we know this is a local link and we want to check it
    # but also suggest some changes if we can figure out how to fix/lint it
    # the following function tries to resolve where this link should point to
    # then we compute how it should be written in the file
    # and if the result is different from the original, we suggest a rewrite
    debug(f"processing local link {link}")

    path = book.resolve_local_link(local_filename, link, report)
    debug(f"local link resolution gave {path}")
    if path is None:
        # cannot resolve link, assume that resolve_local_link reported the error
        return
    return process_path(book, local_filename, path, report)


def __process_hugo_relref(book, local_filename, link, report, local_search):
    # relref can either be relative path to this file or relative path
    # to the root of the documentation

    debug(f"internal processing hugo link {link}")

    if local_search:
        if link.startswith('/'):
            return None
        return _process_relative_link(book, local_filename, link, report)
    else:
        debug(f"try to resolve global link {link}")
        path = book.resolve_global_link(local_filename, link, report)
        if path is None:
            # cannot resolve link, assume that resolve_global_link reported the error
            return None
        return process_path(book, local_filename, path, report)


def _process_hugo_relref(book, local_filename, link, report):
    # Hugo references can do things like pointing to a file bla.md just by writing bla
    # this is makes it quite tricky since when we start mixing this up with move file
    # rewriting or guess of directories, there is no easy way to detect when we should
    # add .md to the link; similarly a link can point to a directory x/ in which case
    # it should be understood as pointing to x/_index.md or x/index.md
    # the solution is just to try with and without it
    debug(f"processing hugo relref {link}")

    def add_md(book, local_filename, link, report, local_search):
        if link.endswith(".md"):
            return None
        return __process_hugo_relref(book, local_filename, link + ".md", report, local_search)

    def add_subfile(book, local_filename, link, report, subfile, local_search):
        if link.endswith(".md"):
            return None
        suff = subfile if link.endswith('/') else '/' + subfile
        return __process_hugo_relref(book, local_filename, link + suff, report, local_search)
    # not that we try add .md only if the first (normal) resolution fails
    # following Hugo's documentation, we first try to resolve it relatively
    # to this file and then relatively to the repo (unless it starts with /
    # in which case it cannot be a relative link)
    processes = [
        # LOCAL search
        lambda *arg: __process_hugo_relref(*arg, True),  # normal processing
        lambda *arg: add_md(*arg, True),  # try to add .md add the end
        lambda *arg: add_subfile(*arg, "index.md", True),  # try to add /index.md
        lambda *arg: add_subfile(*arg, "_index.md", True),  # try to add /_index.md
        # GLOBAL search
        lambda *arg: __process_hugo_relref(*arg, False),  # normal processing
        lambda *arg: add_md(*arg, False),  # try to add .md add the end
        lambda *arg: add_subfile(*arg, "index.md", False),  # try to add /index.md
        lambda *arg: add_subfile(*arg, "_index.md", False),  # try to add /_index.md
    ]
    return try_several_resolutions(book, local_filename, link, processes, report)


def split_anchor_and(book, local_filename, link, process, report):
    arr = link.split("#")
    if len(arr) > 2:
        report(f"link \"{link}\" is weird, giving up on that one")
        return
    base = arr[0]
    anchor = "#" + arr[1] if len(arr) == 2 else ''
    if base == "":
        return
    debug(f"split link to base \"{base}\" and fragment \"{anchor}\"")
    path = process(book, local_filename, base, report)
    if path is None:
        return None
    else:
        return (path, anchor)


def process_relative_link(book, local_filename, link, report):
    return split_anchor_and(book, local_filename, link, _process_relative_link, report)


def process_hugo_relref(book, local_filename, link, report):
    return split_anchor_and(book, local_filename, link, _process_hugo_relref, report)


def show_unlisted_files(book):
    print(f"#### {book.path} ####")
    # check files not in summary
    header_printed = False
    for (name, in_summary) in book.allmdfiles.items():
        # obviously ignore SUMMARY.md
        if not in_summary and name.name != "SUMMARY.md":
            if not header_printed:
                print("Files not listed in SUMMARY.md:")
                header_printed = True
            print(f"- {name}")


# we will store the list of all suggestions and rewrite everything at the end
# for extra safety, when recording a suggestion, we not only memorize what
# we should change to, but also what we are changing from
# when doing the changes, we will check that this matches
g_suggestions = {}


def add_suggestion(path, line_nr, pos_range, oldvalue, newvalue):
    path = path.resolve()
    ff = g_suggestions.get(path, {})
    ll = ff.get(line_nr, {})
    ll[pos_range] = (oldvalue, newvalue)
    ff[line_nr] = ll
    g_suggestions[path] = ff

# apply all suggestions in a file


def apply_suggestions(filename, suggestions):
    out_content = ""
    with filename.open() as f:
        print(filename)
        line_nr = 0
        for line in f:
            line_nr += 1
            if line_nr in suggestions:
                pos_delta = 0
                for ((start, end), (oldvalue, newvalue)) in sorted(suggestions[line_nr].items(), key=lambda x: x[0][0]):
                    # adjust
                    start += pos_delta
                    end += pos_delta
                    # we make sure that the bit that we are replacing matches what it is supposed to replace
                    # this is just for extra safety, if there is no bug this assert will always hold
                    assert line[start:
                                end] == oldvalue, f"mismatch between expected old value ({oldvalue}) and actual old value ({line[start:end]})"
                    line = line[:start] + newvalue + line[end:]
                    # change delta
                    pos_delta += len(newvalue) - len(oldvalue)
            out_content += line
    filename.write_text(out_content)


def check_all_links(book):
    global g_args
    hugo_relref_prog = re.compile(r"^\{\{<\s*relref\s*\"(?P<url>[^\"]*)\"\s*>\}\}$")
    print(f"#### {book.path} ####")
    # for all listed file, check links
    for (name, in_summary) in book.allmdfiles.items():
        # debugging check
        if g_args.debug_only_file is not None:
            local_only_name = book.local_name(Path(g_args.debug_only_file))
            if local_only_name != name:
                continue  # skip file
        # we ignore files that are not in the summary (but we do check SUMMARY.md for bad links)
        # warning: the check for SUMMARY.md needs to be sure to only consider SUMMARY.md at the root
        # of the book, there could be others SUMMARY.md in the tree that are unrelated, we don't want to
        # include those if they are not listed
        if not g_args.ignore_book and not in_summary and name == Path("SUMMARY.md"):
            continue  # skip file
        # get links
        header_printed = False
        for (line_nr, posrange, link) in Book.list_links_in_file(book.srcdir / name):
            # debugging check
            oldname = None
            if g_args.debug_only_line is not None:
                only_line = int(g_args.debug_only_line)
                if line_nr != only_line:
                    continue  # skip line

            def suggest(newvalue):
                add_suggestion(book.srcdir / name, line_nr, posrange, link, newvalue)

            def report(msg):
                # it's global because the whole code is not in a function and nonlocal does not work in this case
                nonlocal header_printed
                if not header_printed:
                    if oldname is not None and oldname != name:
                        print(f"In {name} (previously {oldname}):")
                    else:
                        print(f"In {name}:")
                    header_printed = True
                print(f"- line {line_nr}: {msg}")

            def maybe_suggest_rewrite(res):
                if res is None:
                    return
                (path, fragment) = res
                # this link is good but maybe it is not written in the canonical way, warn about that
                relpath = relative_link_to(path, (book.srcdir / name).parent)
                newlink = str(relpath) + fragment
                if should_rewrite_link(newlink, link):
                    report(f"link \"{link}\" resolved to \"{newlink}\"")
                    report(f"SUGGEST rewrite link to \"{newlink}\"")
                    suggest(newlink)
            # link to internal doc that use the opentitan url
            if link.startswith("https://docs.opentitan.org/"):
                if g_args.warn_internal_weblinks:
                    report(f"link {link} points to internal document, use URL_ROOT or local link")
                continue
            # if this file was moved, we need to make sure that the relative links that we compute
            # are relative to the old position of the file
            oldname = book.local_name(book.path_exists_or_was_moved(book.srcdir / name, True))
            if oldname != name:
                debug(f"file {name} was previously {oldname}")
            # old Hugo links
            if link.startswith("{{<") or link.startswith("{{%"):
                # this tool only understands a tiny subset of those
                x = hugo_relref_prog.match(link)
                if x is not None:
                    res = process_hugo_relref(book, oldname, x["url"], report)
                    maybe_suggest_rewrite(res)
                elif g_args.warn_hugo_links:
                    report(f"link \"{link}\" uses old Hugo syntax")
                continue
            # URL outside of our doc or mailto
            if link.startswith("https://") or link.startswith("mailto:"):
                # ignore
                continue
            # unsecure url
            if link.startswith("http://"):
                report(f"url {link} is not secure")
                continue
            # cross-book links, not checking those yet
            if link.startswith("{{URL_ROOT}}"):
                report(f"link \"{link}\" NOT CHECKED")
                continue

            # try to resolve the path and suggest a rewriting if necessary
            res = process_relative_link(book, oldname, link, report)
            maybe_suggest_rewrite(res)


g_root_doc = Path(g_args.root_doc).resolve()
# if root doc is a link to a book.toml file, just open this one
if g_root_doc.is_file():
    assert g_root_doc.name == "book.toml", "you must give a path a book.toml file or a directory"
    g_book_list = [Book(g_root_doc.parent)]
elif g_args.ignore_book:
    # create a fake book that contains everything
    g_book_list = [Book(g_root_doc)]
else:
    g_book_list = find_all_books(g_root_doc)
print("books:")
for p in g_book_list:
    print("- {}".format(p))

# find all md files in the tree that are not listed in any SUMMARY.md
if not g_args.ignore_book and g_args.warn_unlisted_files:
    for book in g_book_list:
        show_unlisted_files(book)

for book in g_book_list:
    check_all_links(book)

print("### Summary of suggestions ###")
for (filename, per_file) in g_suggestions.items():
    print(f"In {filename}:")
    for (line_nr, per_line) in per_file.items():
        for (posrange, (oldvalue, newvalue)) in per_line.items():
            print(f"- line {line_nr},{posrange[0]}-{posrange[1]}: \"{oldvalue}\" -> \"{newvalue}\"")

if g_args.apply_suggestions:
    for (filename, per_file) in g_suggestions.items():
        apply_suggestions(filename, per_file)
