# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Provides lowRISC extension support for rendering Markdown to html.
{{% }} directives
!!Reg !!Reg.Field to generate cross reference to registers
Syntax highlighting with pygments
Conversion of WaveJSON timing diagrams
Adapted from examples in mistletoe.contrib
<https://github.com/miyuchina/mistletoe/blob/master/contrib/>
"""

import io
import logging as log
import os.path as path
import re
import subprocess
import sys
from itertools import chain
from os import walk
from pathlib import Path
from urllib.parse import urlparse, urlunparse

import hjson
import mistletoe.block_token
import mistletoe.span_token
from mistletoe import HTMLRenderer
from mistletoe.block_token import BlockToken, CodeFence, add_token, tokenize
from mistletoe.span_token import EscapeSequence, RawText, SpanToken
from pkg_resources import resource_filename
from pygments import highlight
from pygments.formatters.html import HtmlFormatter
from pygments.lexers import get_lexer_by_name as get_lexer
from pygments.lexers import guess_lexer
from pygments.styles import get_style_by_name as get_style

import dashboard.gen_dashboard_entry as gen_dashboard_entry
import reggen.gen_cfg_html as gen_cfg_html
import reggen.gen_html as gen_html
import reggen.validate as validate
from docgen import html_data, mathjax
from docgen.hjson_lexer import HjsonLexer
from testplanner import class_defs, testplan_utils
from wavegen import wavesvg


# mirrors Document but adds includes
# have to pull all the sub-files in to the main text so cross-links work
# By default anchor links only resolve within a single file
# arguably this is correct isolation but we want to be able to include anchors
class Document(BlockToken):
    """
    Document token with includes.
    """

    # Called when the include directive starts with a !
    # to indicate execute the first word as a command with rest as opts
    # To help avoid mistakes (and mimimally help avoid attacks in the case
    # of a trusted docgen given untrusted input files) the command must
    # live inside the repo (the example uses a local ls script to
    # run a command from outside, but the script was reviewed and checkedin)
    def exec_include(self, include_text, basedir):
        expand = include_text.split(maxsplit=1)
        cmd = expand[0]
        opts = '' if len(expand) < 2 else expand[1]
        abscmd = path.abspath(path.join(basedir, cmd))
        if not abscmd.startswith(self.treetop):
            log.error("Blocked include: " + cmd + ' (' + abscmd +
                      ") is outside the repo.")
            raise NameError('Command file must be in the repo')
        # do the cd in the subprocess to avoid save/restore of cwd
        res = subprocess.run(
            'cd ' + basedir + '; ' + abscmd + ' ' + opts,
            shell=True,
            universal_newlines=True,
            stdout=subprocess.PIPE).stdout
        return res.splitlines(keepends=True)

    def add_include(self, l, pat, basedir):
        lines = []
        for line in l:
            match = pat.search(line)
            # because this is pre-processed a sepcial case is needed to
            # allow documentation with include command inside back-ticks
            if (match and not (match.start() > 0 and
                               line[match.start() - 1] == '`')):
                lines.append(line[:match.start()] + line[match.end():])
                if match.group(1)[0] == "!":
                    try:
                        res = self.exec_include(match.group(1)[1:], basedir)
                        lines.extend(self.add_include(res, pat, basedir))
                    except NameError:
                        lines.append("Blocked execution of " + match.group(1))
                else:
                    incfname = path.join(basedir, match.group(1))
                    try:
                        incfile = open(incfname, 'r', encoding='UTF-8')
                        with incfile:
                            newdir = path.dirname(incfname)
                            lines.extend(
                                self.add_include(incfile, pat, newdir))
                    except OSError as err:
                        log.error("Could not open include file: " + str(err))
                        lines.append("Failed to include " + incfname + "\n\n")
            else:
                lines.append(line)
        return lines

    def __init__(self, lines, srcfile):
        docdir = path.dirname(resource_filename('docgen', 'md_html.css'))
        self.treetop = path.abspath(path.join(docdir, "../.."))
        pat = re.compile(r"\{\{\% *include +(.+?) *\}\}")
        basedir = ""
        if len(srcfile) > 0:
            basedir = path.dirname(srcfile)
        if basedir == '':
            basedir = '.'
        if isinstance(lines, str):
            lines = lines.splitlines(keepends=True)

        lines = self.add_include(lines, pat, basedir)
        self.footnotes = {}
        mistletoe.block_token._root_node = self
        mistletoe.span_token._root_node = self
        self.children = tokenize(lines)
        mistletoe.span_token._root_node = None
        mistletoe.block_token._root_node = None


# mirrors the CodeFence in mistletoe but with additional parameter
# note this maintains the bug with `~` matching the RE
class CodeFenceDirective(CodeFence):
    """
    Code fence with language and directive

    Supports code blocks starting
    ```language {directive}
    Up to 3 spaces indentation, minimum of 3 fence characters,
    optional spaces, language text, optional spaces, open {,
    optional spaces, directive text, optional spaces, close }
    at the moment there cannot be spaces inside language or directive
    """
    # future may want something like \{ *([^\}]*\} for multiple directives
    pattern = re.compile(r'( {0,3})((?:`|~){3,}) *(\S+) *\{ *(\S*) *\}')
    _open_info = None

    def __init__(self, match):
        lines, open_info = match
        self.language = EscapeSequence.strip(open_info[2])
        self.directive = EscapeSequence.strip(open_info[3])
        self.children = (RawText(''.join(lines)), )

    @classmethod
    def start(cls, line):
        match_obj = cls.pattern.match(line)
        if not match_obj:
            return False
        prepend, leader, lang, direct = match_obj.groups()
        if (leader[0] in lang or leader[0] in direct or
                leader[0] in line[match_obj.end():]):
            return False
        cls._open_info = len(prepend), leader, lang, direct
        return True


class LowriscEscape(SpanToken):
    pattern = re.compile(r"\{\{\% *(.+?) +(.+?) *\}\}")

    def __init__(self, match):
        self.type = match.group(1)
        self.text = match.group(2)


class RegRef(SpanToken):
    pattern = re.compile(r"!!([A-Za-z0-9_.]+)")

    def __init__(self, match):
        self.rname = match.group(1)


class LowriscRenderer(mathjax.MathJaxRenderer):
    formatter = HtmlFormatter()
    formatter.noclasses = True

    def __init__(self, *extras, style='default', srcfile='', wavejs=False):
        # yapf requests different formatting for this code block depending on
        # the Python3 version. Work around that by disabling yapf for this code
        # block.
        # Bug: https://github.com/google/yapf/issues/696
        # yapf: disable
        super().__init__(*chain((LowriscEscape, RegRef,
                                 CodeFenceDirective), extras))
        # yapf: enable
        self.formatter.style = get_style(style)
        self.regs = None
        self.wavejs = wavejs
        self.num_svg = 0
        # compute base of srcfile to allow relative imports
        basedir = ""
        if len(srcfile) > 0:
            basedir = path.dirname(srcfile)
        self.basedir = basedir
        self.toc = []

    # Convert the inner text of header or section into id for html href
    # inner is a flat string but may have html tags
    # html id rules are:
    #    Must contain at least one character
    #    Must not contain any space characters
    # Want to match github, can't find its exact rules
    # The id is derived from the heading text by stripping html tags,
    # changing whitespace to - and lower-casing.
    # e.g. 'Theory of operation' becomes 'theory-of-operation
    # TODO worry about & eg 'Foo & Bar' becomes 'foo-&-bar'
    def id_from_inner(self, inner):
        return re.sub(r'\s+', '-', re.sub(r'<.+?>', '', inner)).lower()

    def render_lowrisc_code(self, token, directive):
        code = token.children[0].content
        # parser seems to get confused (eg by `~`) and makes empty calls
        if len(code) == 0:
            log.warn('Unexpected empty code block. Check for `~`')
            return ""
        # waveforms look like embedded code in the markdown
        # but the WaveDrom javascript wants it in a script tag
        if token.language == "wavejson":
            if self.wavejs:
                return '<script type="WaveDrom">' + code + '</script>'
            else:
                try:
                    wvobj = hjson.loads(code, use_decimal=True)
                except ValueError as err:
                    log.warn('wavejson parse failed at line ' +
                             str(err.lineno) + ': ' + err.msg)
                    return '<pre>Error line '  + str(err.lineno) + \
                        ': ' + err.msg + " in:\n" + code[:err.pos] + \
                        '</pre><pre style="color:red">' + \
                        code[err.pos:] + '</pre>'
                self.num_svg += 1
                return wavesvg.convert(wvobj, self.num_svg - 1)
        else:
            # pygments.util.ClassNotFound subclass of ValueError
            lexer = None
            if (token.language):
                if token.language == 'hjson':
                    lexer = HjsonLexer()
                else:
                    try:
                        lexer = get_lexer(token.language)
                    except ValueError:
                        log.info('Failed to get lexer for language=' +
                                 token.language)
                        lexer = None
            if lexer == None:
                try:
                    lexer = guess_lexer(code)
                    log.info('Guess lexer as ' + lexer.name)
                except ValueError:
                    log.info('Failed to guess lexer for code=' + code)
                    lexer = None
            if lexer:
                if directive == '.good':
                    self.formatter.cssstyles='background:#e0ffe0; ' \
                        'border-left-color: #108040;'
                elif directive == '.bad':
                    self.formatter.cssstyles='background:#ffe0e0; ' \
                        'border-left-color: #c04030'
                else:
                    self.formatter.cssstyles = ''

                return highlight(code, lexer, self.formatter)
            else:
                return super().render_block_code(token)

    def render_code_fence_directive(self, token):
        return self.render_lowrisc_code(token, token.directive)

    def render_block_code(self, token):
        return self.render_lowrisc_code(token, '')

    def render_lowrisc_escape(self, token):
        # plan eventually to allow lowrisc-doc-hdr=doctype
        if token.type[:15] == "lowrisc-doc-hdr":
            return html_data.lowrisc_title_head + token.text + \
                   html_data.lowrisc_title_tail
        if token.type == "toc":
            return html_data.toc_mark_head + token.text + \
                   html_data.toc_mark_tail
        if token.type == "regfile":
            regfile = open(
                path.join(self.basedir, token.text), 'r', encoding='UTF-8')
            with regfile:
                try:
                    obj = hjson.load(
                        regfile,
                        use_decimal=True,
                        object_pairs_hook=validate.checking_dict)
                except ValueError:
                    raise SystemExit(sys.exc_info()[1])
            if validate.validate(obj) == 0:
                log.info("Generated register object\n")
                self.regs = obj
            else:
                log.warn("Register import failed\n")
                self.regs = None
            return ""
        if token.type == "registers":
            if self.regs == None:
                return "<B>Errors parsing registers prevents insertion.</B>"
            outbuf = io.StringIO()
            # note for CSS need to escape the mdown class on the div
            outbuf.write("</div>" + html_data.register_header)
            gen_html.gen_html(self.regs, outbuf, toclist=self.toc, toclevel=3)
            outbuf.write(html_data.register_trailer + '<div class="mdown">')
            generated = outbuf.getvalue()
            outbuf.close()
            return generated
        if token.type == "cfgfile":
            log.error("Deprecated lowRISC token cfgfile ignored. Config is now"\
                      " in a single file with the registers!")
            return ""
        if token.type == "hwcfg":
            if self.regs == None:
                return "<B>Errors parsing configuration prevents insertion.</B>"
            outbuf = io.StringIO()
            # note for CSS need to escape the mdown class on the div
            outbuf.write("</div>" + html_data.hwcfg_header)
            gen_cfg_html.gen_cfg_html(self.regs, outbuf)
            outbuf.write(html_data.hwcfg_trailer + '<div class="mdown">')
            generated = outbuf.getvalue()
            outbuf.close()
            return generated
        if token.type == "section1":
            # TODO should token.text get parsed to allow markdown in it?
            id = self.id_from_inner(token.text)
            self.toc.append((2, token.text, id))
            return html_data.section_template.format(
                cls="section_heading", id=id, inner=token.text)
        if token.type == "section2":
            # TODO should token.text get parsed to allow markdown in it?
            id = self.id_from_inner(token.text)
            self.toc.append((3, token.text, id))
            return html_data.section_template.format(
                cls="subsection_heading", id=id, inner=token.text)
        if token.type == "doctree":
            md_paths = []
            return_string = ''
            subdirs = [path.join(self.basedir, s) for s in token.text.split()]
            for subdir in sorted(subdirs):
                md_paths.extend(sorted(Path(subdir).rglob('*.md')))
            for md_path in md_paths:
                rel_md_path = md_path.relative_to(self.basedir)
                return_string += html_data.doctree_template.format(
                    link=rel_md_path.with_suffix('.html'),
                    text=rel_md_path.with_suffix(''))
            return html_data.doctree_head + return_string + html_data.doctree_tail
        if token.type == "import_testplan":
            self.testplan = testplan_utils.parse_testplan(
                path.join(self.basedir, token.text))
            return ""
        if token.type == "insert_testplan":
            if self.testplan == None:
                return "<B>Errors parsing testplan prevents insertion.</B>"
            outbuf = io.StringIO()
            testplan_utils.gen_html_testplan_table(self.testplan, outbuf)
            generated = outbuf.getvalue()
            outbuf.close()
            return generated
        if token.type == "dashboard":
            hjson_paths = []
            # find all of the .prj.hjson files in the given path
            hjson_paths.extend(
                sorted(
                    Path(path.join(self.basedir,
                                   token.text)).rglob('*.prj.hjson')))
            outbuf = io.StringIO()
            outbuf.write(html_data.dashboard_header)
            for hjson_path in hjson_paths:
                gen_dashboard_entry.gen_html(hjson_path, outbuf)
            outbuf.write(html_data.dashboard_trailer)
            generated = outbuf.getvalue()
            outbuf.close()
            return generated

        bad_tag = '{{% ' + token.type + ' ' + token.text + ' }}'
        log.warn("Unknown lowRISC tag " + bad_tag)
        return bad_tag

    def render_reg_ref(self, token):
        if self.regs == None:
            log.warn("!!" + token.rname + ": no register import was done.")
            return '!!' + token.rname
        cname = self.regs['name']
        base = token.rname.partition('.')[0].lower()
        if not base in self.regs['genrnames']:
            log.warn("!!" + token.rname + " not found in register list.")
            return '!!' + token.rname

        if token.rname[-1] == ".":
            return '<a href="#Reg_' + base + '"><code class=\"reg\">' + \
                cname + "." + token.rname[:-1] + '</code></a>.'
        else:
            return '<a href="#Reg_' + base + '"><code class=\"reg\">' + \
                cname + "." + token.rname + '</code></a>'

    # copied from mistletoe/html_renderer.py and id added
    # override heading to insert reference for anchor
    def render_heading(self, token):
        template = '<h{level} id="{id}">{inner}</h{level}>'
        inner = self.render_inner(token)
        id = self.id_from_inner(inner)
        self.toc.append((token.level, inner, id))
        return template.format(level=token.level, inner=inner, id=id)

    # decorator for link rendering functions in class HTMLRenderer
    # converts relative .md link targets to .html link targets
    def _convert_local_links(func):
        def _wrapper_convert_local_links(*args, **kwargs):
            target_url = urlparse(args[1].target)
            target_path = Path(target_url.path)
            # check link is not absolute
            if not target_url.netloc and target_path.suffix in ['.md', '.mkd']:
                target_url = target_url._replace(
                    path=str(target_path.with_suffix('.html')))
                args[1].target = urlunparse(target_url)

            return func(*args, **kwargs)

        return _wrapper_convert_local_links

    # apply to the link rendering functions inherited from HTMLRenderer
    render_link = _convert_local_links(HTMLRenderer.render_link)
    render_auto_link = _convert_local_links(HTMLRenderer.render_auto_link)
