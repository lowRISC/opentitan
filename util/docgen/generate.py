# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging
import os
import shutil
import sys

import mistletoe
from pkg_resources import resource_filename

from . import html_data, lowrisc_renderer


def generate_doc(src_path, verbose, inlinecss, inlinewave, asdiv):
    """Generate Document for other library to use
    """

    if src_path == '-':
        infile = sys.stdin
    else:
        if os.path.isfile(src_path):
            infile = open(src_path, 'r', encoding='UTF-8')
        else:
            logging.error("Source is not a file: %s", src_path)
            return ""

    if (asdiv):
        outstr = html_data.header_asdiv
        # no body to add the onload to, so must inline waveforms
        inlinewave = True
    elif (inlinewave):
        outstr = html_data.header_waveinline
    else:
        outstr = html_data.header_wavejs

    if (asdiv):
        logging.info("asdiv: no CSS included")
    elif (inlinecss):
        outstr += "<style type='text/css'>"
        with open(
                resource_filename('docgen', 'md_html.css'), 'r',
                encoding='UTF-8') as fin:
            outstr += fin.read()
        with open(
                resource_filename('reggen', 'reg_html.css'), 'r',
                encoding='UTF-8') as fin:
            outstr += fin.read()
        outstr += "</style>"
    else:
        outstr += '<link rel="stylesheet" type="text/css" href="md_html.css">'
        outstr += '<link rel="stylesheet" type="text/css" href="reg_html.css">'

    outstr += html_data.markdown_header

    # lowrisc_renderer.Document rather than mistletoe.Document to get includes
    with infile:
        with lowrisc_renderer.LowriscRenderer(
                srcfile=src_path, wavejs=not inlinewave) as renderer:
            document = lowrisc_renderer.Document(infile, src_path)
            rendered = renderer.render(document)
            tocpos = rendered.find(html_data.toc_mark_head)
            toc = renderer.toc
            if tocpos < 0 or len(toc) == 0:
                outstr += rendered
            else:
                tocp = tocpos + len(html_data.toc_mark_head)
                toci = tocp
                while rendered[tocp] != '-':
                    tocp += 1
                maxlvl = int(rendered[toci:tocp])
                outstr += rendered[:tocpos]
                outstr += html_data.toc_title
                outstr += '<ul>\n'
                lvl = 2
                for x in toc:
                    # don't expect H1, collapse to H2 if it is there
                    wantlvl = x[0] if x[0] > 1 else 2
                    if (wantlvl > maxlvl):
                        continue
                    while lvl < wantlvl:
                        outstr += '<ul>\n'
                        lvl += 1
                    while lvl > wantlvl:
                        outstr += '</ul>\n'
                        lvl -= 1
                    outstr += '<li><a href=#' + x[2] + '>' + x[1] + '</a>\n'
                while lvl > 1:
                    outstr += '</ul>\n'
                    lvl -= 1
                outstr += rendered[tocpos:]

    outstr += html_data.markdown_trailer
    outstr += html_data.trailer_asdiv if asdiv else html_data.trailer

    return outstr
