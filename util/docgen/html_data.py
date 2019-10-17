# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

header_wavejs = """
<html>
<head>
<meta charset="UTF-8">
<script src="https://cdnjs.cloudflare.com/ajax/libs/wavedrom/2.1.2/skins/default.js"
        type="text/javascript"></script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/wavedrom/2.1.2/wavedrom.min.js"
       type="text/javascript"></script>
</head>
<body onload="WaveDrom.ProcessAll()">
"""

header_waveinline = """
<html>
<head>
<meta charset="UTF-8">
</head>
"""

header_asdiv = """
<div>
"""

markdown_header = """
<div class="mdown">
"""

markdown_trailer = """
</div>
"""

register_header = """
<div>
"""

register_trailer = """
</div>
"""

hwcfg_header = """
<div class="mdown">
"""

hwcfg_trailer = """
</div>
"""

trailer = """
</body>
</html>
"""

trailer_asdiv = """
</div>
"""

lowrisc_title_head = """
<table class="section_heading">
<tr><td>lowRISC Comportable IP Document</td></tr>
<tr><td>
"""

lowrisc_title_tail = """
</td></tr>
<tr><td>&copy; lowrisc.org Contributors</td></tr></table>
"""

section_template = """
<table class="{cls}" id="{id}">
<tr><td>{inner}</td></tr></table>
"""

doctree_head = "<ul>"
doctree_template = """
<li> <a href="{link}">{text}</a> </li>
"""
doctree_tail = "</ul>"

toc_title = """
<h2>Table of Contents</h2>
"""

toc_mark_head = "<!--TOC "
toc_mark_tail = "-->\n"

dashboard_header = """
  <table class="hw-project-dashboard">
    <thead>
      <tr>
        <th>Module</th>
        <th>Version</th>
        <th>Life Stage</th>
        <th>Design Stage</th>
        <th>Verification Stage</th>
        <th>Notes</th>
      </tr>
    </thead>
    <tbody>
"""
dashboard_trailer = """
    </tbody>
  </table>
"""
