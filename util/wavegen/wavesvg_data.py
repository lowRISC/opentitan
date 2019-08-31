# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# portions adapted from the javascript wavedrom.js
# https://github.com/drom/wavedrom/blob/master/wavedrom.js
# see LICENSE.wavedrom

head1 = """
   xmlns="http://www.w3.org/2000/svg"
   xmlns:xlink="http://www.w3.org/1999/xlink"
   overflow="hidden"
"""

# Styles are from wavedrom.js
head2 = """
    <style type="text/css">
      text { font-size: 11pt; font-style: normal; font-variant:
      normal; font-weight: normal; font-stretch: normal;
      text-align: center; fill-opacity: 1; font-family:
      Helvetica }

      .muted {
      fill: #aaa
      }

      .warning {
      fill: #f6b900
      }

      .error {
      fill: #f60000
      }

      .info {
      fill: #0041c4
      }

      .success {
      fill: #00ab00
      }

      .h1 {
      font-size: 33pt;
      font-weight: bold
      }

      .h2 {
      font-size: 27pt;
      font-weight: bold
      }

      .h3 {
      font-size: 20pt;
      font-weight: bold
      }

      .h4 {
      font-size: 14pt;
      font-weight: bold
      }

      .h5 {
      font-size: 11pt;
      font-weight: bold
      }

      .h6 {
      font-size: 8pt;
      font-weight: bold
      }

      .s1 {
      fill: none;
      stroke: #000;
      stroke-width: 1;
      stroke-linecap: round;
      stroke-linejoin: miter;
      stroke-miterlimit: 4;
      stroke-opacity: 1;
      stroke-dasharray: none
      }

      .s2 {
      fill: none;
      stroke: #000;
      stroke-width: 0.5;
      stroke-linecap: round;
      stroke-linejoin: miter;
      stroke-miterlimit: 4;
      stroke-opacity: 1;
      stroke-dasharray: none
      }

      .s3 {
      color: #000;
      fill: none;
      stroke: #000;
      stroke-width: 1;
      stroke-linecap: round;
      stroke-linejoin: miter;
      stroke-miterlimit: 4;
      stroke-opacity: 1;
      stroke-dasharray: 1, 3;
      stroke-dashoffset: 0;
      marker: none;
      visibility: visible;
      display: inline;
      overflow: visible;
      enable-background: accumulate
      }

      .s4 {
      color: #000;
      fill: none;
      stroke: #000;
      stroke-width: 1;
      stroke-linecap: round;
      stroke-linejoin: miter;
      stroke-miterlimit: 4;
      stroke-opacity: 1;
      stroke-dasharray: none;
      stroke-dashoffset: 0;
      marker: none;
      visibility: visible;
      display: inline;
      overflow: visible
      }

      .s5 {
      fill: #fff;
      stroke: none
      }

      .s6 {
      color: #000;
      fill: #ffffb4;
      fill-opacity: 1;
      fill-rule: nonzero;
      stroke: none;
      stroke-width: 1px;
      marker: none;
      visibility: visible;
      display: inline;
      overflow: visible;
      enable-background: accumulate
      }

      .s7 {
      color: #000;
      fill: #ffe0b9;
      fill-opacity: 1;
      fill-rule: nonzero;
      stroke: none;
      stroke-width: 1px;
      marker: none;
      visibility: visible;
      display: inline;
      overflow: visible;
      enable-background: accumulate
      }

      .s8 {
      color: #000;
      fill: #b9e0ff;
      fill-opacity: 1;
      fill-rule: nonzero;
      stroke: none;
      stroke-width: 1px;
      marker: none;
      visibility: visible;
      display: inline;
      overflow: visible;
      enable-background: accumulate
      }

      .s9 {
      fill: #000;
      fill-opacity: 1;
      stroke: none
      }

      .s10 {
      color: #000;
      fill: #fff;
      fill-opacity: 1;
      fill-rule: nonzero;
      stroke: none;
      stroke-width: 1px;
      marker: none;
      visibility: visible;
      display: inline;
      overflow: visible;
      enable-background: accumulate
      }

      .s11 {
      fill: #0041c4;
      fill-opacity: 1;
      stroke: none
      }

      .s12 {
      fill: none;
      stroke: #0041c4;
      stroke-width: 1;
      stroke-linecap: round;
      stroke-linejoin: miter;
      stroke-miterlimit: 4;
      stroke-opacity: 1;
      stroke-dasharray: none
      }
    </style>
"""

defs_head = """
    <defs>
"""

defs_tail = """
    </defs>
"""

tail = """
  </svg>
"""

# Brick definitions from wavedrom.js
# Split out here so only the ones that are used are inserted in the svg

use_defs = {
    'arrows':
    '''      <marker id="arrowhead" style="fill: rgb(0, 65, 196);" markerHeight="7" markerWidth="10" markerUnits="strokeWidth" viewBox="0 -4 11 8" refX="15" refY="0" orient="auto">
        <path d="M0 -4 11 0 0 4z"></path>
      </marker>
      <marker id="arrowtail" style="fill: rgb(0, 65, 196);" markerHeight="7" markerWidth="10" markerUnits="strokeWidth" viewBox="-11 -4 11 8" refX="-15" refY="0" orient="auto">
        <path d="M0 -4 -11 0 0 4z"></path>
      </marker>
''',
    'socket':
    '''      <g id="socket">
        <rect y="15" x="6" height="20" width="20"></rect>
      </g>''',
    'pclk':
    '''      <g id="pclk">
        <path d="M0,20 0,0 20,0" class="s1"></path>
      </g>''',
    'nclk':
    '''      <g id="nclk">
        <path d="m0,0 0,20 20,0" class="s1"></path>
      </g>''',
    '000':
    '''      <g id="000">
        <path d="m0,20 20,0" class="s1"></path>
      </g>''',
    '0m0':
    '''      <g id="0m0">
        <path d="m0,20 3,0 3,-10 3,10 11,0" class="s1"></path>
      </g>''',
    '0m1':
    '''      <g id="0m1">
        <path d="M0,20 3,20 9,0 20,0" class="s1"></path>
      </g>''',
    '0mx':
    '''      <g id="0mx">
        <path d="M3,20 9,0 20,0" class="s1"></path>
        <path d="m20,15 -5,5" class="s2"></path>
        <path d="M20,10 10,20" class="s2"></path>
        <path d="M20,5 5,20" class="s2"></path>
        <path d="M20,0 4,16" class="s2"></path>
        <path d="M15,0 6,9" class="s2"></path>
        <path d="M10,0 9,1" class="s2"></path>
        <path d="m0,20 20,0" class="s1"></path>
      </g>''',
    '0md':
    '''      <g id="0md">
        <path d="m8,20 10,0" class="s3"></path>
        <path d="m0,20 5,0" class="s1"></path>
      </g>''',
    '0mu':
    '''      <g id="0mu">
        <path d="m0,20 3,0 C 7,10 10.107603,0 20,0" class="s1"></path>
      </g>''',
    '0mz':
    '''      <g id="0mz">
        <path d="m0,20 3,0 C 10,10 15,10 20,10" class="s1"></path>
      </g>''',
    '111':
    '''      <g id="111">
        <path d="M0,0 20,0" class="s1"></path>
      </g>''',
    '1m0':
    '''      <g id="1m0">
        <path d="m0,0 3,0 6,20 11,0" class="s1"></path>
      </g>''',
    '1m1':
    '''      <g id="1m1">
        <path d="M0,0 3,0 6,10 9,0 20,0" class="s1"></path>
      </g>''',
    '1mx':
    '''      <g id="1mx">
        <path d="m3,0 6,20 11,0" class="s1"></path>
        <path d="M0,0 20,0" class="s1"></path>
        <path d="m20,15 -5,5" class="s2"></path>
        <path d="M20,10 10,20" class="s2"></path>
        <path d="M20,5 8,17" class="s2"></path>
        <path d="M20,0 7,13" class="s2"></path>
        <path d="M15,0 6,9" class="s2"></path>
        <path d="M10,0 5,5" class="s2"></path>
        <path d="M3.5,1.5 5,0" class="s2"></path>
      </g>''',
    '1md':
    '''      <g id="1md">
        <path d="m0,0 3,0 c 4,10 7,20 17,20" class="s1"></path>
      </g>''',
    '1mu':
    '''      <g id="1mu">
        <path d="M0,0 5,0" class="s1"></path>
        <path d="M8,0 18,0" class="s3"></path>
      </g>''',
    '1mz':
    '''      <g id="1mz">
        <path d="m0,0 3,0 c 7,10 12,10 17,10" class="s1"></path>
      </g>''',
    'xxx':
    '''      <g id="xxx">
        <path d="m0,20 20,0" class="s1"></path>
        <path d="M0,0 20,0" class="s1"></path>
        <path d="M0,5 5,0" class="s2"></path>
        <path d="M0,10 10,0" class="s2"></path>
        <path d="M0,15 15,0" class="s2"></path>
        <path d="M0,20 20,0" class="s2"></path>
        <path d="M5,20 20,5" class="s2"></path>
        <path d="M10,20 20,10" class="s2"></path>
        <path d="m15,20 5,-5" class="s2"></path>
      </g>''',
    'xm0':
    '''      <g id="xm0">
        <path d="M0,0 4,0 9,20" class="s1"></path>
        <path d="m0,20 20,0" class="s1"></path>
        <path d="M0,5 4,1" class="s2"></path>
        <path d="M0,10 5,5" class="s2"></path>
        <path d="M0,15 6,9" class="s2"></path>
        <path d="M0,20 7,13" class="s2"></path>
        <path d="M5,20 8,17" class="s2"></path>
      </g>''',
    'xm1':
    '''      <g id="xm1">
        <path d="M0,0 20,0" class="s1"></path>
        <path d="M0,20 4,20 9,0" class="s1"></path>
        <path d="M0,5 5,0" class="s2"></path>
        <path d="M0,10 9,1" class="s2"></path>
        <path d="M0,15 7,8" class="s2"></path>
        <path d="M0,20 5,15" class="s2"></path>
      </g>''',
    'xmx':
    '''      <g id="xmx">
        <path d="m0,20 20,0" class="s1"></path>
        <path d="M0,0 20,0" class="s1"></path>
        <path d="M0,5 5,0" class="s2"></path>
        <path d="M0,10 10,0" class="s2"></path>
        <path d="M0,15 15,0" class="s2"></path>
        <path d="M0,20 20,0" class="s2"></path>
        <path d="M5,20 20,5" class="s2"></path>
        <path d="M10,20 20,10" class="s2"></path>
        <path d="m15,20 5,-5" class="s2"></path>
      </g>''',
    'xmd':
    '''      <g id="xmd">
        <path d="m0,0 4,0 c 3,10 6,20 16,20" class="s1"></path>
        <path d="m0,20 20,0" class="s1"></path>
        <path d="M0,5 4,1" class="s2"></path>
        <path d="M0,10 5.5,4.5" class="s2"></path>
        <path d="M0,15 6.5,8.5" class="s2"></path>
        <path d="M0,20 8,12" class="s2"></path>
        <path d="m5,20 5,-5" class="s2"></path>
        <path d="m10,20 2.5,-2.5" class="s2"></path>
      </g>''',
    'xmu':
    '''      <g id="xmu">
        <path d="M0,0 20,0" class="s1"></path>
        <path d="m0,20 4,0 C 7,10 10,0 20,0" class="s1"></path>
        <path d="M0,5 5,0" class="s2"></path>
        <path d="M0,10 10,0" class="s2"></path>
        <path d="M0,15 10,5" class="s2"></path>
        <path d="M0,20 6,14" class="s2"></path>
      </g>''',
    'xmz':
    '''      <g id="xmz">
        <path d="m0,0 4,0 c 6,10 11,10 16,10" class="s1"></path>
        <path d="m0,20 4,0 C 10,10 15,10 20,10" class="s1"></path>
        <path d="M0,5 4.5,0.5" class="s2"></path>
        <path d="M0,10 6.5,3.5" class="s2"></path>
        <path d="M0,15 8.5,6.5" class="s2"></path>
        <path d="M0,20 11.5,8.5" class="s2"></path>
      </g>''',
    'ddd':
    '''      <g id="ddd">
        <path d="m0,20 20,0" class="s3"></path>
      </g>''',
    'dm0':
    '''      <g id="dm0">
        <path d="m0,20 10,0" class="s3"></path>
        <path d="m12,20 8,0" class="s1"></path>
      </g>''',
    'dm1':
    '''      <g id="dm1">
        <path d="M0,20 3,20 9,0 20,0" class="s1"></path>
      </g>''',
    'dmx':
    '''      <g id="dmx">
        <path d="M3,20 9,0 20,0" class="s1"></path>
        <path d="m20,15 -5,5" class="s2"></path>
        <path d="M20,10 10,20" class="s2"></path>
        <path d="M20,5 5,20" class="s2"></path>
        <path d="M20,0 4,16" class="s2"></path>
        <path d="M15,0 6,9" class="s2"></path>
        <path d="M10,0 9,1" class="s2"></path>
        <path d="m0,20 20,0" class="s1"></path>
      </g>''',
    'dmd':
    '''      <g id="dmd">
        <path d="m0,20 20,0" class="s3"></path>
      </g>''',
    'dmu':
    '''      <g id="dmu">
        <path d="m0,20 3,0 C 7,10 10.107603,0 20,0" class="s1"></path>
      </g>''',
    'dmz':
    '''      <g id="dmz">
        <path d="m0,20 3,0 C 10,10 15,10 20,10" class="s1"></path>
      </g>''',
    'uuu':
    '''      <g id="uuu">
        <path d="M0,0 20,0" class="s3"></path>
      </g>''',
    'um0':
    '''      <g id="um0">
        <path d="m0,0 3,0 6,20 11,0" class="s1"></path>
      </g>''',
    'um1':
    '''      <g id="um1">
        <path d="M0,0 10,0" class="s3"></path>
        <path d="m12,0 8,0" class="s1"></path>
      </g>''',
    'umx':
    '''      <g id="umx">
        <path d="m3,0 6,20 11,0" class="s1"></path>
        <path d="M0,0 20,0" class="s1"></path>
        <path d="m20,15 -5,5" class="s2"></path>
        <path d="M20,10 10,20" class="s2"></path>
        <path d="M20,5 8,17" class="s2"></path>
        <path d="M20,0 7,13" class="s2"></path>
        <path d="M15,0 6,9" class="s2"></path>
        <path d="M10,0 5,5" class="s2"></path>
        <path d="M3.5,1.5 5,0" class="s2"></path>
      </g>''',
    'umd':
    '''      <g id="umd">
        <path d="m0,0 3,0 c 4,10 7,20 17,20" class="s1"></path>
      </g>''',
    'umu':
    '''      <g id="umu">
        <path d="M0,0 20,0" class="s3"></path>
      </g>''',
    'umz':
    '''      <g id="umz">
        <path d="m0,0 3,0 c 7,10 12,10 17,10" class="s4"></path>
      </g>''',
    'zzz':
    '''      <g id="zzz">
        <path d="m0,10 20,0" class="s1"></path>
      </g>''',
    'zm0':
    '''      <g id="zm0">
        <path d="m0,10 6,0 3,10 11,0" class="s1"></path>
      </g>''',
    'zm1':
    '''      <g id="zm1">
        <path d="M0,10 6,10 9,0 20,0" class="s1"></path>
      </g>''',
    'zmx':
    '''      <g id="zmx">
        <path d="m6,10 3,10 11,0" class="s1"></path>
        <path d="M0,10 6,10 9,0 20,0" class="s1"></path>
        <path d="m20,15 -5,5" class="s2"></path>
        <path d="M20,10 10,20" class="s2"></path>
        <path d="M20,5 8,17" class="s2"></path>
        <path d="M20,0 7,13" class="s2"></path>
        <path d="M15,0 6.5,8.5" class="s2"></path>
        <path d="M10,0 9,1" class="s2"></path>
      </g>''',
    'zmd':
    '''      <g id="zmd">
        <path d="m0,10 7,0 c 3,5 8,10 13,10" class="s1"></path>
      </g>''',
    'zmu':
    '''      <g id="zmu">
        <path d="m0,10 7,0 C 10,5 15,0 20,0" class="s1"></path>
      </g>''',
    'zmz':
    '''      <g id="zmz">
        <path d="m0,10 20,0" class="s1"></path>
      </g>''',
    'gap':
    '''      <g id="gap">
        <path d="m7,-2 -4,0 c -5,0 -5,24 -10,24 l 4,0 C 2,22 2,-2 7,-2 z" class="s5"></path>
        <path d="M-7,22 C -2,22 -2,-2 3,-2" class="s1"></path>
        <path d="M-3,22 C 2,22 2,-2 7,-2" class="s1"></path>
      </g>''',
    '0mv-3':
    '''      <g id="0mv-3">
        <path d="M9,0 20,0 20,20 3,20 z" class="s6"></path>
        <path d="M3,20 9,0 20,0" class="s1"></path>
        <path d="m0,20 20,0" class="s1"></path>
      </g>''',
    '1mv-3':
    '''      <g id="1mv-3">
        <path d="M2.875,0 20,0 20,20 9,20 z" class="s6"></path>
        <path d="m3,0 6,20 11,0" class="s1"></path>
        <path d="M0,0 20,0" class="s1"></path>
      </g>''',
    'xmv-3':
    '''      <g id="xmv-3">
        <path d="M9,0 20,0 20,20 9,20 6,10 z" class="s6"></path>
        <path d="M0,20 3,20 9,0 20,0" class="s1"></path>
        <path d="m0,0 3,0 6,20 11,0" class="s1"></path>
        <path d="M0,5 3.5,1.5" class="s2"></path>
        <path d="M0,10 4.5,5.5" class="s2"></path>
        <path d="M0,15 6,9" class="s2"></path>
        <path d="M0,20 4,16" class="s2"></path>
      </g>''',
    'dmv-3':
    '''      <g id="dmv-3">
        <path d="M9,0 20,0 20,20 3,20 z" class="s6"></path>
        <path d="M3,20 9,0 20,0" class="s1"></path>
        <path d="m0,20 20,0" class="s1"></path>
      </g>''',
    'umv-3':
    '''      <g id="umv-3">
        <path d="M3,0 20,0 20,20 9,20 z" class="s6"></path>
        <path d="m3,0 6,20 11,0" class="s1"></path>
        <path d="M0,0 20,0" class="s1"></path>
      </g>''',
    'zmv-3':
    '''      <g id="zmv-3">
        <path d="M9,0 20,0 20,20 9,20 6,10 z" class="s6"></path>
        <path d="m6,10 3,10 11,0" class="s1"></path>
        <path d="M0,10 6,10 9,0 20,0" class="s1"></path>
      </g>''',
    'vvv-3':
    '''      <g id="vvv-3">
        <path d="M20,20 0,20 0,0 20,0" class="s6"></path>
        <path d="m0,20 20,0" class="s1"></path>
        <path d="M0,0 20,0" class="s1"></path>
      </g>''',
    'vm0-3':
    '''      <g id="vm0-3">
        <path d="M0,20 0,0 3,0 9,20" class="s6"></path>
        <path d="M0,0 3,0 9,20" class="s1"></path>
        <path d="m0,20 20,0" class="s1"></path>
      </g>''',
    'vm1-3':
    '''      <g id="vm1-3">
        <path d="M0,0 0,20 3,20 9,0" class="s6"></path>
        <path d="M0,0 20,0" class="s1"></path>
        <path d="M0,20 3,20 9,0" class="s1"></path>
      </g>''',
    'vmx-3':
    '''      <g id="vmx-3">
        <path d="M0,0 0,20 3,20 6,10 3,0" class="s6"></path>
        <path d="m0,0 3,0 6,20 11,0" class="s1"></path>
        <path d="M0,20 3,20 9,0 20,0" class="s1"></path>
        <path d="m20,15 -5,5" class="s2"></path>
        <path d="M20,10 10,20" class="s2"></path>
        <path d="M20,5 8,17" class="s2"></path>
        <path d="M20,0 7,13" class="s2"></path>
        <path d="M15,0 7,8" class="s2"></path>
        <path d="M10,0 9,1" class="s2"></path>
      </g>''',
    'vmd-3':
    '''      <g id="vmd-3">
        <path d="m0,0 0,20 20,0 C 10,20 7,10 3,0" class="s6"></path>
        <path d="m0,0 3,0 c 4,10 7,20 17,20" class="s1"></path>
        <path d="m0,20 20,0" class="s1"></path>
      </g>''',
    'vmu-3':
    '''      <g id="vmu-3">
        <path d="m0,0 0,20 3,0 C 7,10 10,0 20,0" class="s6"></path>
        <path d="m0,20 3,0 C 7,10 10,0 20,0" class="s1"></path>
        <path d="M0,0 20,0" class="s1"></path>
      </g>''',
    'vmz-3':
    '''      <g id="vmz-3">
        <path d="M0,0 3,0 C 10,10 15,10 20,10 15,10 10,10 3,20 L 0,20" class="s6"></path>
        <path d="m0,0 3,0 c 7,10 12,10 17,10" class="s1"></path>
        <path d="m0,20 3,0 C 10,10 15,10 20,10" class="s1"></path>
      </g>''',
    'vmv-3-3':
    '''      <g id="vmv-3-3">
        <path d="M9,0 20,0 20,20 9,20 6,10 z" class="s6"></path>
        <path d="M3,0 0,0 0,20 3,20 6,10 z" class="s6"></path>
        <path d="m0,0 3,0 6,20 11,0" class="s1"></path>
        <path d="M0,20 3,20 9,0 20,0" class="s1"></path>
      </g>''',
    'vmv-3-4':
    '''      <g id="vmv-3-4">
        <path d="M9,0 20,0 20,20 9,20 6,10 z" class="s7"></path>
        <path d="M3,0 0,0 0,20 3,20 6,10 z" class="s6"></path>
        <path d="m0,0 3,0 6,20 11,0" class="s1"></path>
        <path d="M0,20 3,20 9,0 20,0" class="s1"></path>
      </g>''',
    'vmv-3-5':
    '''      <g id="vmv-3-5">
        <path d="M9,0 20,0 20,20 9,20 6,10 z" class="s8"></path>
        <path d="M3,0 0,0 0,20 3,20 6,10 z" class="s6"></path>
        <path d="m0,0 3,0 6,20 11,0" class="s1"></path>
        <path d="M0,20 3,20 9,0 20,0" class="s1"></path>
      </g>''',
    'vmv-4-3':
    '''      <g id="vmv-4-3">
        <path d="M9,0 20,0 20,20 9,20 6,10 z" class="s6"></path>
        <path d="M3,0 0,0 0,20 3,20 6,10 z" class="s7"></path>
        <path d="m0,0 3,0 6,20 11,0" class="s1"></path>
        <path d="M0,20 3,20 9,0 20,0" class="s1"></path>
      </g>''',
    'vmv-4-4':
    '''      <g id="vmv-4-4">
        <path d="M9,0 20,0 20,20 9,20 6,10 z" class="s7"></path>
        <path d="M3,0 0,0 0,20 3,20 6,10 z" class="s7"></path>
        <path d="m0,0 3,0 6,20 11,0" class="s1"></path>
        <path d="M0,20 3,20 9,0 20,0" class="s1"></path>
      </g>''',
    'vmv-4-5':
    '''      <g id="vmv-4-5">
        <path d="M9,0 20,0 20,20 9,20 6,10 z" class="s8"></path>
        <path d="M3,0 0,0 0,20 3,20 6,10 z" class="s7"></path>
        <path d="m0,0 3,0 6,20 11,0" class="s1"></path>
        <path d="M0,20 3,20 9,0 20,0" class="s1"></path>
      </g>''',
    'vmv-5-3':
    '''      <g id="vmv-5-3">
        <path d="M9,0 20,0 20,20 9,20 6,10 z" class="s6"></path>
        <path d="M3,0 0,0 0,20 3,20 6,10 z" class="s8"></path>
        <path d="m0,0 3,0 6,20 11,0" class="s1"></path>
        <path d="M0,20 3,20 9,0 20,0" class="s1"></path>
      </g>''',
    'vmv-5-4':
    '''      <g id="vmv-5-4">
        <path d="M9,0 20,0 20,20 9,20 6,10 z" class="s7"></path>
        <path d="M3,0 0,0 0,20 3,20 6,10 z" class="s8"></path>
        <path d="m0,0 3,0 6,20 11,0" class="s1"></path>
        <path d="M0,20 3,20 9,0 20,0" class="s1"></path>
      </g>''',
    'vmv-5-5':
    '''      <g id="vmv-5-5">
        <path d="M9,0 20,0 20,20 9,20 6,10 z" class="s8"></path>
        <path d="M3,0 0,0 0,20 3,20 6,10 z" class="s8"></path>
        <path d="m0,0 3,0 6,20 11,0" class="s1"></path>
        <path d="M0,20 3,20 9,0 20,0" class="s1"></path>
      </g>''',
    '0mv-4':
    '''      <g id="0mv-4">
        <path d="M9,0 20,0 20,20 3,20 z" class="s7"></path>
        <path d="M3,20 9,0 20,0" class="s1"></path>
        <path d="m0,20 20,0" class="s1"></path>
      </g>''',
    '1mv-4':
    '''      <g id="1mv-4">
        <path d="M2.875,0 20,0 20,20 9,20 z" class="s7"></path>
        <path d="m3,0 6,20 11,0" class="s1"></path>
        <path d="M0,0 20,0" class="s1"></path>
      </g>''',
    'xmv-4':
    '''      <g id="xmv-4">
        <path d="M9,0 20,0 20,20 9,20 6,10 z" class="s7"></path>
        <path d="M0,20 3,20 9,0 20,0" class="s1"></path>
        <path d="m0,0 3,0 6,20 11,0" class="s1"></path>
        <path d="M0,5 3.5,1.5" class="s2"></path>
        <path d="M0,10 4.5,5.5" class="s2"></path>
        <path d="M0,15 6,9" class="s2"></path>
        <path d="M0,20 4,16" class="s2"></path>
      </g>''',
    'dmv-4':
    '''      <g id="dmv-4">
        <path d="M9,0 20,0 20,20 3,20 z" class="s7"></path>
        <path d="M3,20 9,0 20,0" class="s1"></path>
        <path d="m0,20 20,0" class="s1"></path>
      </g>''',
    'umv-4':
    '''      <g id="umv-4">
        <path d="M3,0 20,0 20,20 9,20 z" class="s7"></path>
        <path d="m3,0 6,20 11,0" class="s1"></path>
        <path d="M0,0 20,0" class="s1"></path>
      </g>''',
    'zmv-4':
    '''      <g id="zmv-4">
        <path d="M9,0 20,0 20,20 9,20 6,10 z" class="s7"></path>
        <path d="m6,10 3,10 11,0" class="s1"></path>
        <path d="M0,10 6,10 9,0 20,0" class="s1"></path>
      </g>''',
    '0mv-5':
    '''      <g id="0mv-5">
        <path d="M9,0 20,0 20,20 3,20 z" class="s8"></path>
        <path d="M3,20 9,0 20,0" class="s1"></path>
        <path d="m0,20 20,0" class="s1"></path>
      </g>''',
    '1mv-5':
    '''      <g id="1mv-5">
        <path d="M2.875,0 20,0 20,20 9,20 z" class="s8"></path>
        <path d="m3,0 6,20 11,0" class="s1"></path>
        <path d="M0,0 20,0" class="s1"></path>
      </g>''',
    'xmv-5':
    '''      <g id="xmv-5">
        <path d="M9,0 20,0 20,20 9,20 6,10 z" class="s8"></path>
        <path d="M0,20 3,20 9,0 20,0" class="s1"></path>
        <path d="m0,0 3,0 6,20 11,0" class="s1"></path>
        <path d="M0,5 3.5,1.5" class="s2"></path>
        <path d="M0,10 4.5,5.5" class="s2"></path>
        <path d="M0,15 6,9" class="s2"></path>
        <path d="M0,20 4,16" class="s2"></path>
      </g>''',
    'dmv-5':
    '''      <g id="dmv-5">
        <path d="M9,0 20,0 20,20 3,20 z" class="s8"></path>
        <path d="M3,20 9,0 20,0" class="s1"></path>
        <path d="m0,20 20,0" class="s1"></path>
      </g>''',
    'umv-5':
    '''      <g id="umv-5">
        <path d="M3,0 20,0 20,20 9,20 z" class="s8"></path>
        <path d="m3,0 6,20 11,0" class="s1"></path>
        <path d="M0,0 20,0" class="s1"></path>
      </g>''',
    'zmv-5':
    '''      <g id="zmv-5">
        <path d="M9,0 20,0 20,20 9,20 6,10 z" class="s8"></path>
        <path d="m6,10 3,10 11,0" class="s1"></path>
        <path d="M0,10 6,10 9,0 20,0" class="s1"></path>
      </g>''',
    'vvv-4':
    '''      <g id="vvv-4">
        <path d="M20,20 0,20 0,0 20,0" class="s7"></path>
        <path d="m0,20 20,0" class="s1"></path>
        <path d="M0,0 20,0" class="s1"></path>
      </g>''',
    'vm0-4':
    '''      <g id="vm0-4">
        <path d="M0,20 0,0 3,0 9,20" class="s7"></path>
        <path d="M0,0 3,0 9,20" class="s1"></path>
        <path d="m0,20 20,0" class="s1"></path>
      </g>''',
    'vm1-4':
    '''      <g id="vm1-4">
        <path d="M0,0 0,20 3,20 9,0" class="s7"></path>
        <path d="M0,0 20,0" class="s1"></path>
        <path d="M0,20 3,20 9,0" class="s1"></path>
      </g>''',
    'vmx-4':
    '''      <g id="vmx-4">
        <path d="M0,0 0,20 3,20 6,10 3,0" class="s7"></path>
        <path d="m0,0 3,0 6,20 11,0" class="s1"></path>
        <path d="M0,20 3,20 9,0 20,0" class="s1"></path>
        <path d="m20,15 -5,5" class="s2"></path>
        <path d="M20,10 10,20" class="s2"></path>
        <path d="M20,5 8,17" class="s2"></path>
        <path d="M20,0 7,13" class="s2"></path>
        <path d="M15,0 7,8" class="s2"></path>
        <path d="M10,0 9,1" class="s2"></path>
      </g>''',
    'vmd-4':
    '''      <g id="vmd-4">
        <path d="m0,0 0,20 20,0 C 10,20 7,10 3,0" class="s7"></path>
        <path d="m0,0 3,0 c 4,10 7,20 17,20" class="s1"></path>
        <path d="m0,20 20,0" class="s1"></path>
      </g>''',
    'vmu-4':
    '''      <g id="vmu-4">
        <path d="m0,0 0,20 3,0 C 7,10 10,0 20,0" class="s7"></path>
        <path d="m0,20 3,0 C 7,10 10,0 20,0" class="s1"></path>
        <path d="M0,0 20,0" class="s1"></path>
      </g>''',
    'vmz-4':
    '''      <g id="vmz-4">
        <path d="M0,0 3,0 C 10,10 15,10 20,10 15,10 10,10 3,20 L 0,20" class="s7"></path>
        <path d="m0,0 3,0 c 7,10 12,10 17,10" class="s1"></path>
        <path d="m0,20 3,0 C 10,10 15,10 20,10" class="s1"></path>
      </g>''',
    'vvv-5':
    '''      <g id="vvv-5">
        <path d="M20,20 0,20 0,0 20,0" class="s8"></path>
        <path d="m0,20 20,0" class="s1"></path>
        <path d="M0,0 20,0" class="s1"></path>
      </g>''',
    'vm0-5':
    '''      <g id="vm0-5">
        <path d="M0,20 0,0 3,0 9,20" class="s8"></path>
        <path d="M0,0 3,0 9,20" class="s1"></path>
        <path d="m0,20 20,0" class="s1"></path>
      </g>''',
    'vm1-5':
    '''      <g id="vm1-5">
        <path d="M0,0 0,20 3,20 9,0" class="s8"></path>
        <path d="M0,0 20,0" class="s1"></path>
        <path d="M0,20 3,20 9,0" class="s1"></path>
      </g>''',
    'vmx-5':
    '''      <g id="vmx-5">
        <path d="M0,0 0,20 3,20 6,10 3,0" class="s8"></path>
        <path d="m0,0 3,0 6,20 11,0" class="s1"></path>
        <path d="M0,20 3,20 9,0 20,0" class="s1"></path>
        <path d="m20,15 -5,5" class="s2"></path>
        <path d="M20,10 10,20" class="s2"></path>
        <path d="M20,5 8,17" class="s2"></path>
        <path d="M20,0 7,13" class="s2"></path>
        <path d="M15,0 7,8" class="s2"></path>
        <path d="M10,0 9,1" class="s2"></path>
      </g>''',
    'vmd-5':
    '''      <g id="vmd-5">
        <path d="m0,0 0,20 20,0 C 10,20 7,10 3,0" class="s8"></path>
        <path d="m0,0 3,0 c 4,10 7,20 17,20" class="s1"></path>
        <path d="m0,20 20,0" class="s1"></path>
      </g>''',
    'vmu-5':
    '''      <g id="vmu-5">
        <path d="m0,0 0,20 3,0 C 7,10 10,0 20,0" class="s8"></path>
        <path d="m0,20 3,0 C 7,10 10,0 20,0" class="s1"></path>
        <path d="M0,0 20,0" class="s1"></path>
      </g>''',
    'vmz-5':
    '''      <g id="vmz-5">
        <path d="M0,0 3,0 C 10,10 15,10 20,10 15,10 10,10 3,20 L 0,20" class="s8"></path>
        <path d="m0,0 3,0 c 7,10 12,10 17,10" class="s1"></path>
        <path d="m0,20 3,0 C 10,10 15,10 20,10" class="s1"></path>
      </g>''',
    'Pclk':
    '''      <g id="Pclk">
        <path d="M-3,12 0,3 3,12 C 1,11 -1,11 -3,12 z" class="s9"></path>
        <path d="M0,20 0,0 20,0" class="s1"></path>
      </g>''',
    'Nclk':
    '''      <g id="Nclk">
        <path d="M-3,8 0,17 3,8 C 1,9 -1,9 -3,8 z" class="s9"></path>
        <path d="m0,0 0,20 20,0" class="s1"></path>
      </g>''',
    'vvv-2':
    '''      <g id="vvv-2">
        <path d="M20,20 0,20 0,0 20,0" class="s10"></path>
        <path d="m0,20 20,0" class="s1"></path>
        <path d="M0,0 20,0" class="s1"></path>
      </g>''',
    'vm0-2':
    '''      <g id="vm0-2">
        <path d="M0,20 0,0 3,0 9,20" class="s10"></path>
        <path d="M0,0 3,0 9,20" class="s1"></path>
        <path d="m0,20 20,0" class="s1"></path>
      </g>''',
    'vm1-2':
    '''      <g id="vm1-2">
        <path d="M0,0 0,20 3,20 9,0" class="s10"></path>
        <path d="M0,0 20,0" class="s1"></path>
        <path d="M0,20 3,20 9,0" class="s1"></path>
      </g>''',
    'vmx-2':
    '''      <g id="vmx-2">
        <path d="M0,0 0,20 3,20 6,10 3,0" class="s10"></path>
        <path d="m0,0 3,0 6,20 11,0" class="s1"></path>
        <path d="M0,20 3,20 9,0 20,0" class="s1"></path>
        <path d="m20,15 -5,5" class="s2"></path>
        <path d="M20,10 10,20" class="s2"></path>
        <path d="M20,5 8,17" class="s2"></path>
        <path d="M20,0 7,13" class="s2"></path>
        <path d="M15,0 7,8" class="s2"></path>
        <path d="M10,0 9,1" class="s2"></path>
      </g>''',
    'vmd-2':
    '''      <g id="vmd-2">
        <path d="m0,0 0,20 20,0 C 10,20 7,10 3,0" class="s10"></path>
        <path d="m0,0 3,0 c 4,10 7,20 17,20" class="s1"></path>
        <path d="m0,20 20,0" class="s1"></path>
      </g>''',
    'vmu-2':
    '''      <g id="vmu-2">
        <path d="m0,0 0,20 3,0 C 7,10 10,0 20,0" class="s10"></path>
        <path d="m0,20 3,0 C 7,10 10,0 20,0" class="s1"></path>
        <path d="M0,0 20,0" class="s1"></path>
      </g>''',
    'vmz-2':
    '''      <g id="vmz-2">
        <path d="M0,0 3,0 C 10,10 15,10 20,10 15,10 10,10 3,20 L 0,20" class="s10"></path>
        <path d="m0,0 3,0 c 7,10 12,10 17,10" class="s1"></path>
        <path d="m0,20 3,0 C 10,10 15,10 20,10" class="s1"></path>
      </g>''',
    '0mv-2':
    '''      <g id="0mv-2">
        <path d="M9,0 20,0 20,20 3,20 z" class="s10"></path>
        <path d="M3,20 9,0 20,0" class="s1"></path>
        <path d="m0,20 20,0" class="s1"></path>
      </g>''',
    '1mv-2':
    '''      <g id="1mv-2">
        <path d="M2.875,0 20,0 20,20 9,20 z" class="s10"></path>
        <path d="m3,0 6,20 11,0" class="s1"></path>
        <path d="M0,0 20,0" class="s1"></path>
      </g>''',
    'xmv-2':
    '''      <g id="xmv-2">
        <path d="M9,0 20,0 20,20 9,20 6,10 z" class="s10"></path>
        <path d="M0,20 3,20 9,0 20,0" class="s1"></path>
        <path d="m0,0 3,0 6,20 11,0" class="s1"></path>
        <path d="M0,5 3.5,1.5" class="s2"></path>
        <path d="M0,10 4.5,5.5" class="s2"></path>
        <path d="M0,15 6,9" class="s2"></path>
        <path d="M0,20 4,16" class="s2"></path>
      </g>''',
    'dmv-2':
    '''      <g id="dmv-2">
        <path d="M9,0 20,0 20,20 3,20 z" class="s10"></path>
        <path d="M3,20 9,0 20,0" class="s1"></path>
        <path d="m0,20 20,0" class="s1"></path>
      </g>''',
    'umv-2':
    '''      <g id="umv-2">
        <path d="M3,0 20,0 20,20 9,20 z" class="s10"></path>
        <path d="m3,0 6,20 11,0" class="s1"></path>
        <path d="M0,0 20,0" class="s1"></path>
      </g>''',
    'zmv-2':
    '''      <g id="zmv-2">
        <path d="M9,0 20,0 20,20 9,20 6,10 z" class="s10"></path>
        <path d="m6,10 3,10 11,0" class="s1"></path>
        <path d="M0,10 6,10 9,0 20,0" class="s1"></path>
      </g>''',
    'vmv-3-2':
    '''      <g id="vmv-3-2">
        <path d="M9,0 20,0 20,20 9,20 6,10 z" class="s10"></path>
        <path d="M3,0 0,0 0,20 3,20 6,10 z" class="s6"></path>
        <path d="m0,0 3,0 6,20 11,0" class="s1"></path>
        <path d="M0,20 3,20 9,0 20,0" class="s1"></path>
      </g>''',
    'vmv-4-2':
    '''      <g id="vmv-4-2">
        <path d="M9,0 20,0 20,20 9,20 6,10 z" class="s10"></path>
        <path d="M3,0 0,0 0,20 3,20 6,10 z" class="s7"></path>
        <path d="m0,0 3,0 6,20 11,0" class="s1"></path>
        <path d="M0,20 3,20 9,0 20,0" class="s1"></path>
      </g>''',
    'vmv-5-2':
    '''      <g id="vmv-5-2">
        <path d="M9,0 20,0 20,20 9,20 6,10 z" class="s10"></path>
        <path d="M3,0 0,0 0,20 3,20 6,10 z" class="s8"></path>
        <path d="m0,0 3,0 6,20 11,0" class="s1"></path>
        <path d="M0,20 3,20 9,0 20,0" class="s1"></path>
      </g>''',
    'vmv-2-3':
    '''      <g id="vmv-2-3">
        <path d="M9,0 20,0 20,20 9,20 6,10 z" class="s6"></path>
        <path d="M3,0 0,0 0,20 3,20 6,10 z" class="s10"></path>
        <path d="m0,0 3,0 6,20 11,0" class="s1"></path>
        <path d="M0,20 3,20 9,0 20,0" class="s1"></path>
      </g>''',
    'vmv-2-4':
    '''      <g id="vmv-2-4">
        <path d="M9,0 20,0 20,20 9,20 6,10 z" class="s7"></path>
        <path d="M3,0 0,0 0,20 3,20 6,10 z" class="s10"></path>
        <path d="m0,0 3,0 6,20 11,0" class="s1"></path>
        <path d="M0,20 3,20 9,0 20,0" class="s1"></path>
      </g>''',
    'vmv-2-5':
    '''      <g id="vmv-2-5">
        <path d="M9,0 20,0 20,20 9,20 6,10 z" class="s8"></path>
        <path d="M3,0 0,0 0,20 3,20 6,10 z" class="s10"></path>
        <path d="m0,0 3,0 6,20 11,0" class="s1"></path>
        <path d="M0,20 3,20 9,0 20,0" class="s1"></path>
      </g>''',
    'vmv-2-2':
    '''      <g id="vmv-2-2">
        <path d="M9,0 20,0 20,20 9,20 6,10 z" class="s10"></path>
        <path d="M3,0 0,0 0,20 3,20 6,10 z" class="s10"></path>
        <path d="m0,0 3,0 6,20 11,0" class="s1"></path>
        <path d="M0,20 3,20 9,0 20,0" class="s1"></path>
      </g>''',
}
