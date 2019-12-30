# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Svg data for I2C display

# constants in svg tag
svgtag_consts = """
   xmlns="http://www.w3.org/2000/svg"
   xmlns:xlink="http://www.w3.org/1999/xlink"
   overflow="hidden"
"""

# styles
svgstyle = """
    <style type="text/css">
      text { font-size: 11pt; font-style: normal; font-variant:
      normal; font-weight: bold; font-stretch: normal;
      text-align: center; text-anchor: middle; fill-opacity: 1; font-family:
      Helvetica }

      .tt {
      text-anchor: start; font-weight: normal; font-size: 10pt;
      font-family: monospace
      }

      .shost {
      fill: none;
      stroke: #000;
      stroke-width: 1;
      stroke-linecap: round;
      stroke-linejoin: miter;
      stroke-miterlimit: 4;
      stroke-opacity: 1;
      stroke-dasharray: none
      }

      .dash {
      fill: none;
      stroke: #000;
      stroke-width: 1;
      stroke-linecap: butt;
      stroke-linejoin: miter;
      stroke-miterlimit: 4;
      stroke-opacity: 1;
      stroke-dasharray: 8;
      }

      .sdev {
      fill: #CCC;
      stroke: #000;
      stroke-width: 1;
      stroke-linecap: round;
      stroke-linejoin: miter;
      stroke-miterlimit: 4;
      stroke-opacity: 1;
      stroke-dasharray: none
      }


    </style>
"""

# width of the svg
svgw = 1000

# svg defs are made with a bit-box 20,40 so set constants based on that
bitw = 20
bith = 40
bytew = 160

# text is offset from the top of a bit
txty = 25

# formatting:
wrap = 880  # the wrap point for long transactions
cindent = 60  # the indentation for continuation lines
linesep = 50  # separation between lines

svg_defs = """
    <defs>
      <g id="start">
        <path d="M0,0 h 20 m0,40 h -20 v -40" class="shost" />
        <text x="10" y="25">S</text>
      </g>
      <g id="pstop">
        <path d="M0,0 h 20 v 40 h -20 M0,0" class="shost" />
        <text x="10" y="25">P</text>
      </g>
      <g id="ackh">
        <path d="M0,0 h 20 v 40 h -20 v -40" class="shost" />
        <text x="10" y="25">A</text>
      </g>
      <g id="ackd">
        <path d="M0,0 h 20 v 40 h -20 v -40" class="sdev" />
        <text x="10" y="25">A</text>
      </g>
      <g id="nackh">
        <path d="M0,0 h 20 v 40 h -20 v -40" class="shost" />
        <text x="10" y="25">N</text>
      </g>
      <g id="nackd">
        <path d="M0,0 h 20 v 40 h -20 v -40" class="sdev" />
        <text x="10" y="25">N</text>
      </g>
      <g id="norackd">
        <path d="M0,0 h 20 v 40 h -20 v -40" class="sdev" />
        <text x="5" y="15">A/</text>
        <text x="15" y="35">N</text>
      </g>
      <g id="skip">
        <path d="M0,0 h 8 l-5,30 l5,-10 l-5,20 h -3 v -40" class="shost" />
        <path d="M17,0 h 3 v 40 h -8 l5,-30 l-5,10 l5,-20" class="shost" />
      </g>
      <g id="hbyte">
        <path d="M0,0 h 160 m0,40 h -160 v -40" class="shost" />
      </g>
      <g id="dbyte">
        <path d="M0,0 h 160 v 40 h -160 v -40" class="sdev" />
      </g>
      <g id="adr0">
        <path d="M0,0 h 160 m0,40 h -160 v -40" class="shost" />
        <path d="M140,0 v 40" class="dash" />
        <text x="80" y="25">Adr</text>
        <text x="150" y="25">wr</text>
      </g>
      <g id="adr1">
        <path d="M0,0 h 160 m0,40 h -160 v -40" class="shost" />
        <path d="M140,0 v 40" class="dash" />
        <text x="80" y="25">Adr</text>
        <text x="150" y="25">rd</text>
      </g>
      <g id="adr2">
        <path d="M0,0 h 160 m0,40 h -160 v -40" class="shost" />
        <path d="M140,0 v 40" class="dash" />
        <text x="80" y="25">Adr</text>
        <text x="150" y="25">d</text>
      </g>

    </defs>
"""
