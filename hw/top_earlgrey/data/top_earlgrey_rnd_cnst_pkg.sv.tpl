// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
${gencmd}
<%
  def make_blocked_sv_literal(hexstr, randwidth):
    """This chops the random hexstring into manageable blocks of 64 chars such that the
    lines do not get too long.
    """
    # Make all-caps and drop '0x' preamble
    hexstr = str(hexstr[2:]).upper()
    # Block width in hex chars
    blockwidth = 64
    remainder = randwidth % (4*blockwidth)
    numbits = remainder if remainder else 4*blockwidth
    idx = 0
    hexblocks = []
    while randwidth > 0:
      hexstr = hexstr[idx:]
      randwidth -= numbits
      idx = (numbits + 3) // 4
      hexblocks.append(str(numbits) + "'h" + hexstr[0:idx])
      numbits = 4*blockwidth
    return hexblocks
%>
package top_${top["name"]}_rnd_cnst_pkg;

% for m in top["module"]:
  % for p in filter(lambda p: p.get("randtype") in ["data", "perm"], m["param_list"]):
    % if loop.first:
  ////////////////////////////////////////////
  // ${m['name']}
  ////////////////////////////////////////////
    % endif
  // ${p['desc']}
  parameter ${p["type"]} ${p["name_top"]} = {
    % for block in make_blocked_sv_literal(p["default"], p["randwidth"]):
    ${block}${"" if loop.last else ","}
    % endfor
  };

  % endfor
% endfor
endpackage : top_${top["name"]}_rnd_cnst_pkg
