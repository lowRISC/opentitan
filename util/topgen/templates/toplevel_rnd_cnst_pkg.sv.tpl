// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
${gencmd}
<%
  def make_blocked_sv_literal(hexstr, randwidth):
    """Chop a hex string into blocks of <= 64 digits"""
    # Convert hexstr to an actual number
    num = int(hexstr, 16)
    assert 0 <= num < (1 << randwidth)

    mask = (1 << 256) - 1

    bits_left = randwidth
    acc = []
    while bits_left > 0:
      word = num & mask
      width = min(256, bits_left)

      num_nibbles = (width + 3) // 4
      string = "{word:0{num_nibbles}X}".format(word=word, num_nibbles=num_nibbles)
      # Separate 32-bit words for readability.
      for i in range(num_nibbles-1, 0, -1):
            if (num_nibbles - i) % 8 == 0:
                string = string[:i] + "_" + string[i:]
      acc.append("{nbits}'h{string}"
                 .format(string=string,
                         nbits=width))
      bits_left -= width
      num >>= width

    acc.reverse()
    return acc
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
