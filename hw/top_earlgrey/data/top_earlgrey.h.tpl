// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _TOP_EARLGREY_H_
#define _TOP_EARLGREY_H_

#define PINMUX_PERIPH_INSEL_IDX_OFFSET 2
#define PINMUX_PERIPH_OUTSEL_IDX_OFFSET 2

// PERIPH_INSEL ranges from 0 to NUM_MIO + 2 -1}
//  0 and 1 are tied to value 0 and 1
#define NUM_MIO ${top["pinmux"]["num_mio"]}
#define NUM_DIO ${sum([x["width"] if "width" in x else 1 for x in top["pinmux"]["dio"]])}

<% offset = 0 %>\
% for i, sig in enumerate(top["pinmux"]["inouts"] + top["pinmux"]["inputs"]):
  % if sig["width"] == 1:
#define PINMUX_${sig["name"].upper()}_IN ${offset + i}
  % else:
    % for j in range(sig["width"]):
#define PINMUX_${sig["name"].upper()}_${j}_IN ${offset + i + j}
    % endfor
<% offset += sig["width"] %>\
  % endif
% endfor

## offset starts from 3 as 0, 1, 2 are prefixed value
<% offset = 3 %>\
#define PINMUX_VALUE_0_OUT 0
#define PINMUX_VALUE_1_OUT 1
#define PINMUX_VALUE_Z_OUT 2
% for i, sig in enumerate(top["pinmux"]["inouts"] + top["pinmux"]["outputs"]):
  % if sig["width"] == 1:
#define PINMUX_${sig["width"].upper()}_OUT ${offset + i}
  % else:
    % for j in range(sig["width"]):
#define PINMUX_${sig["name"].upper()}_${j}_OUT ${offset + i + j}
    % endfor
<% offset += sig["width"] %>\
  % endif
% endfor

#endif  // _TOP_EARLGREY_H_
