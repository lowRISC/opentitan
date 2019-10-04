// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

module pinmux_bind;

  bind pinmux pinmux_assert i_pinmux_assert (
    // symbolic inputs for FPV
    .periph_sel_i(pinmux_tb.periph_sel_i),
    .mio_sel_i(pinmux_tb.mio_sel_i),
    // normal inputs
    .*
  );

endmodule : pinmux_bind
