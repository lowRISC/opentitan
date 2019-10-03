// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

module padctrl_bind;

  bind padring padring_assert padring_assert (
    // symbolic inputs for FPV
    .mio_sel_i(padctrl_tb.mio_sel_i),
    .dio_sel_i(padctrl_tb.dio_sel_i),
    // normal connections to padring
    .*
  );

endmodule : padctrl_bind
