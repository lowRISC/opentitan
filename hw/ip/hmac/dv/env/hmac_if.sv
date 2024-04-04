// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A lightweight interface to sample idle signal.
interface hmac_if(input clk_i, input rst_ni);
  prim_mubi_pkg::mubi4_t idle;

  function automatic bit is_idle();
    return (idle == prim_mubi_pkg::MuBi4True);
  endfunction

endinterface
