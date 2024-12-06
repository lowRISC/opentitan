// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module sec_cm_prim_singleton_fifo_bind ();
  // Bind prim_singleton_fifo_if into each instance of prim_fifo_sync. This will have no effect
  // unless the fifo has Depth=1 and Secure=1.
  bind
    prim_fifo_sync
    prim_singleton_fifo_if #(.Depth(Depth), .Secure(Secure)) u_prim_singleton_fifo_if (.*);
endmodule
