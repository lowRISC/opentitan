// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Map latch primitives to a specific cell
module $_DLATCH_P_ (input E, input D, output Q);
DLH_X1 _TECHMAP_REPLACE_ (
.G(E),
.D(D),
.Q(Q)
);
endmodule
