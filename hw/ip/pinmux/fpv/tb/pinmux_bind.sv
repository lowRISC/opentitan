// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

module pinmux_bind;

  bind pinmux pinmux_assert i_pinmux_assert (
    .*
  );

endmodule : pinmux_bind
