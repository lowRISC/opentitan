// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

module padctrl_bind;

  bind padring padring_assert padring_assert (
    .*
  );

  bind padctrl padctrl_assert #(
    .Impl(Impl)
  ) padctrl_assert (
    .*
  );

endmodule : padctrl_bind
