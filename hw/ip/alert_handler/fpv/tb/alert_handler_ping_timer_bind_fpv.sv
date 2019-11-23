// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

module alert_handler_ping_timer_bind_fpv;

  bind alert_handler_ping_timer
        alert_handler_ping_timer_assert_fpv alert_handler_ping_timer_assert_fpv (
    .*
  );

endmodule : alert_handler_ping_timer_bind_fpv
