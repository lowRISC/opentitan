// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// rv_core_ibex_peri package
//

package rv_core_ibex_peri_pkg;

  typedef enum logic [1:0] {
    EventOn = 2'b10,
    EventOff = 2'b01
  } alert_event_e;

  typedef alert_event_e alert_event_t;

endpackage // rv_core_ibex_peri_pkg
