// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package push_pull_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // Instantiated in agent's config object.
  typedef enum {
    PushAgent,
    PullAgent
  } push_pull_agent_e;

  // Pull req-ack handshake type.
  typedef enum {
    /*
     * The two-phase handshake follows this protocol:
     *             ____________________
     * req _______/                    \____________
     *                             ____
     * ack _______________________/    \____________
     *
     * Ack asserts for 1 cycle. Req is accepted when both req and ack is true.
     */
    TwoPhase,

    /*
     * The four-phase handshake follows this protocol:
     *             __________________
     * req _______/                  \______________
     *                   _______________________
     * ack _____________/                       \___
     *
     * Req de-asserts after ack asserts. Ack de-asserts after the req
     * de-asserts. This type of handshake is more common in async domains.
     */
    FourPhase
  } pull_handshake_e;

  `include "push_pull_item.sv"
  `include "push_pull_agent_cfg.sv"
  `include "push_pull_agent_cov.sv"
  `include "push_pull_driver_lib.sv"
  `include "push_pull_monitor.sv"
  `include "push_pull_sequencer.sv"
  `include "push_pull_seq_list.sv"
  `include "push_pull_agent.sv"

endpackage : push_pull_agent_pkg
