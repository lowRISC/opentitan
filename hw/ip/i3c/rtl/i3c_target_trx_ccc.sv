// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// NOTE: This is just a sketch of what's required of the CCC handling within
// the Target transceiver logic; it's intended to be explanatory and should be
// regarded as mutable.
// If the ACK/NACK decision logic ends up being sufficiently simple, this submodule
// may be unwarranted.

module i3c_target_trx_ccc
  import i3c_target_pkg::*;
#(
  parameter int unsigned NumTargets = 2
) (
  // Combinational, no need for clock or reset.
  // - internal state could be problematic because of the nature of SCL.

  // Vetting of CCC traffic must be done at two moments, at least:
  // - CCC and optionally DEFB during Broadcast Write or Direct Read.
  //   - a decision is required on whether this CCC/DEFB is understood,
  //     and `i3c_target_trx` can qualify this with whether any VT is enabled
  //     and listening ( => ACK/NACK decision).
  // - After address matching, ACK/NACK
  input                     cmd_phase_i,

  // Prefetched CCC ACK/NACK response and, optionally, read data from the CCC core logic.
  input                     trx_ctvalid_i,
  output                    trx_ctready_o,
  input  i3c_targ_trx_txc_t trx_ctreq_i,

  // Address header, matching has been performed in `i3c_target_trx`
  input       [TargIDW-1:0] targ_id_i,
  input                     group_i,
  input                     rnw_i,
  // .... any additional per-target configuration/state that is required.

  output                    ack_o  // ACK/NACK or a more specific status/error code.
);

endmodule
