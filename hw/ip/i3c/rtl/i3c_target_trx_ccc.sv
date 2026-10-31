// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// NOTE: This is just a sketch of what's required of the CCC/DEFB vetting within
// the Target transceiver logic; it's intended to be explanatory and should be
// regarded as mutable.
module i3c_target_trx_ccc
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
  input                 cmd_phase_i,

  // Command phase parameters.
  input  i3c_ccc_e      ccc_i,
  input                 has_defb_i,
  input  [7:0]          defb_i,

  // Address header, matching has been performed in `i3c_target_trx`
  input  [TargIDW-1:0]  targ_id_i,
  input                 rnw_i,
  // .... any additional per-target configuration/state that is required.

  output                ack_o  // ACK/NACK or a more specific status/error code.
);

endmodule
