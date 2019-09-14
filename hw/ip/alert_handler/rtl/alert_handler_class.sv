// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module gates the alert triggers with their enable bits, and correctly bins
// the enabled alerts into the class that they have been assigned to. The module
// produces the alert cause and class trigger signals.
//

module alert_handler_class (
  input [alert_pkg::NAlerts-1:0]                              alert_trig_i,      // alert trigger
  input [alert_pkg::N_LOC_ALERT-1:0]                          loc_alert_trig_i,  // alert trigger
  input [alert_pkg::NAlerts-1:0]                              alert_en_i,        // alert enable
  input [alert_pkg::N_LOC_ALERT-1:0]                          loc_alert_en_i,    // alert enable
  input [alert_pkg::NAlerts-1:0]    [alert_pkg::CLASS_DW-1:0] alert_class_i,     // class assignment
  input [alert_pkg::N_LOC_ALERT-1:0][alert_pkg::CLASS_DW-1:0] loc_alert_class_i, // class assignment
  input [alert_pkg::N_CLASSES-1:0]                            class_en_i,        // class enables

  output logic [alert_pkg::NAlerts-1:0]                       alert_cause_o,     // alert cause
  output logic [alert_pkg::N_LOC_ALERT-1:0]                   loc_alert_cause_o, // alert cause
  output logic [alert_pkg::N_CLASSES-1:0]                     class_trig_o       // class triggered
);

  // assign alert cause
  assign alert_cause_o     = alert_en_i     & alert_trig_i;
  assign loc_alert_cause_o = loc_alert_en_i & loc_alert_trig_i;

  // classification mapping
  logic [alert_pkg::N_CLASSES-1:0][alert_pkg::NAlerts-1:0]     class_masks;
  logic [alert_pkg::N_CLASSES-1:0][alert_pkg::N_LOC_ALERT-1:0] loc_class_masks;

  // this is basically an address to onehot0 decoder
  always_comb begin : p_class_mask
    class_masks = '0;
    loc_class_masks = '0;
    for (int unsigned kk = 0; kk < alert_pkg::NAlerts; kk++) begin
      class_masks[alert_class_i[kk]][kk] = 1'b1;
    end
    for (int unsigned kk = 0; kk < alert_pkg::N_LOC_ALERT; kk++) begin
      loc_class_masks[loc_alert_class_i[kk]][kk] = 1'b1;
    end
  end

  // mask and OR reduction, followed by class enable gating
  for (genvar k = 0; k < alert_pkg::N_CLASSES; k++) begin : gen_classifier
    assign class_trig_o[k] = class_en_i[k]         &
                             (|{ alert_cause_o     & class_masks[k],
                                 loc_alert_cause_o & loc_class_masks[k] });
  end

endmodule : alert_handler_class
