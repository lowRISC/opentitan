// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// I3C Controller global state.
//
// - Handles the transitions between the global states of the Host Controller:
//   Disabled/Enabled, Suspend/Resume, Halted, Abort.
// - These transitions may be initiated by software writes to HC_CONTROL or in response to
//   hardware-detected events on the I3C bus.
// - The general approach is that when transitioning between stable states the requested/intended
//   transition is indicated to the core FSM logic using a '<x>ing' state and it will indicate when
//   it has actioned that request.
// - The `suspending_i` signal is the exception, being a simple notification issued by the FSM.

module i3c_controller_state
  import i3c_controller_pkg::*;
  import i3c_reg_pkg::*;
(
  input                     clk_i,
  input                     rst_ni,

  // Control inputs.
  input                     sw_reset_i,

  // Configuration settings; software-initiated state changes.
  input  i3c_reg2hw_t       reg2hw_i,

  // Indication that the Controller logic has become inactive and may be gated off.
  input                     inactive_i,
  // Command processing suspending due to an error?
  // - this is a notification from the FSM, it receives no response.
  input                     suspending_i,
  // Status signal indicating that the Controller logic has aborted.
  input                     aborted_i,

  // Current global state.
  output i3c_ctrl_gstate_e  gstate_o,

  // Global enabled/disabled signal used for clock-gating all Controller-side logic.
  output                    enabled_o,

  // Register state.
  output hc_control_t hc_control_o
);

  // Control inputs from the driver; single-cycle assertions causing state changes.
  wire enable_now  = reg2hw_i.hc_control.bus_enable.qe &  reg2hw_i.hc_control.bus_enable.q;
  wire disable_now = reg2hw_i.hc_control.bus_enable.qe & !reg2hw_i.hc_control.bus_enable.q;
  wire resume_now  = reg2hw_i.hc_control.resume.qe     &  reg2hw_i.hc_control.resume.q;
  wire abort_now   = reg2hw_i.hc_control.abort.qe      &  reg2hw_i.hc_control.abort.q;
  wire abort_clr   = reg2hw_i.hc_control.abort.qe      & !reg2hw_i.hc_control.abort.q;

  // Global state of the Host Controller.
  i3c_ctrl_gstate_e gstate_q, gstate_d;
  always_comb begin
    // Disabling takes precedence over all else; note that we must still transition via `Disabling`
    // rather than jumping straight to the `Disabled` in case the FSM needs to stop any I3C traffic
    // cleanly and avoid bus errors.
    if (disable_now) gstate_d = GState_Disabling;
    else begin
      gstate_d = gstate_q;
      case (gstate_q)
        GState_Disabled:  if (enable_now)        gstate_d = GState_Running;
        GState_Disabling: if (inactive_i)        gstate_d = GState_Disabled;
        GState_Aborted:   if (abort_clr)         gstate_d = GState_Running;
        // We shall wait for the FSM to indicate that an Abort request has been actioned because
        // some actions may need to be taken first (HCI 6.5.6).
        // - Abort requests cannot be retracted (HCI 6.8.4).
        // - `suspending_i` is ignored, FSM shall proceed to handle the Abort request.
        GState_Aborting:  if (aborted_i)         gstate_d = GState_Aborted;
        // Abort requests take precedence over Resume requests; they could be issued simultaneously.
        GState_Running:   if (abort_now)         gstate_d = GState_Aborting;
                          else if (suspending_i) gstate_d = GState_Suspended;
        // We transition straight to `Running` and the FSM spots that it and proceeds some time
        // later when its other conditions are met, such as Command Descriptor and Data
        // availability.
        GState_Suspended: if (abort_now)         gstate_d = GState_Aborting;
                          else if (resume_now)   gstate_d = GState_Running;
        // Covers any invalid states.
        default: gstate_d = GState_Disabling;
      endcase
    end
  end

  // Handling of HC_CONTROL fields:
  // - BUS_ENABLE, RESUME, SUSPEND, ABORT
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) gstate_q <= GState_Disabled;
    else if (sw_reset_i) gstate_q <= GState_Disabled;  // Software reset shall be a last resort.
    else if (enabled_o || enable_now) begin
      gstate_q  <= gstate_d;
    end
  end

  // Implementation of the HC_CONTROL register
  // - the tooling does not allow us to implement just some register fields externally; these
  //   fields are just conventional R/W register bits under software control.
  logic halt_on_cmd_seq_timeout;
  logic hot_join_ctrl;
  logic i2c_dev_present;
  logic autocmd_data_rpt;
  logic iba_include;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      halt_on_cmd_seq_timeout <= I3C_HC_CONTROL_HALT_ON_CMD_SEQ_TIMEOUT_RESVAL;
      hot_join_ctrl           <= I3C_HC_CONTROL_HOT_JOIN_CTRL_RESVAL;
      i2c_dev_present         <= I3C_HC_CONTROL_I2C_DEV_PRESENT_RESVAL;
      autocmd_data_rpt        <= I3C_HC_CONTROL_AUTOCMD_DATA_RPT_RESVAL;
      iba_include             <= I3C_HC_CONTROL_IBA_INCLUDE_RESVAL;
    end else if (sw_reset_i) begin
      halt_on_cmd_seq_timeout <= I3C_HC_CONTROL_HALT_ON_CMD_SEQ_TIMEOUT_RESVAL;
      hot_join_ctrl           <= I3C_HC_CONTROL_HOT_JOIN_CTRL_RESVAL;
      i2c_dev_present         <= I3C_HC_CONTROL_I2C_DEV_PRESENT_RESVAL;
      autocmd_data_rpt        <= I3C_HC_CONTROL_AUTOCMD_DATA_RPT_RESVAL;
      iba_include             <= I3C_HC_CONTROL_IBA_INCLUDE_RESVAL;
    end else begin
      if (reg2hw_i.hc_control.halt_on_cmd_seq_timeout.qe) begin
        halt_on_cmd_seq_timeout <= reg2hw_i.hc_control.halt_on_cmd_seq_timeout.q;
      end
      if (reg2hw_i.hc_control.hot_join_ctrl.qe) begin
        hot_join_ctrl <= reg2hw_i.hc_control.hot_join_ctrl.q;
      end
      if (reg2hw_i.hc_control.i2c_dev_present.qe) begin
        i2c_dev_present <= reg2hw_i.hc_control.i2c_dev_present.q;
      end
      if (reg2hw_i.hc_control.autocmd_data_rpt.qe) begin
        autocmd_data_rpt <= reg2hw_i.hc_control.autocmd_data_rpt.q;
      end
      if (reg2hw_i.hc_control.iba_include.qe) iba_include <= reg2hw_i.hc_control.iba_include.q;
    end
  end

  // Register state presented to the driver.
  always_comb begin
    hc_control_o = '0;
    // Control bits that reflect the current state and not the requested transition.
    hc_control_o.bus_enable.d = (gstate_q != GState_Disabled);
    hc_control_o.resume.d     = (gstate_q == GState_Suspended);  // RESUME == '1' means `Suspended`.
    hc_control_o.abort.d      = (gstate_q inside {GState_Aborting, GState_Aborted});
    // Simple R/W bits under software control.
    hc_control_o.halt_on_cmd_seq_timeout.d = halt_on_cmd_seq_timeout;
    hc_control_o.hot_join_ctrl.d           = hot_join_ctrl;
    hc_control_o.i2c_dev_present.d         = i2c_dev_present;
    hc_control_o.autocmd_data_rpt.d        = autocmd_data_rpt;
    hc_control_o.iba_include.d             = iba_include;
    // Read Only bits.
    hc_control_o.mode_selector.d        = I3C_HC_CONTROL_MODE_SELECTOR_RESVAL;
    hc_control_o.data_byte_order_mode.d = I3C_HC_CONTROL_DATA_BYTE_ORDER_MODE_RESVAL;
  end

  // Controller-global enable signal for clock-gating Controller-side logic.
  assign enabled_o = (gstate_q != GState_Disabled);

  // Present the global state to the FSM; the '<x>ing' states are particularly important in
  // signaling intent, e.g. to Abort command processing or to Resume from the `Suspended` state.
  assign gstate_o = gstate_q;

endmodule
