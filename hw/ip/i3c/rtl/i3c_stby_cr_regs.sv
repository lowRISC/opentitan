// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Implementation of a number of Standby Controller-related registers that exhibit special behavior,
// e.g. those that demand conditional writing.
// - these cannot be implemented directly using the OpenTitan tooling and thus require custom logic.

// Note: Since the current implementation of the IP block does not include Standby Controller
// support, these registers are not actually required.

module i3c_stby_cr_regs
  import i3c_consts_pkg::*;
  import i3c_reg_pkg::*;
(
  input               clk_i,
  input               rst_ni,

  // Software register access.
  input  i3c_reg2hw_t reg2hw_i,
  // Currently the Active Controller?
  input               ac_current_own_i,
  // Software writes to the `CONTROLLER_DEVICE_ADDR` register.
  input               ctrladdr_qe_i,
  input         [7:0] ctrladdr_q_i,
  // Setting the Standby Controller Dynamic Address.
  input               stby_cr_dynaddr_de_i,
  input         [7:0] stby_cr_dynaddr_d_i,
  // Setting the RSTACT.
  input               rstact_de_i,
  input i3c_rstact_e  rstact_d_i,

  // Register state.
  output i3c_hw2reg_stby_cr_control_reg_t                   stby_cr_control_o,
  output i3c_hw2reg_stby_cr_device_addr_reg_t               stby_cr_device_addr_o,
  output i3c_hw2reg_stby_cr_device_char_reg_t               stby_cr_device_char_o,
  output i3c_hw2reg_stby_cr_device_pid_lo_reg_t             stby_cr_device_pid_lo_o,
  output i3c_hw2reg_stby_cr_ccc_config_getcaps_reg_t        stby_cr_config_getcaps_o,
  output i3c_hw2reg_stby_cr_ccc_config_rstact_params_reg_t  stby_cr_config_rstact_o
);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      // Fields within STBY_CR_CONTROL.
      stby_cr_control_o.stby_cr_enable_init.d   <= I3C_STBY_CR_CONTROL_STBY_CR_ENABLE_INIT_RESVAL;
      stby_cr_control_o.rstact_defbyte_02.d     <= I3C_STBY_CR_CONTROL_RSTACT_DEFBYTE_02_RESVAL;
      stby_cr_control_o.daa_entdaa_enable.d     <= I3C_STBY_CR_CONTROL_DAA_ENTDAA_ENABLE_RESVAL;
      stby_cr_control_o.daa_setdasa_enable.d    <= I3C_STBY_CR_CONTROL_DAA_SETDASA_ENABLE_RESVAL;
      stby_cr_control_o.daa_setaasa_enable.d    <= I3C_STBY_CR_CONTROL_DAA_SETAASA_ENABLE_RESVAL;
      stby_cr_control_o.target_xact_enable.d    <= I3C_STBY_CR_CONTROL_TARGET_XACT_ENABLE_RESVAL;
      stby_cr_control_o.bcast_ccc_ibi_ring.d    <= I3C_STBY_CR_CONTROL_BCAST_CCC_IBI_RING_RESVAL;
      stby_cr_control_o.cr_request_send.d       <= I3C_STBY_CR_CONTROL_CR_REQUEST_SEND_RESVAL;
      stby_cr_control_o.handoff_deep_sleep.d    <= I3C_STBY_CR_CONTROL_HANDOFF_DEEP_SLEEP_RESVAL;
      stby_cr_control_o.prime_accept_getacccr.d <= I3C_STBY_CR_CONTROL_PRIME_ACCEPT_GETACCCR_RESVAL;
      stby_cr_control_o.acr_fsm_op_select.d     <= I3C_STBY_CR_CONTROL_ACR_FSM_OP_SELECT_RESVAL;
      stby_cr_control_o.handoff_delay_nack.d    <= I3C_STBY_CR_CONTROL_HANDOFF_DELAY_NACK_RESVAL;
      stby_cr_control_o.pending_rx_nack.d       <= I3C_STBY_CR_CONTROL_PENDING_RX_NACK_RESVAL;

      // Fields within STBY_CR_DEVICE_ADDR.
      stby_cr_device_addr_o.dynamic_addr_valid.d <=
        I3C_STBY_CR_DEVICE_ADDR_DYNAMIC_ADDR_VALID_RESVAL;
      stby_cr_device_addr_o.dynamic_addr.d       <= I3C_STBY_CR_DEVICE_ADDR_DYNAMIC_ADDR_RESVAL;
      stby_cr_device_addr_o.static_addr_valid.d  <=
        I3C_STBY_CR_DEVICE_ADDR_STATIC_ADDR_VALID_RESVAL;
      stby_cr_device_addr_o.static_addr.d        <= I3C_STBY_CR_DEVICE_ADDR_STATIC_ADDR_RESVAL;

      // Fields within STBY_CR_DEVICE_CHAR.
      stby_cr_device_char_o.bcr_fixed.d <= I3C_STBY_CR_DEVICE_CHAR_BCR_FIXED_RESVAL;
      stby_cr_device_char_o.bcr_var.d   <= I3C_STBY_CR_DEVICE_CHAR_BCR_VAR_RESVAL;
      stby_cr_device_char_o.dcr.d       <= I3C_STBY_CR_DEVICE_CHAR_DCR_RESVAL;
      stby_cr_device_char_o.pid_hi.d    <= I3C_STBY_CR_DEVICE_CHAR_PID_HI_RESVAL;

      // STBY_CR_DEVICE_PID_LO.
      stby_cr_device_pid_lo_o.d <= I3C_STBY_CR_DEVICE_PID_LO_PID_LO_RESVAL;

      // STBY_CR_CCC_CONFIG_GETCAPS
      stby_cr_config_getcaps_o.f2_crcap2_dev_interact.d <=
        I3C_STBY_CR_CCC_CONFIG_GETCAPS_F2_CRCAP2_DEV_INTERACT_RESVAL;
      stby_cr_config_getcaps_o.f2_crcap1_bus_config.d   <=
        I3C_STBY_CR_CCC_CONFIG_GETCAPS_F2_CRCAP1_BUS_CONFIG_RESVAL;

      // STBY_CR_CCC_CONFIG_RSTACT_PARAMS
      stby_cr_config_rstact_o.reset_dynamic_addr.d    <=
        I3C_STBY_CR_CCC_CONFIG_RSTACT_PARAMS_RESET_DYNAMIC_ADDR_RESVAL;
      stby_cr_config_rstact_o.reset_time_target.d     <=
        I3C_STBY_CR_CCC_CONFIG_RSTACT_PARAMS_RESET_TIME_TARGET_RESVAL;
      stby_cr_config_rstact_o.reset_time_peripheral.d <=
        I3C_STBY_CR_CCC_CONFIG_RSTACT_PARAMS_RESET_TIME_PERIPHERAL_RESVAL;
      stby_cr_config_rstact_o.rst_action.d            <=
        I3C_STBY_CR_CCC_CONFIG_RSTACT_PARAMS_RST_ACTION_RESVAL;
    end else begin
      // Note that because we're using the `hw2reg` structures and implementing `hwext` registers,
      // the stored state (for reading) is unfortunately in the `d` fields, and the `q` fields of
      // the corresponding `reg2hw` structures convey the new write data from the software.
      //
      // Hence the potentially-confusing `hw2reg.d <= reg2hw.q` assignments.
      //
      // Also note that a number of registers fields are here only because they share a register
      // with a special field, and a register cannot by partially `hwext` with current tooling.

      // ----- STBY_CR_CONTROL register (Table 119) -----
      if (reg2hw_i.stby_cr_control.stby_cr_enable_init.qe) begin
        stby_cr_control_o.stby_cr_enable_init.d <= reg2hw_i.stby_cr_control.stby_cr_enable_init.q;
      end
      if (reg2hw_i.stby_cr_control.rstact_defbyte_02.qe) begin
        stby_cr_control_o.rstact_defbyte_02.d <= reg2hw_i.stby_cr_control.rstact_defbyte_02.q;
      end
      // The next 3 bits are specified as R/cW; we opt to support all address assignment methods.
      if (reg2hw_i.stby_cr_control.daa_entdaa_enable.qe) begin
        stby_cr_control_o.daa_entdaa_enable.d <= reg2hw_i.stby_cr_control.daa_entdaa_enable.q;
      end
      if (reg2hw_i.stby_cr_control.daa_setdasa_enable.qe) begin
        stby_cr_control_o.daa_setdasa_enable.d <= reg2hw_i.stby_cr_control.daa_setdasa_enable.q;
      end
      if (reg2hw_i.stby_cr_control.daa_setaasa_enable.qe) begin
        stby_cr_control_o.daa_setaasa_enable.d <= reg2hw_i.stby_cr_control.daa_setaasa_enable.q;
      end
      if (reg2hw_i.stby_cr_control.bcast_ccc_ibi_ring.qe) begin
        stby_cr_control_o.bcast_ccc_ibi_ring.d <= reg2hw_i.stby_cr_control.bcast_ccc_ibi_ring.q;
      end
      if (reg2hw_i.stby_cr_control.cr_request_send.qe) begin
        stby_cr_control_o.cr_request_send.d <= reg2hw_i.stby_cr_control.cr_request_send.q;
      end
      // HANDOFF_DEEP_SLEEP is 'sticky' and cannot be cleared by software.
      // - since we presently do not support Controller Role Handoff, there is no clearing logic.
      if (reg2hw_i.stby_cr_control.handoff_deep_sleep.qe) begin
        stby_cr_control_o.handoff_deep_sleep.d <= reg2hw_i.stby_cr_control.handoff_deep_sleep.q |
                                                  stby_cr_control_o.handoff_deep_sleep.d;
      end
      if (reg2hw_i.stby_cr_control.prime_accept_getacccr.qe) begin
        stby_cr_control_o.prime_accept_getacccr.d <=
          reg2hw_i.stby_cr_control.prime_accept_getacccr.q;
      end
      if (reg2hw_i.stby_cr_control.acr_fsm_op_select.qe) begin
        stby_cr_control_o.acr_fsm_op_select.d <= reg2hw_i.stby_cr_control.acr_fsm_op_select.q;
      end
      if (reg2hw_i.stby_cr_control.handoff_delay_nack.qe &
          reg2hw_i.stby_cr_control.handoff_delay_nack.q) begin
        stby_cr_control_o.handoff_delay_nack.d <= 1'b0;  // R/W1C, with no hw write presently.
      end
      if (reg2hw_i.stby_cr_control.pending_rx_nack.qe &
          reg2hw_i.stby_cr_control.pending_rx_nack.q) begin
        stby_cr_control_o.pending_rx_nack.d <= 1'b0; // R/W1C, with no hw write presently.
      end

      // ----- STBY_CR_DEVICE_ADDR register (Table 120) -----
      // Dynamic address configuration depends upon the mode, see below.
      if (ac_current_own_i) begin
        // Software may supply a Dynamic Address whilst the Controller is still Active, as part of
        // the Controller Role Handoff.
        if (ctrladdr_qe_i) begin
          stby_cr_device_addr_o.dynamic_addr_valid.d <= ctrladdr_q_i[7];
          stby_cr_device_addr_o.dynamic_addr.d <= ctrladdr_q_i[6:0];
        end
      end else if (stby_cr_dynaddr_de_i) begin
        // The Target-side logic can receive a new Dynamic Address from the Active Controller.
        stby_cr_device_addr_o.dynamic_addr_valid.d <= stby_cr_dynaddr_d_i[7];
        stby_cr_device_addr_o.dynamic_addr.d <= stby_cr_dynaddr_d_i[6:0];
      end

      // ----- STBY_CR_DEVICE_CHAR register (Table 123) -----
      if (reg2hw_i.stby_cr_device_char.bcr_fixed.qe) begin
        stby_cr_device_char_o.bcr_fixed.d <= reg2hw_i.stby_cr_device_char.bcr_fixed.q;
      end

      // ----- STBY_CR_CCC_CONFIG_RSTACT_PARAMS register (Table 129) -----
      // - RO to software, written by hardware when RSTACT CCC accepted.
      if (rstact_de_i) stby_cr_config_rstact_o.rst_action.d <= rstact_d_i;

      // The remaining configuration may only be changed whilst the Standby Controller is disabled.
      if (~|stby_cr_control_o.stby_cr_enable_init.d) begin
        // ----- STBY_CR_CONTROL register (Table 119) -----
        if (reg2hw_i.stby_cr_control.target_xact_enable.qe) begin
          stby_cr_control_o.target_xact_enable.d <= reg2hw_i.stby_cr_control.target_xact_enable.q;
        end

        // ----- STBY_CR_DEVICE_ADDR register (Table 120) -----
        if (reg2hw_i.stby_cr_device_addr.static_addr_valid.qe) begin
          stby_cr_device_addr_o.static_addr_valid.d <=
            reg2hw_i.stby_cr_device_addr.static_addr_valid.q;
        end
        if (reg2hw_i.stby_cr_device_addr.static_addr.qe) begin
          stby_cr_device_addr_o.static_addr.d <= reg2hw_i.stby_cr_device_addr.static_addr.q;
        end

        // ----- STBY_CR_DEVICE_CHAR register (Table 123) -----
        // - BCR_FIXED is read only.
        if (reg2hw_i.stby_cr_device_char.bcr_var.qe) begin
          stby_cr_device_char_o.bcr_var.d <= reg2hw_i.stby_cr_device_char.bcr_var.q;
        end
        if (reg2hw_i.stby_cr_device_char.dcr.qe) begin
          stby_cr_device_char_o.dcr.d <= reg2hw_i.stby_cr_device_char.dcr.q;
        end
        if (reg2hw_i.stby_cr_device_char.pid_hi.qe) begin
          stby_cr_device_char_o.pid_hi.d <= reg2hw_i.stby_cr_device_char.pid_hi.q;
        end

        // ----- STBY_CR_DEVICE_PID_LO register (Table 124) -----
        if (reg2hw_i.stby_cr_device_pid_lo.qe) begin
          stby_cr_device_pid_lo_o.d <= reg2hw_i.stby_cr_device_pid_lo.q;
        end

        // ----- STBY_CR_CCC_CONFIG_GETCAPS register (Table 128) -----
        if (reg2hw_i.stby_cr_ccc_config_getcaps.f2_crcap2_dev_interact.qe) begin
          stby_cr_config_getcaps_o.f2_crcap2_dev_interact.d  <=
            reg2hw_i.stby_cr_ccc_config_getcaps.f2_crcap2_dev_interact.q;
        end
        if (reg2hw_i.stby_cr_ccc_config_getcaps.f2_crcap1_bus_config.qe) begin
          stby_cr_config_getcaps_o.f2_crcap1_bus_config.d <=
            reg2hw_i.stby_cr_ccc_config_getcaps.f2_crcap1_bus_config.q;
        end

        // ----- STBY_CR_CCC_CONFIG_RSTACT_PARAMS register (Table 129) -----
        if (reg2hw_i.stby_cr_ccc_config_rstact_params.reset_dynamic_addr.qe) begin
          stby_cr_config_rstact_o.reset_dynamic_addr.d <=
            reg2hw_i.stby_cr_ccc_config_rstact_params.reset_dynamic_addr.q;
        end
        if (reg2hw_i.stby_cr_ccc_config_rstact_params.reset_time_target.qe) begin
          stby_cr_config_rstact_o.reset_time_target.d <=
            reg2hw_i.stby_cr_ccc_config_rstact_params.reset_time_target.q;
        end
        if (reg2hw_i.stby_cr_ccc_config_rstact_params.reset_time_peripheral.qe) begin
          stby_cr_config_rstact_o.reset_time_peripheral.d <=
            reg2hw_i.stby_cr_ccc_config_rstact_params.reset_time_peripheral.q;
        end
      end
    end
  end

endmodule
