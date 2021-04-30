// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class lc_ctrl_scoreboard extends cip_base_scoreboard #(
    .CFG_T(lc_ctrl_env_cfg),
    .RAL_T(lc_ctrl_reg_block),
    .COV_T(lc_ctrl_env_cov)
  );
  `uvm_component_utils(lc_ctrl_scoreboard)

  // local variables
  bit is_personalized = 0;

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(push_pull_item#(.HostDataWidth(OTP_PROG_HDATA_WIDTH),
                        .DeviceDataWidth(OTP_PROG_DDATA_WIDTH))) otp_prog_fifo;
  uvm_tlm_analysis_fifo #(push_pull_item#(.HostDataWidth(lc_ctrl_state_pkg::LcTokenWidth)))
                        otp_token_fifo;
  uvm_tlm_analysis_fifo #(alert_esc_seq_item) esc_wipe_secrets_fifo;
  uvm_tlm_analysis_fifo #(alert_esc_seq_item) esc_scrap_state_fifo;

  // local queues to hold incoming packets pending comparison

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    otp_prog_fifo = new("otp_prog_fifo", this);
    otp_token_fifo = new("otp_token_fifo", this);
    esc_wipe_secrets_fifo = new("esc_wipe_secrets_fifo", this);
    esc_scrap_state_fifo = new("esc_scrap_state_fifo", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      check_lc_output();
      process_otp_prog_rsp();
      process_otp_token_rsp();
    join_none
  endtask

  virtual task check_lc_output();
    forever begin
      @(posedge cfg.pwr_lc_vif.pins[LcPwrDoneRsp] && cfg.en_scb) begin
        // TODO: add coverage
        dec_lc_state_e lc_state = dec_lc_state(cfg.lc_ctrl_vif.otp_i.state);
        lc_outputs_t   exp_lc_o = EXP_LC_OUTPUTS[int'(lc_state)];
        string         err_msg  = $sformatf("LC_St %0s", lc_state.name);
        cfg.clk_rst_vif.wait_n_clks(1);

        // lc_creator_seed_sw_rw_en_o is ON only when device has NOT been personalized or RMA state
        if (is_personalized && lc_state != DecLcStRma) begin
          exp_lc_o.lc_creator_seed_sw_rw_en_o = lc_ctrl_pkg::Off;
        end
        // lc_seed_hw_rd_en_o is ON only when device has been personalized or RMA state
        if (!is_personalized && lc_state != DecLcStRma) begin
          exp_lc_o.lc_seed_hw_rd_en_o = lc_ctrl_pkg::Off;
        end

        check_lc_outputs(exp_lc_o, err_msg);

        // predict LC state and cnt csr
        void'(ral.lc_state.predict(lc_state));
        void'(ral.lc_transition_cnt.predict(dec_lc_cnt(cfg.lc_ctrl_vif.otp_i.count)));
      end
    end
  endtask

  virtual task process_otp_prog_rsp();
    forever begin
      push_pull_item#(.HostDataWidth(OTP_PROG_HDATA_WIDTH),
                      .DeviceDataWidth(OTP_PROG_DDATA_WIDTH)) item_rcv;
      otp_prog_fifo.get(item_rcv);
      if (item_rcv.d_data == 1 && cfg.en_scb) begin
        set_exp_alert(.alert_name("fatal_prog_error"), .is_fatal(1));
      end
    end
  endtask

  virtual task process_otp_token_rsp();
    forever begin
      push_pull_item#(.HostDataWidth(lc_ctrl_state_pkg::LcTokenWidth)) item_rcv;
      otp_token_fifo.get(item_rcv);
      if (cfg.en_scb) begin
        `DV_CHECK_EQ(item_rcv.h_data, {`gmv(ral.transition_token_3), `gmv(ral.transition_token_2),
                                       `gmv(ral.transition_token_1), `gmv(ral.transition_token_0)})
      end
    end
  endtask

  // check lc outputs, default all off
  virtual function void check_lc_outputs(lc_outputs_t exp_o = '{default:lc_ctrl_pkg::Off},
                                         string       msg   = "expect all output OFF");
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_dft_en_o,              exp_o.lc_dft_en_o,              msg)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_nvm_debug_en_o,        exp_o.lc_nvm_debug_en_o,        msg)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_hw_debug_en_o,         exp_o.lc_hw_debug_en_o,         msg)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_cpu_en_o,              exp_o.lc_cpu_en_o,              msg)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_keymgr_en_o,           exp_o.lc_keymgr_en_o,           msg)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_escalate_en_o,         exp_o.lc_escalate_en_o,         msg)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_owner_seed_sw_rw_en_o, exp_o.lc_owner_seed_sw_rw_en_o, msg)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_iso_part_sw_rd_en_o,   exp_o.lc_iso_part_sw_rd_en_o,   msg)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_iso_part_sw_wr_en_o,   exp_o.lc_iso_part_sw_wr_en_o,   msg)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_seed_hw_rd_en_o,       exp_o.lc_seed_hw_rd_en_o,       msg)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_creator_seed_sw_rw_en_o,
                 exp_o.lc_creator_seed_sw_rw_en_o, msg)
  endfunction

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg csr;
    bit     do_read_check   = 1'b0;
    bit     write           = item.is_write();
    uvm_reg_addr_t csr_addr = ral.get_word_aligned_addr(item.a_addr);
    lc_outputs_t exp        = '{default:lc_ctrl_pkg::Off};

    bit addr_phase_read   = (!write && channel == AddrChannel);
    bit addr_phase_write  = (write && channel == AddrChannel);
    bit data_phase_read   = (!write && channel == DataChannel);
    bit data_phase_write  = (write && channel == DataChannel);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.csr_addrs[ral_name]}) begin
      csr = ral.default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end
    else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    // if incoming access is a write to a valid csr, then make updates right away
    if (addr_phase_write) begin
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
    end

    // process the csr req
    // for write, update local variable and fifo at address phase
    // for read, update predication at address phase and compare at data phase
    case (csr.get_name())
      // TODO: temp enable read checking, once do_read_check default set to 1, should not need this.
      "lc_transition_cnt", "lc_state": do_read_check = 1;
      "status": begin
        if (data_phase_read) begin
          // when lc successfully req a transition, all outputs are turned off, except for the
          // lc_escalate_en_o signal, which is asserted when in scrap state.
          exp.lc_escalate_en_o = lc_ctrl_pkg::On;
          if (item.d_data[ral.status.transition_successful.get_lsb_pos()]) check_lc_outputs(exp);
        end
      end
      default: begin
        // `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
      end
    endcase

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (data_phase_read) begin
      if (do_read_check) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
                     $sformatf("reg name: %0s", csr.get_full_name()))
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end
  endtask

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset local fifos queues and variables
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
  endfunction

endclass
