// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`define GMV32(csr) 32'(`gmv(csr))

class lc_ctrl_scoreboard extends cip_base_scoreboard #(
  .CFG_T(lc_ctrl_env_cfg),
  .RAL_T(lc_ctrl_reg_block),
  .COV_T(lc_ctrl_env_cov)
);
  `uvm_component_utils(lc_ctrl_scoreboard)

  // local variables
  bit is_personalized;

  lc_ctrl_pkg::lc_tx_t exp_clk_byp_req = lc_ctrl_pkg::Off;

  // Data to program OTP
  protected otp_ctrl_pkg::lc_otp_program_req_t m_otp_prog_data;
  // First OTP program instruction count cleared by reset
  protected uint m_otp_prog_cnt;
  event check_lc_output_ev;

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(push_pull_item #(
    .HostDataWidth  (OTP_PROG_HDATA_WIDTH),
    .DeviceDataWidth(OTP_PROG_DDATA_WIDTH)
  )) otp_prog_fifo;
  uvm_tlm_analysis_fifo #(kmac_app_item) kmac_app_req_fifo;
  uvm_tlm_analysis_fifo #(kmac_app_item) kmac_app_rsp_fifo;
  uvm_tlm_analysis_fifo #(alert_esc_seq_item) esc_wipe_secrets_fifo;
  uvm_tlm_analysis_fifo #(alert_esc_seq_item) esc_scrap_state_fifo;
  uvm_tlm_analysis_fifo #(jtag_riscv_item) jtag_riscv_fifo;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    otp_prog_fifo = new("otp_prog_fifo", this);
    kmac_app_req_fifo = new("kmac_app_req_fifo", this);
    kmac_app_rsp_fifo = new("kmac_app_rsp_fifo", this);
    esc_wipe_secrets_fifo = new("esc_wipe_secrets_fifo", this);
    esc_scrap_state_fifo = new("esc_scrap_state_fifo", this);
    jtag_riscv_fifo = new("jtag_riscv_fifo", this);

  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      check_lc_output();
      process_otp_prog_rsp();
      process_kmac_app_req();
      process_kmac_app_rsp();
      if (cfg.jtag_riscv_map != null) process_jtag_riscv();
    join_none
  endtask

  virtual task check_lc_output();
    forever begin
      @(posedge cfg.pwr_lc_vif.pins[LcPwrDoneRsp] && cfg.en_scb) begin
        dec_lc_state_e lc_state = dec_lc_state(lc_state_e'(cfg.lc_ctrl_vif.otp_i.state));
        lc_outputs_t   exp_lc_o = EXP_LC_OUTPUTS[int'(lc_state)];
        string         err_msg = $sformatf("LC_St %0s", lc_state.name);
        cfg.clk_rst_vif.wait_n_clks(1);

        // lc_creator_seed_sw_rw_en_o is ON only when device has NOT been personalized or RMA state
        if (is_personalized && lc_state != DecLcStRma) begin
          exp_lc_o.lc_creator_seed_sw_rw_en_o = lc_ctrl_pkg::Off;
        end
        // lc_seed_hw_rd_en_o is ON only when device has been personalized or RMA state
        if (!is_personalized && lc_state != DecLcStRma) begin
          exp_lc_o.lc_seed_hw_rd_en_o = lc_ctrl_pkg::Off;
        end

        // lc_seed_hw_rd_en copies otp_secrets_valid in certain states
        if (cfg.err_inj.otp_secrets_valid_mubi_err && lc_state_e'(cfg.lc_ctrl_vif.otp_i.state)
            inside {LcStProd, LcStProdEnd, LcStDev}) begin
          exp_lc_o.lc_seed_hw_rd_en_o = cfg.otp_secrets_valid;
          exp_lc_o.lc_creator_seed_sw_rw_en_o = lc_tx_t'(~cfg.otp_secrets_valid);
        end

        if (cfg.escalate_injected) begin
          exp_lc_o = EXP_LC_OUTPUTS[int'(DecLcStEscalate)];
        end

        fork
          begin
            // Delay a some of cycles to allow escalate to be recognised
            if (cfg.escalate_injected) cfg.clk_rst_vif.wait_clks(5);
            ->check_lc_output_ev;
            check_lc_outputs(exp_lc_o, {$sformatf("Called from line: %0d, ", `__LINE__), err_msg});
          end
        join_none

        if (cfg.err_inj.state_err || cfg.err_inj.count_err ||
            cfg.err_inj.state_backdoor_err || cfg.err_inj.count_backdoor_err ||
            cfg.err_inj.count_illegal_err || cfg.err_inj.state_illegal_err ||
            cfg.err_inj.lc_fsm_backdoor_err || cfg.err_inj.kmac_fsm_backdoor_err ||
            cfg.err_inj.clk_byp_rsp_mubi_err || cfg.err_inj.otp_secrets_valid_mubi_err
            ) begin // State/count error expected
          set_exp_alert(.alert_name("fatal_state_error"), .is_fatal(1),
                        .max_delay(cfg.alert_max_delay));
        end

        if (cfg.err_inj.otp_prog_err || cfg.err_inj.clk_byp_error_rsp ||
            cfg.err_inj.clk_byp_rsp_mubi_err) begin
          // OTP program error expected
          set_exp_alert(.alert_name("fatal_prog_error"), .is_fatal(1),
                        .max_delay(cfg.alert_max_delay));
        end

      end
    end
  endtask

  virtual task process_otp_prog_rsp();
    otp_ctrl_pkg::lc_otp_program_req_t otp_prog_data_exp;
    lc_state_e otp_prog_state_act, otp_prog_state_exp;
    lc_cnt_e otp_prog_count_act, otp_prog_count_exp;
    const string MsgFmt = "Check failed %s == %s %s [%h] vs %s [%h]";
    forever begin
      push_pull_item #(
        .HostDataWidth  (OTP_PROG_HDATA_WIDTH),
        .DeviceDataWidth(OTP_PROG_DDATA_WIDTH)
      ) item_rcv;
      otp_prog_fifo.get(item_rcv);
      if (item_rcv.d_data == 1 && cfg.en_scb) begin
        set_exp_alert(.alert_name("fatal_prog_error"), .is_fatal(1));
      end

      // Error if this occurs in the in the Post Transition test phase or beyond
      `DV_CHECK_LT(cfg.test_phase, LcCtrlPostTransition, "Second transition detected")

      // Decode and store to use for prediction
      m_otp_prog_data = otp_ctrl_pkg::lc_otp_program_req_t'(item_rcv.h_data);

      // Increment otp program count
      m_otp_prog_cnt++;

      // Get expected from model
      otp_prog_data_exp  = predict_otp_prog_req();

      otp_prog_state_act = lc_state_e'(m_otp_prog_data.state);
      otp_prog_state_exp = lc_state_e'(otp_prog_data_exp.state);
      otp_prog_count_exp = lc_cnt_e'(otp_prog_data_exp.count);
      otp_prog_count_act = lc_cnt_e'(m_otp_prog_data.count);

      `DV_CHECK_EQ(otp_prog_state_act, otp_prog_state_exp, $sformatf(
                   " - %s vs %s", otp_prog_state_act.name, otp_prog_state_exp.name))

      `DV_CHECK_EQ(otp_prog_count_act, otp_prog_count_exp, $sformatf(
                   " - %s vs %s", otp_prog_count_act.name, otp_prog_count_exp.name))

      // Check OTP vendor control
      if (!cfg.err_inj.lc_fsm_backdoor_err && !cfg.err_inj.count_backdoor_err) begin
        // Don't check for backdoor error injection as the results
        // are unpredictable
        `DV_CHECK_EQ(cfg.lc_ctrl_vif.otp_vendor_test_ctrl_o, predict_otp_vendor_test_ctrl())
      end
    end
  endtask

  // verilog_format: off - avoid bad formatting
  virtual task process_kmac_app_req();
    forever begin
      bit [127:0] token_data;
      kmac_app_item item_rcv;
      kmac_app_req_fifo.get(item_rcv);
      `uvm_info(`gfn, item_rcv.sprint(uvm_default_line_printer), UVM_HIGH)

      // Should be 16 bytes of data
      `DV_CHECK_EQ_FATAL(item_rcv.byte_data_q.size(), 16)
      // Unpack token data from request
      for(int i=0; i<16; i++) begin
        token_data[i*8 +: 8] = item_rcv.byte_data_q[i];
      end
      `uvm_info(`gfn, $sformatf("process_kmac_app_req: token received %h", token_data), UVM_MEDIUM)

      if (cfg.en_scb) begin
        `DV_CHECK_EQ(token_data, {`GMV32(ral.transition_token[3]),
                                  `GMV32(ral.transition_token[2]),
                                  `GMV32(ral.transition_token[1]),
                                  `GMV32(ral.transition_token[0])})
      end
    end
  endtask
  // verilog_format: on

  virtual task process_kmac_app_rsp();
    forever begin
      kmac_app_item item_rcv;
      kmac_app_rsp_fifo.get(item_rcv);
      `uvm_info(`gfn, item_rcv.sprint(uvm_default_line_printer), UVM_HIGH)
    end
  endtask

  virtual task process_jtag_riscv();
    jtag_riscv_item      jt_item;
    tl_seq_item          tl_item;
    const uvm_reg_addr_t jtag_risc_address_mask = ~(2 ** (DMI_ADDRW + 2) - 1);
    const uvm_reg_addr_t base_address = cfg.jtag_riscv_map.get_base_addr();
    const uvm_reg_addr_t base_address_masked = base_address & jtag_risc_address_mask;

    forever begin
      jtag_riscv_fifo.get(jt_item);
      `uvm_info(`gfn, {"process_jtag_risc: ", jt_item.sprint(uvm_default_line_printer)}, UVM_MEDIUM)
      if ((jt_item.op === DmiRead || jt_item.op === DmiWrite) && jt_item.status === DmiNoErr) begin
        `uvm_create_obj(tl_seq_item, tl_item)
        tl_item.a_addr   = base_address_masked | (jt_item.addr << 2);
        tl_item.a_data   = jt_item.data;
        tl_item.a_opcode = (jt_item.op === DmiRead) ? tlul_pkg::Get : tlul_pkg::PutFullData;
        tl_item.a_mask   = '1;
        tl_item.d_data   = jt_item.data;
        tl_item.d_opcode = (jt_item.op === DmiRead) ? tlul_pkg::Get : tlul_pkg::PutFullData;


        process_tl_access(tl_item, AddrChannel, "lc_ctrl_reg_block");
        process_tl_access(tl_item, DataChannel, "lc_ctrl_reg_block");


      end
    end
  endtask

  // check lc outputs, default all off
  virtual function void check_lc_outputs(lc_outputs_t exp_o = '{default: lc_ctrl_pkg::Off},
                                         string msg = "expect all output OFF");
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_dft_en_o, exp_o.lc_dft_en_o, msg)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_nvm_debug_en_o, exp_o.lc_nvm_debug_en_o, msg)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_hw_debug_en_o, exp_o.lc_hw_debug_en_o, msg)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_cpu_en_o, exp_o.lc_cpu_en_o, msg)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_keymgr_en_o, exp_o.lc_keymgr_en_o, msg)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_escalate_en_o, exp_o.lc_escalate_en_o, msg)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_owner_seed_sw_rw_en_o, exp_o.lc_owner_seed_sw_rw_en_o, msg)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_iso_part_sw_rd_en_o, exp_o.lc_iso_part_sw_rd_en_o, msg)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_iso_part_sw_wr_en_o, exp_o.lc_iso_part_sw_wr_en_o, msg)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_seed_hw_rd_en_o, exp_o.lc_seed_hw_rd_en_o, msg)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.lc_creator_seed_sw_rw_en_o, exp_o.lc_creator_seed_sw_rw_en_o, msg)
    `DV_CHECK_EQ(cfg.lc_ctrl_vif.clk_byp_req_o, exp_clk_byp_req, msg)
  endfunction

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg        csr;
    bit            do_read_check = 1'b0;
    bit            write = item.is_write();
    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);
    lc_outputs_t   exp = '{default: lc_ctrl_pkg::Off};

    bit            addr_phase_read = (!write && channel == AddrChannel);
    bit            addr_phase_write = (write && channel == AddrChannel);
    bit            data_phase_read = (!write && channel == DataChannel);
    bit            data_phase_write = (write && channel == DataChannel);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    // if incoming access is a write to a valid csr, then make updates right away
    if (addr_phase_write && cfg.en_scb_ral_update_write) begin
      case (csr.get_name())
        "transition_ctrl": begin
          if (`gmv(ral.claim_transition_if) == prim_mubi_pkg::MuBi8True) begin
            dec_lc_state_e lc_state = dec_lc_state(lc_state_e'(cfg.lc_ctrl_vif.otp_i.state));
            if (!(lc_state inside {DecLcStDev, DecLcStProd, DecLcStProdEnd, DecLcStScrap,
                                   DecLcStPostTrans, DecLcStEscalate, DecLcStInvalid})) begin
              if (item.a_data[0]) exp_clk_byp_req = lc_ctrl_pkg::On;
              else                exp_clk_byp_req = lc_ctrl_pkg::Off;
            end
          end
        end
        default: begin
         // Do nothing.
        end
      endcase
      `uvm_info(`gfn, {
                "process_tl_access: write predict ",
                csr.get_name(),
                " ",
                item.sprint(uvm_default_line_printer)
                }, UVM_MEDIUM)
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
    end

    if (addr_phase_read) begin
      case (csr.get_name())
        "lc_state": begin
          `DV_CHECK_FATAL(ral.lc_state.state.predict(
                          .value(predict_lc_state()), .kind(UVM_PREDICT_READ)))
        end

        "lc_transition_cnt": begin
          `DV_CHECK_FATAL(ral.lc_transition_cnt.cnt.predict(
                          .value(predict_lc_transition_cnt()), .kind(UVM_PREDICT_READ)))
        end

        "device_id_0",  "device_id_1", "device_id_2",
            "device_id_3",  "device_id_4", "device_id_5",
            "device_id_6",  "device_id_7" : begin
          string name = csr.get_name();
          string idx_str = string'(name.getc(name.len() - 1));
          int idx = idx_str.atoi();
          // Register values should reflect cfg.otp_device_id
          // which is driven on otp_device_id_i
          `DV_CHECK_FATAL(ral.device_id[idx].predict(
                          .value(cfg.otp_device_id[idx*32+:32]), .kind(UVM_PREDICT_READ)))
        end

        "manuf_state_0",  "manuf_state_1", "manuf_state_2",
            "manuf_state_3",  "manuf_state_4", "manuf_state_5",
            "manuf_state_6",  "manuf_state_7" : begin
          string name = csr.get_name();
          string idx_str = string'(name.getc(name.len() - 1));
          int idx = idx_str.atoi();
          // Register values should reflect cfg.otp_device_id
          // which is driven on otp_device_id_i
          `DV_CHECK_FATAL(ral.manuf_state[idx].predict(
                          .value(cfg.otp_manuf_state[idx*32+:32]), .kind(UVM_PREDICT_READ)))
        end

        "otp_vendor_test_status": begin
          `DV_CHECK_FATAL(ral.otp_vendor_test_status.predict(
                          .value(predict_otp_vendor_test_status()), .kind(UVM_PREDICT_READ)))
        end

        "hw_revision0": begin
          `DV_CHECK_FATAL(
              ral.hw_revision0.silicon_creator_id.predict(
              .value(LcCtrlSiliconCreatorId[lc_ctrl_reg_pkg::SiliconCreatorIdWidth-1:0]),
              .kind(UVM_PREDICT_READ)))
          `DV_CHECK_FATAL(
              ral.hw_revision0.product_id.predict(
              .value(LcCtrlProductId[lc_ctrl_reg_pkg::ProductIdWidth-1:0]),
              .kind(UVM_PREDICT_READ)))
        end

        "hw_revision1": begin
          `DV_CHECK_FATAL(
              ral.hw_revision1.revision_id.predict(
              .value(LcCtrlRevisionId[lc_ctrl_reg_pkg::RevisionIdWidth-1:0]),
              .kind(UVM_PREDICT_READ)))
        end

        default: begin
          // `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
        end
      endcase
    end

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (data_phase_read) begin
      if (csr.get_name() inside {"lc_state", "lc_transition_cnt",
        "device_id_0", "device_id_1", "device_id_2",
            "device_id_3",  "device_id_4", "device_id_5",
            "device_id_6",  "device_id_7", "manuf_state_0",  "manuf_state_1", "manuf_state_2",
            "manuf_state_3",  "manuf_state_4", "manuf_state_5",
            "manuf_state_6",  "manuf_state_7", "otp_vendor_test_status", "hw_rev"
          })
        do_read_check = 1;

      if (do_read_check) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data, $sformatf(
                     "reg name: %0s", csr.get_full_name()))
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
      `uvm_info(`gfn, {
                "process_tl_access: read predict ",
                csr.get_name(),
                " ",
                item.sprint(uvm_default_line_printer)
                }, UVM_MEDIUM)

      if (cfg.test_phase inside {[LcCtrlEscalate : LcCtrlPostTransTransitionComplete]}) begin
        if(cfg.err_inj.lc_fsm_backdoor_err || cfg.err_inj.count_backdoor_err ||
            cfg.err_inj.otp_prog_err || cfg.err_inj.clk_byp_error_rsp) begin
          // Expect escalate to be asserted
          exp.lc_escalate_en_o = lc_ctrl_pkg::On;
        end
      end

      if (cfg.err_inj.security_escalation_err) begin
        // Expect escalate to be asserted
        exp.lc_escalate_en_o = lc_ctrl_pkg::On;
      end

      // when lc successfully req a transition, all outputs are turned off.
      if (ral.status.transition_successful.get()) begin
        fork
          begin
            // Wait for escalate to be recognise
            if (cfg.err_inj.security_escalation_err) cfg.clk_rst_vif.wait_clks(5);
            check_lc_outputs(exp, $sformatf("Called from line: %0d", `__LINE__));
          end
        join_none
      end
    end
  endtask

  // Predict the value of lc_state register
  virtual function bit [31:0] predict_lc_state();
    // Expected lc_state, lc_state register has this repeated DecLcStateNumRep times
    dec_lc_state_e lc_state_single_exp = dec_lc_state_e'('X);
    bit [31:0] lc_state_exp;

    // State error of some kind expected
    bit state_err_exp = cfg.err_inj.state_err || cfg.err_inj.count_err ||
        cfg.err_inj.state_illegal_err || cfg.err_inj.count_illegal_err ||
        cfg.err_inj.count_backdoor_err ||  cfg.err_inj.state_backdoor_err ||
        cfg.err_inj.lc_fsm_backdoor_err || cfg.err_inj.kmac_fsm_backdoor_err ||
        cfg.err_inj.otp_secrets_valid_mubi_err;

    // OTP program error is expected
    bit prog_err_exp = cfg.err_inj.otp_prog_err || cfg.err_inj.clk_byp_error_rsp ||
        cfg.err_inj.clk_byp_rsp_mubi_err;


    // Exceptions to default
    unique case (cfg.test_phase)
      LcCtrlTestInit, LcCtrlIterStart, LcCtrlLcInit, LcCtrlDutInitComplete,
        LcCtrlDutReady, LcCtrlWaitTransition: begin
        // Prior to transition lc_state should mirror otp_i
        lc_state_single_exp = dec_lc_state(lc_state_e'(cfg.lc_ctrl_vif.otp_i.state));
      end
      LcCtrlTransitionComplete, LcCtrlReadState1: begin
        // Default PostTransition
        lc_state_single_exp = DecLcStPostTrans;

        if (cfg.err_inj.security_escalation_err) begin
          // We should have entered escalate state
          lc_state_single_exp = DecLcStEscalate;
        end else if (state_err_exp) begin
          // For state error prior to escalate being triggered we expect Invalid
          lc_state_single_exp = DecLcStInvalid;
        end
      end
      LcCtrlEscalate, LcCtrlReadState2, LcCtrlPostTransition, LcCtrlPostStart: begin
        // Default PostTransition
        lc_state_single_exp = DecLcStPostTrans;

        if (cfg.err_inj.security_escalation_err) begin
          // We should have entered escalate state
          lc_state_single_exp = DecLcStEscalate;
        end else if (state_err_exp || prog_err_exp) begin
          // For state / prog error after escalate is triggered we expect Escalate
          lc_state_single_exp = DecLcStEscalate;
        end
      end
      default: begin
        `uvm_fatal(
            `gfn, $sformatf(
            "predict_lc_state: Unimplemented test_phase %s(%h)", cfg.test_phase.name, cfg.test_phase
            ))
      end
    endcase

    if (cfg.escalate_injected) lc_state_single_exp = DecLcStEscalate;

    // repeat state to fill the word for hardness
    lc_state_exp = {DecLcStateNumRep{lc_state_single_exp}};

    `uvm_info(`gfn, $sformatf(
              "predict_lc_state: lc_state_single_exp=%s(%x) lc_state_exp=%h",
              lc_state_single_exp.name,
              lc_state_single_exp,
              lc_state_exp
              ), UVM_MEDIUM)

    return lc_state_exp;
  endfunction

  // Predict the value of lc_transition_cnt register
  virtual function dec_lc_cnt_t predict_lc_transition_cnt();
    // Default lc_transition_count expected
    dec_lc_cnt_t lc_transition_cnt_exp = 'X;

    // State error of some kind expected
    bit state_err_exp = cfg.err_inj.state_err || cfg.err_inj.count_err ||
        cfg.err_inj.state_illegal_err || cfg.err_inj.count_illegal_err ||
        cfg.err_inj.count_backdoor_err || cfg.err_inj.lc_fsm_backdoor_err ||
        cfg.err_inj.clk_byp_rsp_mubi_err || cfg.err_inj.otp_secrets_valid_mubi_err;

    // Exceptions to default expected lc_transition_count
    unique case (cfg.test_phase)
      LcCtrlTestInit, LcCtrlIterStart, LcCtrlLcInit, LcCtrlDutInitComplete,
      LcCtrlDutReady, LcCtrlWaitTransition: begin
        // Prior to transition lc_transition_count should mirror otp_i
        lc_transition_cnt_exp = dec_lc_cnt(lc_cnt_e'(cfg.lc_ctrl_vif.otp_i.count));
      end
      LcCtrlTransitionComplete, LcCtrlReadState1, LcCtrlEscalate,
        LcCtrlReadState2, LcCtrlPostTransition, LcCtrlPostStart : begin
        // lc_transition_count post transition is maximum value
        lc_transition_cnt_exp = '1;
      end

      default: begin
        `uvm_fatal(`gfn, $sformatf(
                   "predict_lc_transition_cnt: Unimplemented test_phase %s(%h)",
                   cfg.test_phase.name,
                   cfg.test_phase
                   ))
      end
    endcase

    `uvm_info(`gfn, $sformatf(
              "predict_lc_transition_cnt: lc_transition_cnt_exp= %0d", lc_transition_cnt_exp),
              UVM_MEDIUM)

    return lc_transition_cnt_exp;
  endfunction

  virtual function otp_ctrl_pkg::lc_otp_program_req_t predict_otp_prog_req();
    // Convert state and count back to enums
    const lc_state_e LcStateIn = lc_state_e'(cfg.lc_ctrl_vif.otp_i.state);
    const lc_cnt_e LcCntIn = lc_cnt_e'(cfg.lc_ctrl_vif.otp_i.count);
    // Incremented LcCntIn - next() works because of encoding method
    const lc_cnt_e LcCntInInc = LcCntIn.next();
    // ICEBOX(#18078) - unclear what this TODO refers to (needs expanding for JTAG registers)
    const
    lc_state_e
    LcTargetState = encode_lc_state(
        dec_lc_state_e'(cfg.ral.transition_target.state.get_mirrored_value())
    );
    lc_state_e lc_state_exp;
    lc_cnt_e lc_cnt_exp;

    if (m_otp_prog_cnt == 1) begin
      // First program transaction just programs the incremented count so state
      // is the same as input
      lc_cnt_exp   = LcCntInInc;
      lc_state_exp = LcStateIn;
    end else if (m_otp_prog_cnt == 2) begin
      // Second program transaction programs both the incremented count and
      // the transition target state in (TRANSITION_TARGET register)
      lc_cnt_exp   = LcCntInInc;
      lc_state_exp = LcTargetState;
    end

    // Transition to SCRAP state always programs LcCnt24
    if (LcTargetState == LcStScrap) lc_cnt_exp = LcCnt24;

    `uvm_info(`gfn, $sformatf(
              "predict_otp_prog_req: state=%s count=%s", lc_state_exp.name(), lc_cnt_exp.name),
              UVM_MEDIUM)

    return ('{state: lc_state_exp, count: lc_cnt_exp, req: 0});
  endfunction

  // Predict otp_vendor_test_status reg
  virtual function uvm_reg_data_t predict_otp_vendor_test_status();
    // Convert state and count to enums
    const lc_state_e LcStateIn = lc_state_e'(cfg.lc_ctrl_vif.otp_i.state);
    const lc_cnt_e   LcCntIn = lc_cnt_e'(cfg.lc_ctrl_vif.otp_i.count);

    // Reflects otp_vendor_test_status_i in these states otherwise 0
    if ((LcStateIn inside {LC_CTRL_OTP_TEST_REG_ENABLED_STATES}) &&
        (LcCntIn inside {LC_CTRL_OTP_TEST_REG_ENABLED_COUNTS}) &&
        (cfg.test_phase < LcCtrlPostTransition) &&
        !cfg.err_inj.otp_secrets_valid_mubi_err &&
        !cfg.escalate_injected
        ) begin
      return cfg.otp_vendor_test_status;
    end else return 0;
  endfunction

  // Predict otp_vendor_test_ctrl output
  virtual function uvm_reg_data_t predict_otp_vendor_test_ctrl();
    // Convert state and count to enums
    const lc_state_e LcStateIn = lc_state_e'(cfg.lc_ctrl_vif.otp_i.state);
    const lc_cnt_e   LcCntIn = lc_cnt_e'(cfg.lc_ctrl_vif.otp_i.count);

    // Reflects otp_vendor_test_status_i in these states otherwise 0
    if ((LcStateIn inside {LC_CTRL_OTP_TEST_REG_ENABLED_STATES}) &&
        (LcCntIn inside {LC_CTRL_OTP_TEST_REG_ENABLED_COUNTS}) &&
        (cfg.test_phase < LcCtrlPostTransition)) begin
      return cfg.otp_vendor_test_ctrl;
    end else return 0;
  endfunction

  // this function check if the triggered alert is expected
  // to turn off this check, user can set `do_alert_check` to 0
  // We overload this to trigger events in the config object when an alert is triggered
  virtual function void process_alert(string alert_name, alert_esc_seq_item item);
    if (item.alert_handshake_sta == AlertReceived) begin
      case (alert_name)
        "fatal_prog_error": begin
          ->cfg.fatal_prog_error_ev;
        end
        "fatal_state_error": begin
          ->cfg.fatal_state_error_ev;
        end
        "fatal_bus_integ_error": begin
          ->cfg.fatal_bus_integ_error_ev;
        end
        default: begin
          `uvm_fatal(`gfn, {"Unexpected alert received: ", alert_name})
        end
      endcase
    end

    super.process_alert(alert_name, item);

  endfunction

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset local fifos queues and variables
    // Clear OTP program count
    m_otp_prog_cnt = 0;
    exp_clk_byp_req = lc_ctrl_pkg::Off;
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
  endfunction

  `undef GMV32

endclass
