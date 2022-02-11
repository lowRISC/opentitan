// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_base_vseq extends cip_base_vseq #(
    .RAL_T               (csrng_reg_block),
    .CFG_T               (csrng_env_cfg),
    .COV_T               (csrng_env_cov),
    .VIRTUAL_SEQUENCER_T (csrng_virtual_sequencer)
  );
  `uvm_object_utils(csrng_base_vseq)
  `uvm_object_new

  bit                    do_csrng_init = 1'b1;
  bit [TL_DW-1:0]        rdata;
  virtual csrng_cov_if   cov_vif;

  push_pull_device_seq#(.HostDataWidth(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH))
      m_entropy_src_pull_seq;
  push_pull_host_seq#(.HostDataWidth(csrng_pkg::CSRNG_CMD_WIDTH))
      m_edn_push_seq[NUM_HW_APPS];
  push_pull_host_seq#(.HostDataWidth(1))   m_aes_halt_pull_seq;

  virtual task body();
    if (!uvm_config_db#(virtual csrng_cov_if)::get(null, "*.env" , "csrng_cov_if", cov_vif)) begin
      `uvm_fatal(`gfn, $sformatf("Failed to get csrng_cov_if from uvm_config_db"))
    end

    cov_vif.cg_cfg_sample(.cfg(cfg));
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    cfg.otp_en_cs_sw_app_read_vif.drive(.val(cfg.otp_en_cs_sw_app_read));
    cfg.lc_hw_debug_en_vif.drive(.val(cfg.lc_hw_debug_en));

    super.dut_init(reset_kind);

    if (do_csrng_init) csrng_init();
  endtask

  virtual task dut_shutdown();
    // check for pending csrng operations and wait for them to complete
    // TODO
  endtask

  // setup basic csrng features
  virtual task csrng_init();

    // Enables
    csr_wr(.ptr(ral.regwen), .value(cfg.regwen));
    ral.ctrl.enable.set(cfg.enable);
    ral.ctrl.sw_app_enable.set(cfg.sw_app_enable);
    ral.ctrl.read_int_state.set(cfg.read_int_state);
    csr_update(.csr(ral.ctrl));
  endtask

  task wait_cmd_req_done();
    csr_spinwait(.ptr(ral.intr_state.cs_cmd_req_done), .exp_data(1'b1));
    csr_rd_check(.ptr(ral.sw_cmd_sts.cmd_sts), .compare_value(1'b0));
    check_interrupts(.interrupts((1 << CmdReqDone)), .check_set(1'b1));
  endtask

  task send_cmd_req(uint app, csrng_item cs_item);
    bit [csrng_pkg::CSRNG_CMD_WIDTH-1:0]   cmd;
    // Gen cmd_req
    cmd = {cs_item.glen, cs_item.flags, cs_item.clen, 1'b0, cs_item.acmd};
    if (app != SW_APP) begin
      cfg.m_edn_agent_cfg[app].m_cmd_push_agent_cfg.add_h_user_data(cmd);
      m_edn_push_seq[app].num_trans = cs_item.clen + 1;
      for (int i = 0; i < cs_item.clen; i++)
        cfg.m_edn_agent_cfg[app].m_cmd_push_agent_cfg.add_h_user_data(
            cs_item.cmd_data_q.pop_front());
      fork
        // Drive cmd_req
        m_edn_push_seq[app].start(p_sequencer.edn_sequencer_h[app].m_cmd_push_sequencer);
      join_none
      // Wait for ack
      cfg.m_edn_agent_cfg[app].vif.wait_cmd_ack();
    end
    else begin
      // Wait for CSRNG cmd_rdy
      csr_spinwait(.ptr(ral.sw_cmd_sts.cmd_rdy), .exp_data(1'b1));
      csr_wr(.ptr(ral.cmd_req), .value(cmd));
      for (int i = 0; i < cs_item.clen; i++) begin
        cmd = cs_item.cmd_data_q.pop_front();
        // Wait for CSRNG cmd_rdy
        csr_spinwait(.ptr(ral.sw_cmd_sts.cmd_rdy), .exp_data(1'b1));
        csr_wr(.ptr(ral.cmd_req), .value(cmd));
      end
      if (cs_item.acmd != csrng_pkg::GEN) begin
        wait_cmd_req_done();
      end
      else begin
        for (int i = 0; i < cs_item.glen; i++) begin
          csr_spinwait(.ptr(ral.genbits_vld.genbits_vld), .exp_data(1'b1));
          for (int i = 0; i < csrng_pkg::GENBITS_BUS_WIDTH/TL_DW; i++) begin
            csr_rd(.ptr(ral.genbits.genbits), .value(rdata));
          end
        end
        wait_cmd_req_done();
      end
    end
  endtask
endclass : csrng_base_vseq
