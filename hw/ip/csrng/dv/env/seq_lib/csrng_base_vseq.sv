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
  bit [3:0]              alt_flags;
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
    // TODO(#19031): Remove this task once scoreboard checks that its queues are empty.
  endtask

  // setup basic csrng features
  virtual task csrng_init();
    // In cases where we are testing alert scenarios using invalid register configurations
    // we must first disable the DUT assertions to allow the environment to catch the alerts
    if (cfg.use_invalid_mubi) begin
      cfg.csrng_assert_vif.assert_off_alert();
    end

    // Enables
    csr_wr(.ptr(ral.regwen), .value(cfg.regwen));
    ral.ctrl.enable.set(cfg.enable);
    ral.ctrl.sw_app_enable.set(cfg.sw_app_enable);
    ral.ctrl.read_int_state.set(cfg.read_int_state);
    csr_update(.csr(ral.ctrl));
  endtask

  task wait_cmd_req_done();
    // Sample while SW app is not ready
    cov_vif.cg_err_code_sample(.err_code(32'b0));
    csr_spinwait_or_edn_rst_n(.ptr(ral.intr_state.cs_cmd_req_done), .exp_data(1'b1));
    if (edn_under_reset()) return;
    csr_rd_check(.ptr(ral.sw_cmd_sts.cmd_sts), .compare_value(1'b0));
    check_interrupts(.interrupts((1 << CmdReqDone)), .check_set(1'b1));
  endtask

  function automatic bit edn_under_reset();
    return cfg.m_edn_agent_cfg[0].vif.rst_n === 1'b0;
  endfunction

  // Wait for a CSR to contain an expected value or EDN to be reset, whichever happens first.  This
  // is useful for the SW app interface, which behaves like an EDN agent in the sense that it can
  // stop requests at any time.  (For simplicity, we currently disable all EDN agents together.)
  task automatic csr_spinwait_or_edn_rst_n(input uvm_object ptr, input uvm_reg_data_t exp_data);
    `DV_SPINWAIT(
      forever begin
        uvm_reg_data_t act_data;
        if (edn_under_reset()) break;
        csr_rd(.ptr(ptr), .value(act_data));
        if (act_data == exp_data) break;
      end,
      "timeout waiting for a CSR to contain an expected value or for EDN to be reset",
      1_000_000_000 /* 1e9 ns = 1 s; practically forever */
    )
  endtask

  task send_cmd_req(uint app, csrng_item cs_item, bit await_response=1'b1, bit edn_rst_as_ack=1'b1);
    bit [csrng_pkg::CSRNG_CMD_WIDTH-1:0]   cmd;
    // Gen cmd_req
    if ((cs_item.acmd != INS) && (cs_item.acmd != RES)) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(alt_flags)
      cmd = {cs_item.glen, alt_flags, cs_item.clen, 1'b0, cs_item.acmd};
    end
    else begin
      cmd = {cs_item.glen, cs_item.flags, cs_item.clen, 1'b0, cs_item.acmd};
    end
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
      if (await_response) begin
        // Wait for ack
        if (edn_rst_as_ack) cfg.m_edn_agent_cfg[app].vif.wait_cmd_ack_or_rst_n();
        else cfg.m_edn_agent_cfg[app].vif.wait_cmd_ack();
      end
    end
    else begin
      // Wait for CSRNG cmd_rdy
      csr_spinwait_or_edn_rst_n(.ptr(ral.sw_cmd_sts.cmd_rdy), .exp_data(1'b1));
      if (edn_under_reset()) begin
        `uvm_info(`gfn, "SW app stopped due to EDN reset", UVM_HIGH)
        return;
      end

      csr_wr(.ptr(ral.cmd_req), .value(cmd));
      if (edn_under_reset()) begin
        `uvm_info(`gfn, "SW app stopped due to EDN reset", UVM_HIGH)
        return;
      end

      for (int i = 0; i < cs_item.clen; i++) begin
        cmd = cs_item.cmd_data_q.pop_front();
        // Wait for CSRNG cmd_rdy
        csr_spinwait_or_edn_rst_n(.ptr(ral.sw_cmd_sts.cmd_rdy), .exp_data(1'b1));
        if (edn_under_reset()) begin
          `uvm_info(`gfn, "SW app stopped due to EDN reset", UVM_HIGH)
          return;
        end

        csr_wr(.ptr(ral.cmd_req), .value(cmd));
        if (edn_under_reset()) begin
          `uvm_info(`gfn, "SW app stopped due to EDN reset", UVM_HIGH)
          return;
        end
      end
      if (await_response) begin
        if (cs_item.acmd != csrng_pkg::GEN) begin
          wait_cmd_req_done();
        end
        else begin
          for (int i = 0; i < cs_item.glen; i++) begin
            csr_spinwait_or_edn_rst_n(.ptr(ral.genbits_vld.genbits_vld), .exp_data(1'b1));
            if (edn_under_reset()) begin
              `uvm_info(`gfn, "SW app stopped due to EDN reset", UVM_HIGH)
              return;
            end
            for (int i = 0; i < csrng_pkg::GENBITS_BUS_WIDTH/TL_DW; i++) begin
              csr_rd(.ptr(ral.genbits.genbits), .value(rdata));
              if (edn_under_reset()) begin
                `uvm_info(`gfn, "SW app stopped due to EDN reset", UVM_HIGH)
                return;
              end
            end
          end
          wait_cmd_req_done();
        end
      end
    end
  endtask // send_cmd_req

  task force_path(string path1, string path2, bit value1, bit value2);
    if (!uvm_hdl_check_path(path1)) begin
      `uvm_fatal(`gfn, "\n\t ----| PATH NOT FOUND")
    end else begin
      `DV_CHECK(uvm_hdl_force(path1, value1));
    end
    if (!uvm_hdl_check_path(path2)) begin
      `uvm_fatal(`gfn, "\n\t ----| PATH NOT FOUND")
    end else begin
      `DV_CHECK(uvm_hdl_force(path2, value2));
    end
  endtask // force_path

  task force_fifo_readwrite_err(string path1, string path2, string path3, bit value1, bit value2,
                            bit[3:0] value3, uvm_reg_field reg_field, bit exp_data);
    if (!uvm_hdl_check_path(path3)) begin
      `uvm_fatal(`gfn, "\n\t ----| PATH NOT FOUND")
    end else begin
      `DV_CHECK(uvm_hdl_force(path3, value3));
    end
    force_path(path1, path2, value1, value2);
    // Check register value
    csr_spinwait(.ptr(reg_field), .exp_data(exp_data));
    `DV_CHECK(uvm_hdl_release(path1));
    `DV_CHECK(uvm_hdl_release(path2));
    `DV_CHECK(uvm_hdl_release(path3));
  endtask // force_fifo_err

  task force_fifo_err(string path1, string path2, bit value1, bit value2,
                      uvm_reg_field reg_field, bit exp_data);
    force_path(path1, path2, value1, value2);
    // Check register value
    csr_spinwait(.ptr(reg_field), .exp_data(exp_data));
    `DV_CHECK(uvm_hdl_release(path1));
    `DV_CHECK(uvm_hdl_release(path2));
  endtask // force_fifo_err

  task force_fifo_err_exception(string path1, string path2, bit value1, bit value2,
                                bit value3, uvm_reg_field reg_field, bit exp_data);
    force_path(path1, path2, value1, value2);
    // Check register value
    csr_spinwait(.ptr(reg_field), .exp_data(exp_data));
    `DV_CHECK(uvm_hdl_force(path1, value3));
    `DV_CHECK(uvm_hdl_release(path2));
  endtask // force_fifo_err_exception

  task force_all_fifo_errs(string paths [6], bit values [6], string path_exts [6],
                           uvm_reg_field reg_field, bit exp_data, int case_state);
    int    index1 [$], index2 [$], index3 [$];
    string path_push, path_full, path_data, path_pop, path_not_empty;
    bit    val_push, val_full, val_data, val_pop, val_not_empty;
    case (case_state)
      fifo_write: begin // fifo write err
        index1     = path_exts.find_index(x) with (x == "push");
        index2     = path_exts.find_index(x) with (x == "full");
        index3     = path_exts.find_index(x) with (x == "wdata");
        path_push  = paths[index1[0]];
        path_full  = paths[index2[0]];
        path_data  = paths[index3[0]];
        val_push   = values[index1[0]];
        val_full   = values[index2[0]];
        val_data   = values[index3[0]];
        force_fifo_readwrite_err(path_push, path_full, path_data, 1'b1, 1'b1, 8'b0, reg_field,
                                 exp_data);
      end
      fifo_read: begin // fifo read err
        index1         = path_exts.find_index(x) with (x == "pop");
        index2         = path_exts.find_index(x) with (x == "not_empty");
        index3         = path_exts.find_index(x) with (x == "rdata");
        path_pop       = paths[index1[0]];
        path_not_empty = paths[index2[0]];
        path_data      = paths[index3[0]];
        val_pop        = values[index1[0]];
        val_not_empty  = values[index2[0]];
        force_fifo_readwrite_err(path_pop, path_not_empty, path_data, 1'b1, 1'b0, 8'b0, reg_field,
                                 exp_data);
      end
      fifo_state: begin // fifo state err
        index1         = path_exts.find_index(x) with (x == "full");
        index2         = path_exts.find_index(x) with (x == "not_empty");
        path_full      = paths[index1[0]];
        path_not_empty = paths[index2[0]];
        val_full       = values[index1[0]];
        val_not_empty  = values[index2[0]];
        force_fifo_err(path_full, path_not_empty, 1'b1, 1'b0, reg_field, exp_data);
      end
      default: begin
        `uvm_fatal(`gfn, "Invalid case! (bug in environment)")
      end
    endcase // case (case_state)
  endtask // force_all_fifo_errs

  task force_all_fifo_errs_exception(string paths [6], bit values [6],string path_exts [6],
                                     uvm_reg_field reg_field, bit exp_data, int case_state);
    int    index1 [$], index2 [$];
    string path_push, path_full, path_pop, path_not_empty;
    bit    val_push, val_full, val_pop, val_not_empty;
    case (case_state)
      fifo_write: begin // fifo write err
        index1     = path_exts.find_index(x) with (x == "push");
        index2     = path_exts.find_index(x) with (x == "full");
        path_push  = paths[index1[0]];
        path_full  = paths[index2[0]];
        val_push   = values[index1[0]];
        val_full   = values[index2[0]];
        force_fifo_err(path_push, path_full, val_push, val_full, reg_field, exp_data);
      end
      fifo_read: begin // fifo read err
        index1         = path_exts.find_index(x) with (x == "pop");
        index2         = path_exts.find_index(x) with (x == "not_empty");
        path_pop       = paths[index1[0]];
        path_not_empty = paths[index2[0]];
        val_pop        = values[index1[0]];
        val_not_empty  = values[index2[0]];
        force_fifo_err_exception(path_pop, path_not_empty, val_pop, val_not_empty, 1'b0,
                                 reg_field, exp_data);
      end
      fifo_state: begin // fifo state err
        index1         = path_exts.find_index(x) with (x == "full");
        index2         = path_exts.find_index(x) with (x == "not_empty");
        path_full      = paths[index1[0]];
        path_not_empty = paths[index2[0]];
        val_full       = values[index1[0]];
        val_not_empty  = values[index2[0]];
        force_fifo_err(path_full, path_not_empty, val_full, val_not_empty, reg_field, exp_data);
      end
      default: begin
        `uvm_fatal(`gfn, "Invalid case! (bug in environment)")
      end
    endcase // case (case_state)
  endtask // force_all_fifo_errs_exception

  task force_path_err(string path, bit [7:0] value, uvm_reg_field reg_field,
                      bit exp_data);
    if (!uvm_hdl_check_path(path)) begin
      `uvm_fatal(`gfn, $sformatf("\n\t ----| PATH NOT FOUND"))
    end else begin
      `DV_CHECK(uvm_hdl_force(path, value));
      cfg.clk_rst_vif.wait_clks(50);
      `DV_CHECK(uvm_hdl_release(path));
      cfg.clk_rst_vif.wait_clks(50);
      // Check register value
      csr_rd_check(.ptr(reg_field), .compare_value(exp_data));
    end
  endtask // force_path_err

  task force_cnt_err(string path, uvm_reg_field reg_field, bit exp_data, int ctr_width);
    bit[31:0] tmp_cnt, bit_flip_mask, tamper_cnt;
    if (ctr_width > 32) begin
      `uvm_fatal(`gfn, $sformatf("\n\t ----| ctr_width greater than 32: %d %s", ctr_width, path))
    end
    if (!uvm_hdl_check_path(path)) begin
      `uvm_fatal(`gfn, $sformatf("\n\t ----| PATH NOT FOUND: %s", path))
    end else begin
      // Read the correct count value
      `DV_CHECK(uvm_hdl_read(path, tmp_cnt));
      // Randomize bit flip vector
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(bit_flip_mask, $onehot(bit_flip_mask);)
      // Make sure the random bit is within the ctr_width (this has a slight prefernce for lower
      // bits in case 32 is not divisible by ctr_width)
      while (bit_flip_mask > (32'h1 << (ctr_width-1))) begin
        bit_flip_mask = bit_flip_mask >> ctr_width;
      end
      // Flip the bit
      tamper_cnt = tmp_cnt ^ bit_flip_mask;
      // Write back count with flipped bit
      `DV_CHECK(uvm_hdl_force(path, tamper_cnt));
      cfg.clk_rst_vif.wait_clks(50);
      `DV_CHECK(uvm_hdl_release(path));
      cfg.clk_rst_vif.wait_clks(50);
      // Check register value
      csr_rd_check(.ptr(reg_field), .compare_value(exp_data));
    end
  endtask // force_cnt_err

  // Find the first or last index in the original string that the target character appears
  function automatic int find_index (string target, string original_str, string which_index);
    int        index;
    case (which_index)
      "first": begin
        for (int i = original_str.len(); i > 0; i--) begin
          if (original_str[i] == target) index = i;
        end
      end
      "last": begin
        for (int i = 0; i < original_str.len(); i++) begin
          if (original_str[i] == target) index = i;
        end
      end
      default: begin
        `uvm_fatal(`gfn, "Invalid index!")
      end
    endcase // case (which_index)
    return index;
  endfunction // find_index
endclass : csrng_base_vseq
