// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class edn_base_vseq extends cip_base_vseq #(
    .RAL_T               (edn_reg_block),
    .CFG_T               (edn_env_cfg),
    .COV_T               (edn_env_cov),
    .VIRTUAL_SEQUENCER_T (edn_virtual_sequencer)
  );
  `uvm_object_utils(edn_base_vseq)
  `uvm_object_new

  bit do_edn_init = 1'b1;
  bit [csrng_pkg::GENBITS_BUS_WIDTH - 1:0]      genbits;
  bit [entropy_src_pkg::FIPS_BUS_WIDTH - 1:0]   fips;
  mubi4_t                                       flags;
  bit [3:0]                                     clen, additional_data;
  bit [11:0]                                    glen;
  bit [csrng_pkg::CSRNG_CMD_WIDTH - 1:0]        cmd_data;

  rand bit                                      set_regwen;
  rand bit                                      write_reserved_err_code_test_reg;
  virtual edn_cov_if                            cov_vif;

  constraint regwen_c {
    set_regwen == 0;
  }

  virtual task body();
    cov_vif.cg_cfg_sample(.cfg(cfg));
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);

    if (!uvm_config_db#(virtual edn_cov_if)::get(null, "*.env" , "edn_cov_if", cov_vif)) begin
      `uvm_fatal(`gfn, $sformatf("Failed to get edn_cov_if from uvm_config_db"))
    end

    if (do_edn_init) begin
      // Initialize DUT and start device sequence
      device_init();
      edn_init();
    end
  endtask

  virtual task device_init();
    csrng_device_seq   m_dev_seq;

    // Let CSRNG agent know that EDN interface is no longer disabled.
    cfg.edn_vif.drive_edn_disable(0);

    m_dev_seq = csrng_device_seq::type_id::create("m_dev_seq");
    fork
      m_dev_seq.start(p_sequencer.csrng_sequencer_h);
    join_none
  endtask

  virtual task edn_init(string reset_kind = "HARD");

    additional_data = 0;

    if (cfg.use_invalid_mubi) begin
      // Turn off DUT assertions so that the corresponding alert can fire
      cfg.edn_assert_vif.assert_off_alert();
    end

    if (cfg.boot_req_mode == MuBi4True) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(flags)
      `DV_CHECK_STD_RANDOMIZE_FATAL(glen)
      wr_cmd(.cmd_type("boot_ins"), .acmd(csrng_pkg::INS), .clen(0), .flags(flags), .glen(glen));
      `DV_CHECK_STD_RANDOMIZE_FATAL(flags)
      if (cfg.force_disable) begin
        wr_cmd(.cmd_type("boot_gen"), .acmd(csrng_pkg::GEN), .clen(0), .flags(flags),
               .glen(1'b1));
      end
      else begin
        wr_cmd(.cmd_type("boot_gen"), .acmd(csrng_pkg::GEN), .clen(0), .flags(flags),
               .glen(cfg.num_boot_reqs));
      end
    end

    if (cfg.auto_req_mode == MuBi4True) begin
      // Verify CMD_FIFO_RST bit
      for (int i = 0; i < 13; i++) begin
        `DV_CHECK_STD_RANDOMIZE_FATAL(cmd_data)
        csr_wr(.ptr(ral.generate_cmd), .value(cmd_data));
      end
      csr_wr(.ptr(ral.ctrl.cmd_fifo_rst), .value(MuBi4True));
      csr_wr(.ptr(ral.ctrl.cmd_fifo_rst), .value(MuBi4False));

      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(clen, clen dist { 0 :/ 20, [1:12] :/ 80 };)
      `DV_CHECK_STD_RANDOMIZE_FATAL(flags)
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(glen, glen dist { 0 :/ 20, [1:$] :/ 80 };)
      wr_cmd(.cmd_type("reseed"), .acmd(csrng_pkg::RES), .clen(clen), .flags(flags), .glen(glen));
      for (int i = 0; i < clen; i++) begin
        `DV_CHECK_STD_RANDOMIZE_FATAL(cmd_data)
        wr_cmd(.cmd_type("reseed"), .cmd_data(cmd_data));
      end
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(clen, clen dist { 0 :/ 20, [1:12] :/ 80 };)
      `DV_CHECK_STD_RANDOMIZE_FATAL(flags)
      glen = 1;
      wr_cmd(.cmd_type("generate"), .acmd(csrng_pkg::GEN), .clen(clen), .flags(flags), .glen(glen));
      for (int i = 0; i < clen; i++) begin
        `DV_CHECK_STD_RANDOMIZE_FATAL(cmd_data)
        wr_cmd(.cmd_type("generate"), .cmd_data(cmd_data));
      end
    end

    // Enable edn, set modes
    ral.ctrl.edn_enable.set(cfg.enable);
    ral.ctrl.boot_req_mode.set(cfg.boot_req_mode);
    ral.ctrl.auto_req_mode.set(cfg.auto_req_mode);
    csr_update(.csr(ral.ctrl));

    // If set_regwen is set, write random value to the EDN, and expect the write won't be taken.
    if (set_regwen) begin
      csr_wr(.ptr(ral.regwen), .value(0));
      csr_wr(.ptr(ral.ctrl), .value($urandom));
    end

    // Read and check ctrl register value. Check in scb.
    if ($urandom_range(0, 19) == 19 || set_regwen) begin
      bit [TL_DW-1:0] val;
      csr_rd(.ptr(ral.ctrl), .value(val));
    end

    if (write_reserved_err_code_test_reg) begin
      `DV_CHECK_RANDOMIZE_WITH_FATAL(ral.err_code_test.err_code_test,
          !(value inside
          {EdnSfifoRescmdErrTest, EdnSfifoGencmdErrTest, EdnSfifoOutputErrTest, EdnAckSmErrTest,
           EdnMainSmErrTest, EdnCntrErrTest, EdnFifoWriteErrTest, EdnFifoReadErrTest,
           EdnFifoStateErrTest});)
      csr_update(ral.err_code_test);
    end
  endtask

  virtual task instantiate_csrng();
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(clen, clen dist { 0 :/ 20, [1:12] :/ 80 };)
    `DV_CHECK_STD_RANDOMIZE_FATAL(flags)
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(glen, glen dist { 0 :/ 20, [1:$] :/ 80 };)
    wr_cmd(.cmd_type("sw"), .acmd(csrng_pkg::INS), .clen(clen), .flags(flags), .glen(glen));
    for (int i = 0; i < clen; i++) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(cmd_data)
      wr_cmd(.cmd_type("sw"), .cmd_data(cmd_data));
    end
  endtask

  virtual task wr_cmd(string cmd_type = "", csrng_pkg::acmd_e acmd = csrng_pkg::INV,
                      bit[3:0] clen = '0, bit[3:0] flags = MuBi4False, bit[17:0] glen = '0,
                      bit [csrng_pkg::CSRNG_CMD_WIDTH - 1:0] cmd_data = '0);

    cov_vif.cg_cs_cmds_sample(.clen(clen), .flags(flags), .glen(glen));

    case (cmd_type)
      "boot_ins": csr_wr(.ptr(ral.boot_ins_cmd), .value({glen, flags, clen, 1'b0, acmd}));
      "boot_gen": csr_wr(.ptr(ral.boot_gen_cmd), .value({glen, flags, clen, 1'b0, acmd}));
      "generate": begin
                    if (additional_data) begin
                      csr_wr(.ptr(ral.generate_cmd), .value(cmd_data));
                      additional_data -= 1;
                    end
                    else begin
                      csr_wr(.ptr(ral.generate_cmd), .value({glen, flags, clen, 1'b0, acmd}));
                      additional_data = clen;
                    end
                  end
      "reseed"  : begin
                    if (additional_data) begin
                      csr_wr(.ptr(ral.reseed_cmd), .value(cmd_data));
                      additional_data -= 1;
                    end
                    else begin
                      csr_wr(.ptr(ral.reseed_cmd), .value({glen, flags, clen, 1'b0, acmd}));
                      additional_data = clen;
                    end
                  end
      "sw"      : begin
                    if (additional_data) begin
                      csr_wr(.ptr(ral.sw_cmd_req), .value(cmd_data));
                      additional_data -= 1;
                    end
                    else begin
                      `DV_SPINWAIT_EXIT(
                        csr_spinwait(.ptr(ral.sw_cmd_sts.cmd_rdy), .exp_data(1'b1));,
                        wait(cfg.abort_sw_cmd);,
                        "Aborted SW command"
                      )
                      if (!cfg.abort_sw_cmd) begin
                        csr_wr(.ptr(ral.sw_cmd_req), .value({glen, flags, clen, 1'b0, acmd}));
                        additional_data = clen;
                      end
                    end
                    if (!additional_data && !cfg.abort_sw_cmd) begin
                      wait_cmd_req_done();
                    end
                  end
      default   : `uvm_fatal(`gfn, $sformatf("Invalid cmd_type: %0s", cmd_type))
    endcase
  endtask

  virtual task wait_cmd_req_done();
    // Expect/Clear interrupt bit
    csr_spinwait(.ptr(ral.intr_state.edn_cmd_req_done), .exp_data(1'b1));
    check_interrupts(.interrupts((1 << CmdReqDone)), .check_set(1'b1));
  endtask

  task force_fifo_err(string path1, string path2, bit value1, bit value2,
                                uvm_reg_field reg_field, bit exp_data);
    if (!uvm_hdl_check_path(path1)) begin
      `uvm_fatal(`gfn, $sformatf("\n\t ----| PATH NOT FOUND"))
    end else begin
      `DV_CHECK(uvm_hdl_force(path1, value1));
    end
    if (!uvm_hdl_check_path(path2)) begin
      `uvm_fatal(`gfn, $sformatf("\n\t ----| PATH NOT FOUND"))
    end else begin
      `DV_CHECK(uvm_hdl_force(path2, value2));
    end
    // Check register value
    csr_spinwait(.ptr(reg_field), .exp_data(exp_data));
    // Clear interrupt_enable
    csr_wr(.ptr(ral.intr_enable), .value(32'd0));
    // This assertion has to be disabled, since FIFO clear on edn_disable leads
    // to unstable h_data (when FIFO write error introduced unaccounted values in FIFO)
    $assertoff(0, "tb.csrng_if.cmd_push_if.H_DataStableWhenValidAndNotReady_A");
    ral.ctrl.edn_enable.set(prim_mubi_pkg::MuBi4False);
    ral.ctrl.cmd_fifo_rst.set(prim_mubi_pkg::MuBi4True);
    csr_update(.csr(ral.ctrl));
    $asserton(0, "tb.csrng_if.cmd_push_if.H_DataStableWhenValidAndNotReady_A");
    // Expect/Clear interrupt bit
    check_interrupts(.interrupts((1 << FifoErr)), .check_set(1'b1));
    `DV_CHECK(uvm_hdl_release(path1));
    `DV_CHECK(uvm_hdl_release(path2));
  endtask // force_fifo_err

  task force_all_fifo_errs(string paths [4], bit values [4], string path_exts [4],
                           uvm_reg_field reg_field, bit exp_data, int case_state);
    int    index1 [$], index2 [$];
    string path_push, path_full, path_pop, path_not_empty;
    bit    val_push, val_full, val_pop, val_not_empty;
    case (case_state)
      fifo_write_error: begin // fifo write err
        index1     = path_exts.find_index(x) with (x == "push");
        index2     = path_exts.find_index(x) with (x == "full");
        path_push  = paths[index1[0]];
        path_full  = paths[index2[0]];
        val_push   = values[index1[0]];
        val_full   = values[index2[0]];
        force_fifo_err(path_push, path_full, 1'b1, 1'b1, reg_field, exp_data);
      end
      fifo_read_error: begin // fifo read err
        index1         = path_exts.find_index(x) with (x == "pop");
        index2         = path_exts.find_index(x) with (x == "not_empty");
        path_pop       = paths[index1[0]];
        path_not_empty = paths[index2[0]];
        val_pop        = values[index1[0]];
        val_not_empty  = values[index2[0]];
        force_fifo_err(path_pop, path_not_empty, 1'b1, 1'b0, reg_field, exp_data);
      end
      fifo_state_error: begin // fifo state err
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

  task force_path_err(string path, bit [5:0] value, uvm_reg_field reg_field,
                      bit exp_data);
    if (!uvm_hdl_check_path(path)) begin
      `uvm_fatal("intr_dbg", $sformatf("\n\t ----| PATH NOT FOUND"))
    end else begin
      `DV_CHECK(uvm_hdl_force(path, value));
      cfg.clk_rst_vif.wait_clks(50);
      `DV_CHECK(uvm_hdl_release(path));
      cfg.clk_rst_vif.wait_clks(50);
      // Check err_code register
      csr_rd_check(.ptr(reg_field), .compare_value(exp_data));
      // Clear interrupt_enable
      csr_wr(.ptr(ral.intr_enable), .value(32'd0));
      ral.ctrl.edn_enable.set(prim_mubi_pkg::MuBi4False);
      ral.ctrl.cmd_fifo_rst.set(prim_mubi_pkg::MuBi4True);
      csr_update(.csr(ral.ctrl));
      // Expect/Clear interrupt bit
      check_interrupts(.interrupts((1 << FifoErr)), .check_set(1'b1));
    end
  endtask // force_path_err

  // Find the first or last index in the original string that the target character appears
  function automatic int find_index (byte target, string original_str, string which_index);
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
endclass : edn_base_vseq
