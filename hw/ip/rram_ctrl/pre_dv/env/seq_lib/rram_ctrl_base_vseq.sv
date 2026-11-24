// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rram_ctrl_base_vseq extends cip_base_vseq #(
    .RAL_T               (rram_ctrl_core_reg_block),
    .CFG_T               (rram_ctrl_env_cfg),
    .COV_T               (rram_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T (rram_ctrl_virtual_sequencer)
  );
  `uvm_object_utils(rram_ctrl_base_vseq)

  rram_macro_prim_reg_block prim_ral;

  // Timeout of a host read. It matches the longest time the host can wait, which is while the
  // controller finishes a write operation.
  uint host_read_timeout_ns = 1_000_000;  // 1ms

  // Prevents multiple concurrent operations on the controller interface. Taken when an operation
  // starts and released by rram_ctrl_wait_op_done().
  semaphore ctrl_port_task_guard;

  // Standard SV/UVM methods
  extern function new(string name="");

  // Class specific methods
  extern function void set_handles();

  // Apply reset to both the primary and OTP clock domains in parallel so that both clock
  // generators get their reset.
  extern virtual task apply_reset(string kind = "HARD");

  // The base apply_resets_concurrently() only resets cfg.clk_rst_vifs, which excludes
  // otp_clk_rst_vif. Reset it here too so both domains stay in sync during rand-reset stress.
  extern virtual task apply_resets_concurrently(int reset_duration_ps = 0);

  // Resets the DUT and brings the RRAM controller out of reset.
  extern task dut_init(string reset_kind = "HARD");

  // Initializes the RRAM controller.
  // - waits for the phy to be initialized
  // - zeroes the data and info arrays through the backdoor, unless skipped
  // - starts the controller's init sequence that reads the scrambling keys from otp_ctrl, unless
  //   skipped. Without this initialization, no software/host access is granted.
  extern task rram_ctrl_init();

  // Returns the current configuration of the page that holds bus word `word_offset` of an
  // operation starting at byte address `addr`.
  extern function page_cfg_t get_current_page_cfg(addr_t      addr,
                                                  int         word_offset,
                                                  rram_part_e partition);

  // Waits until the scoreboard has seen the last configuration write and the memory protection
  // model reflects it.
  extern task wait_mp_model_update();

  // Configures the default region.
  extern task update_default_region_cfg(mubi4_t wr_en,
                                        mubi4_t rd_en,
                                        mubi4_t scramble_en,
                                        mubi4_t ecc_en);

  // Configures info page `info_page`.
  extern task update_info_page_cfg(uint    info_page,
                                   mubi4_t en,
                                   mubi4_t wr_en,
                                   mubi4_t rd_en,
                                   mubi4_t scramble_en,
                                   mubi4_t ecc_en);

  // Configures memory protection region `region` to cover `page_size` + 1 pages starting at page
  // `page_base`.
  extern task update_mp_region(uint    region,
                               uint    page_base,
                               uint    page_size,
                               mubi4_t en,
                               mubi4_t wr_en,
                               mubi4_t rd_en,
                               mubi4_t scramble_en,
                               mubi4_t ecc_en);

  // Starts operation `ctrl_op` on the controller interface.
  extern task rram_ctrl_start_op(rram_ctrl_op_t ctrl_op);

  // Waits for the current controller operation to complete, then clears op_status.done and
  // releases the controller interface.
  extern task rram_ctrl_wait_op_done();

  // Waits until the phy has completed all pending writes.
  extern task rram_ctrl_wait_wr_done();

  // Writes `data` through the controller interface.
  //
  // If `wr_check` is set, the data in the RRAM is checked through the backdoor once the write
  // completed. Words after the first one without write permission must keep their previous
  // value, since the operation stops there.
  extern task rram_ctrl_write(rram_ctrl_op_t ctrl_op,
                              data_q_t       data,
                              bit            wr_check = 1'b1);

  // Reads `data` through the controller interface.
  //
  // If `rd_check` is set, the data is checked against the RRAM contents read through the
  // backdoor. Words from the first one without read permission onwards must read as all ones.
  extern task rram_ctrl_read(rram_ctrl_op_t ctrl_op,
                             ref data_q_t   data,
                             input bit      rd_check = 1'b1);

  // Issues a rewrite of the RRAM word at byte address `addr` through the controller interface.
  extern task rram_ctrl_rewrite(addr_t addr, rram_part_e partition);

  // Reads the data word at `addr` through the host interface.
  //
  // The scoreboard predicts errors from the memory protection configuration. If `check_rdata` is
  // set, the read data is compared against `exp_rdata`.
  extern task rram_host_read(addr_t      addr,
                             bit         blocking = 0,
                             bit         check_rdata = 0,
                             data_t      exp_rdata = '0,
                             mubi4_t     instr_type = MuBi4False,
                             output data_t rdata,
                             output bit    completed);

  // Returns the data expected for a host read of every word of `ctrl_op`, which must address the
  // data partition. Words without host read permission read as all ones.
  extern function data_q_t get_exp_host_data(rram_ctrl_op_t ctrl_op);

  // Sends the Init command on the OTP macro interface. otp_ctrl does this once before any other
  // command.
  extern task otp_init();

  // Reads `otp_size` + 1 OTP words starting at `otp_addr` through the OTP macro interface.
  // If `rd_check` is set, checks the data and the error against the backdoor contents.
  extern task otp_read(otp_ctrl_macro_pkg::otp_macro_addr_t otp_addr,
                       otp_ctrl_macro_pkg::otp_macro_size_t otp_size,
                       bit                                  raw,
                       bit                                  rd_check,
                       output otp_ctrl_macro_pkg::otp_macro_data_t rdata);

  // Writes `otp_size` + 1 OTP words starting at `otp_addr` through the OTP macro interface.
  // OTP bits can only be set. If `wr_check` is set, checks the data, the error and, unless `raw`
  // is set, the integrity against the backdoor contents.
  extern task otp_write(otp_ctrl_macro_pkg::otp_macro_addr_t otp_addr,
                        otp_ctrl_macro_pkg::otp_macro_size_t otp_size,
                        bit                                  raw,
                        bit                                  wr_check,
                        otp_ctrl_macro_pkg::otp_macro_data_t otp_wdata);

  // Zeroizes, i.e. sets all bits of, `otp_size` + 1 OTP words starting at `otp_addr` through the
  // OTP macro interface. If `rd_check` is set, checks the result.
  extern task otp_zeroize(otp_ctrl_macro_pkg::otp_macro_addr_t otp_addr,
                          otp_ctrl_macro_pkg::otp_macro_size_t otp_size,
                          bit                                  rd_check,
                          output otp_ctrl_macro_pkg::otp_macro_data_t rdata);

  // Sends an RMA request with a random seed and waits for its acknowledgement.
  extern task rma_req();

endclass : rram_ctrl_base_vseq

function rram_ctrl_base_vseq::new(string name="");
  super.new(name);
  ctrl_port_task_guard = new(1);
endfunction : new

function void rram_ctrl_base_vseq::set_handles();
  super.set_handles();
  `downcast(prim_ral, cfg.ral_models[cfg.prim_ral_name]);
endfunction : set_handles

task rram_ctrl_base_vseq::apply_reset(string kind = "HARD");
  fork
    super.apply_reset(kind);
    cfg.otp_clk_rst_vif.apply_reset();
  join
endtask : apply_reset

task rram_ctrl_base_vseq::apply_resets_concurrently(int reset_duration_ps = 0);
  cfg.otp_clk_rst_vif.drive_rst_pin(0);
  super.apply_resets_concurrently(cfg.otp_clk_rst_vif.clk_period_ps);
  cfg.otp_clk_rst_vif.drive_rst_pin(1);
endtask : apply_resets_concurrently

task rram_ctrl_base_vseq::dut_init(string reset_kind = "HARD");
  // Run super.dut_init() first so rram_ctrl_init() always starts from a DUT that has just
  // settled out of reset.
  super.dut_init(reset_kind);
  rram_ctrl_init();
  // The OTP interface only answers the Init command once the phy has initialized.
  if (do_apply_reset) otp_init();
endtask : dut_init

task rram_ctrl_base_vseq::rram_ctrl_init();
  // poll phy_init_done
  csr_spinwait(.ptr(ral.phy_status.init_done), .exp_data(1'b1));

  `uvm_info(`gfn, "Initializing the RRAM arrays", UVM_MEDIUM)
  // Zero the arrays, so that every word holds valid ECC. The data partition stores bus words
  // infected with their address, while the OTP pages store raw data and integrity, for which
  // all zeroes is consistent.
  if (!cfg.skip_init_data_array) begin
    for (int unsigned w = 0; w < TotalDataPages * WordsPerPage; w++) begin
      if (w < OtpStartPage * WordsPerPage) begin
        cfg.rram_bkdr_word_write(w, RramPartData, '0, 1'b0);
      end else begin
        cfg.mem_bkdr_util_h[RramPartData].write128(w << DataByteWidth, '0);
      end
    end
  end
  if (!cfg.skip_init_info_array) begin
    for (int unsigned w = 0; w < TotalInfoPages * WordsPerPage; w++) begin
      cfg.rram_bkdr_word_write(w, RramPartInfo, '0, 1'b0);
    end
  end

  if (!cfg.skip_lc_init) begin
    `uvm_info(`gfn, "Initializing the controller", UVM_MEDIUM)
    // initialize controller
    csr_wr(.ptr(ral.init), .value('b1));

    // poll init_done
    csr_spinwait(.ptr(ral.status.init_done), .exp_data(1'b1));
  end
endtask : rram_ctrl_init

function page_cfg_t rram_ctrl_base_vseq::get_current_page_cfg(addr_t      addr,
                                                              int         word_offset,
                                                              rram_part_e partition);
  return cfg.mp_model.get_sw_page_cfg(partition, cfg.get_page(addr + word_offset * BusBytes));
endfunction : get_current_page_cfg

task rram_ctrl_base_vseq::wait_mp_model_update();
  // The TL monitor publishes the response in the same cycle csr_wr() returns, so wait for the
  // scoreboard to process it.
  cfg.clk_rst_vif.wait_clks(1);
endtask : wait_mp_model_update

task rram_ctrl_base_vseq::update_default_region_cfg(mubi4_t wr_en,
                                                    mubi4_t rd_en,
                                                    mubi4_t scramble_en,
                                                    mubi4_t ecc_en);
  uvm_reg_data_t data = '0;
  data = get_csr_val_with_updated_field(ral.default_region.wr_en, data, wr_en);
  data = get_csr_val_with_updated_field(ral.default_region.rd_en, data, rd_en);
  data = get_csr_val_with_updated_field(ral.default_region.scramble_en, data, scramble_en);
  data = get_csr_val_with_updated_field(ral.default_region.ecc_en, data, ecc_en);
  csr_wr(.ptr(ral.default_region), .value(data));
  wait_mp_model_update();
endtask : update_default_region_cfg

task rram_ctrl_base_vseq::update_info_page_cfg(uint    info_page,
                                               mubi4_t en,
                                               mubi4_t wr_en,
                                               mubi4_t rd_en,
                                               mubi4_t scramble_en,
                                               mubi4_t ecc_en);
  uvm_reg_data_t data = '0;
  `DV_CHECK_LT(info_page, TotalInfoPages)
  data = get_csr_val_with_updated_field(ral.info_page_cfg[info_page].en, data, en);
  data = get_csr_val_with_updated_field(ral.info_page_cfg[info_page].wr_en, data, wr_en);
  data = get_csr_val_with_updated_field(ral.info_page_cfg[info_page].rd_en, data, rd_en);
  data = get_csr_val_with_updated_field(ral.info_page_cfg[info_page].scramble_en, data,
                                        scramble_en);
  data = get_csr_val_with_updated_field(ral.info_page_cfg[info_page].ecc_en, data, ecc_en);
  csr_wr(.ptr(ral.info_page_cfg[info_page]), .value(data));
  wait_mp_model_update();
endtask : update_info_page_cfg

task rram_ctrl_base_vseq::update_mp_region(uint    region,
                                           uint    page_base,
                                           uint    page_size,
                                           mubi4_t en,
                                           mubi4_t wr_en,
                                           mubi4_t rd_en,
                                           mubi4_t scramble_en,
                                           mubi4_t ecc_en);
  uvm_reg_data_t data = '0;
  `DV_CHECK_LT(region, MpRegions)
  `DV_CHECK_LT(page_base + page_size, TotalDataPages)

  data = get_csr_val_with_updated_field(ral.mp_region_cfg[region].en, data, en);
  data = get_csr_val_with_updated_field(ral.mp_region_cfg[region].wr_en, data, wr_en);
  data = get_csr_val_with_updated_field(ral.mp_region_cfg[region].rd_en, data, rd_en);
  data = get_csr_val_with_updated_field(ral.mp_region_cfg[region].scramble_en, data, scramble_en);
  data = get_csr_val_with_updated_field(ral.mp_region_cfg[region].ecc_en, data, ecc_en);
  csr_wr(.ptr(ral.mp_region_cfg[region]), .value(data));

  data = '0;
  data = get_csr_val_with_updated_field(ral.mp_region[region].base, data, page_base);
  data = get_csr_val_with_updated_field(ral.mp_region[region].size, data, page_size);
  csr_wr(.ptr(ral.mp_region[region]), .value(data));
  wait_mp_model_update();
endtask : update_mp_region

task rram_ctrl_base_vseq::rram_ctrl_start_op(rram_ctrl_op_t ctrl_op);
  uvm_reg_data_t data = '0;
  ctrl_port_task_guard.get(1);
  csr_wr(.ptr(ral.addr), .value(ctrl_op.addr));
  data = get_csr_val_with_updated_field(ral.control.start, data, 1'b1);
  data = get_csr_val_with_updated_field(ral.control.op, data, ctrl_op.op);
  data = get_csr_val_with_updated_field(ral.control.partition, data, ctrl_op.partition);
  data = get_csr_val_with_updated_field(ral.control.num, data, ctrl_op.num_words);
  csr_wr(.ptr(ral.control), .value(data));
endtask : rram_ctrl_start_op

task rram_ctrl_base_vseq::rram_ctrl_wait_op_done();
  csr_spinwait(.ptr(ral.op_status.done), .exp_data(1'b1));
  csr_wr(.ptr(ral.op_status), .value('0));
  ctrl_port_task_guard.put(1);
endtask : rram_ctrl_wait_op_done

task rram_ctrl_base_vseq::rram_ctrl_wait_wr_done();
  csr_spinwait(.ptr(ral.phy_status.wr_busy), .exp_data(1'b0));
endtask : rram_ctrl_wait_wr_done

task rram_ctrl_base_vseq::rram_ctrl_write(rram_ctrl_op_t ctrl_op,
                                          data_q_t       data,
                                          bit            wr_check = 1'b1);
  uvm_reg_data_t wr_fifo_level;
  data_q_t       exp_data;
  bit            exp_err;

  // Words from the first one without write permission onwards keep their previous value. Those
  // are only known once the phy has finished any write still pending from an earlier operation.
  for (int i = 0; i <= ctrl_op.num_words; i++) begin
    page_cfg_t page_cfg = get_current_page_cfg(ctrl_op.addr, i, ctrl_op.partition);
    if ((page_cfg.en != MuBi4True) || (page_cfg.wr_en != MuBi4True)) begin
      exp_err = 1'b1;
      break;
    end
  end
  if (exp_err) begin
    cfg.misc_vif.wait_nvm_idle();
    exp_data = cfg.rram_bkdr_mem_read(ctrl_op, 1'b0, 1'b1);
  end
  for (int i = 0; i <= ctrl_op.num_words; i++) begin
    page_cfg_t page_cfg = get_current_page_cfg(ctrl_op.addr, i, ctrl_op.partition);
    if ((page_cfg.en != MuBi4True) || (page_cfg.wr_en != MuBi4True)) break;
    if (exp_err) exp_data[i] = data[i];
    else         exp_data.push_back(data[i]);
  end

  rram_ctrl_start_op(ctrl_op);

  // Fill the write FIFO, waiting for space whenever it is full.
  wr_fifo_level = 0;
  for (int i = 0; i <= ctrl_op.num_words; i++) begin
    while (wr_fifo_level >= cfg.m_wr_fifo_depth - 1) begin
      csr_rd(.ptr(ral.curr_fifo_lvl.wr), .value(wr_fifo_level));
    end
    mem_wr(.ptr(ral.wr_fifo), .offset(0), .data(data[i]));
    wr_fifo_level++;
  end

  rram_ctrl_wait_op_done();

  // Check the RRAM contents in the background, once the phy has written all data.
  if (wr_check) begin
    fork begin
      automatic rram_ctrl_op_t bkdr_op       = ctrl_op;
      automatic data_q_t       bkdr_exp_data = exp_data;
      data_q_t                 bkdr_data;
      cfg.misc_vif.wait_nvm_idle();
      bkdr_data = cfg.rram_bkdr_mem_read(bkdr_op, 1'b0, 1'b1);
      foreach (bkdr_exp_data[i]) begin
        `DV_CHECK_EQ(bkdr_data[i], bkdr_exp_data[i],
                     $sformatf("Write of word %0d of op %p", i, bkdr_op))
      end
    end join_none
  end
endtask : rram_ctrl_write

task rram_ctrl_base_vseq::rram_ctrl_rewrite(addr_t addr, rram_part_e partition);
  rram_ctrl_op_t ctrl_op;
  ctrl_op.op        = RramOpRewrite;
  ctrl_op.partition = partition;
  ctrl_op.addr      = addr;
  ctrl_op.num_words = WidthMultiple - 1;
  rram_ctrl_start_op(ctrl_op);
  rram_ctrl_wait_op_done();
endtask : rram_ctrl_rewrite

task rram_ctrl_base_vseq::rram_ctrl_read(rram_ctrl_op_t ctrl_op,
                                         ref data_q_t   data,
                                         input bit      rd_check = 1'b1);
  uvm_reg_data_t rd_fifo_level;
  data_q_t       exp_data;
  bit            exp_err;

  rram_ctrl_start_op(ctrl_op);

  // Drain the read FIFO, waiting for data whenever it is empty.
  data = {};
  rd_fifo_level = 0;
  for (int i = 0; i <= ctrl_op.num_words; i++) begin
    data_t rdata;
    while (rd_fifo_level == 0) begin
      csr_rd(.ptr(ral.curr_fifo_lvl.rd), .value(rd_fifo_level));
    end
    mem_rd(.ptr(ral.rd_fifo), .offset(0), .data(rdata));
    rd_fifo_level--;
    data.push_back(rdata);
  end

  rram_ctrl_wait_op_done();

  // The read data must match what is stored once the operation completed. A write from an
  // earlier operation may still have been pending in the phy when this one started, and the
  // read returns the data of that write.
  if (rd_check) begin
    cfg.misc_vif.wait_nvm_idle();
    exp_data = cfg.rram_bkdr_mem_read(ctrl_op, 1'b0, 1'b1);
    foreach (data[i]) begin
      page_cfg_t page_cfg = get_current_page_cfg(ctrl_op.addr, i, ctrl_op.partition);
      exp_err |= (page_cfg.en != MuBi4True) || (page_cfg.rd_en != MuBi4True);
      `DV_CHECK_EQ(data[i], exp_err ? data_t'('1) : exp_data[i],
                   $sformatf("Read of word %0d of op %p", i, ctrl_op))
    end
  end
endtask : rram_ctrl_read

task rram_ctrl_base_vseq::rram_host_read(addr_t      addr,
                                         bit         blocking = 0,
                                         bit         check_rdata = 0,
                                         data_t      exp_rdata = '0,
                                         mubi4_t     instr_type = MuBi4False,
                                         output data_t rdata,
                                         output bit    completed);
  bit saw_err;
  // Errors are predicted and checked by the scoreboard, so don't check them here.
  tl_access_w_abort(.addr(addr), .write(1'b0), .data(rdata), .completed(completed),
                    .saw_err(saw_err), .tl_access_timeout_ns(host_read_timeout_ns),
                    .check_err_rsp(1'b0), .check_exp_data(check_rdata), .exp_data(exp_rdata),
                    .blocking(blocking), .instr_type(instr_type),
                    .tl_sequencer_h(p_sequencer.tl_sequencer_hs[cfg.host_ral_name]));
endtask : rram_host_read

function data_q_t rram_ctrl_base_vseq::get_exp_host_data(rram_ctrl_op_t ctrl_op);
  data_q_t exp_data;
  `DV_CHECK_EQ(ctrl_op.partition, RramPartData)
  exp_data = cfg.rram_bkdr_mem_read(ctrl_op, 1'b0, 1'b1);
  foreach (exp_data[i]) begin
    if (!cfg.mp_model.host_rd_allowed(cfg.get_page(ctrl_op.addr + i * BusBytes))) begin
      exp_data[i] = '1;
    end
  end
  return exp_data;
endfunction : get_exp_host_data

task rram_ctrl_base_vseq::otp_init();
  otp_ctrl_macro_pkg::otp_macro_data_t rdata;
  otp_ctrl_macro_pkg::err_e            err;
  `uvm_info(`gfn, "Sending the OTP Init command", UVM_MEDIUM)
  cfg.otp_macro_vif.send(otp_ctrl_macro_pkg::Init, '0, '0, '0, rdata, err);
  `DV_CHECK_EQ(err, otp_ctrl_macro_pkg::NoError, "OTP Init command")
endtask : otp_init

task rram_ctrl_base_vseq::otp_read(otp_ctrl_macro_pkg::otp_macro_addr_t otp_addr,
                                   otp_ctrl_macro_pkg::otp_macro_size_t otp_size,
                                   bit                                  raw,
                                   bit                                  rd_check,
                                   output otp_ctrl_macro_pkg::otp_macro_data_t rdata);
  otp_ctrl_macro_pkg::err_e err;
  cfg.otp_macro_vif.send(raw ? otp_ctrl_macro_pkg::ReadRaw : otp_ctrl_macro_pkg::Read, otp_addr,
                         otp_size, '0, rdata, err);
  `uvm_info(`gfn, $sformatf("OTP read: addr=0x%0x size=%0d raw=%0b rdata=0x%0x err=%s",
                            otp_addr, otp_size, raw, rdata, err.name()), UVM_MEDIUM)

  if (rd_check) begin
    otp_ctrl_macro_pkg::otp_macro_data_t exp_rdata;
    bit                                  intg_err;
    cfg.otp_bkdr_read(otp_addr, otp_size, exp_rdata, intg_err);
    `DV_CHECK_EQ(err, (intg_err && !raw) ? otp_ctrl_macro_pkg::MacroEccUncorrError :
                                           otp_ctrl_macro_pkg::NoError,
                 $sformatf("OTP read error: addr=0x%0x size=%0d", otp_addr, otp_size))
    `DV_CHECK_EQ(rdata, exp_rdata,
                 $sformatf("OTP read data: addr=0x%0x size=%0d", otp_addr, otp_size))
  end
endtask : otp_read

task rram_ctrl_base_vseq::otp_write(otp_ctrl_macro_pkg::otp_macro_addr_t otp_addr,
                                    otp_ctrl_macro_pkg::otp_macro_size_t otp_size,
                                    bit                                  raw,
                                    bit                                  wr_check,
                                    otp_ctrl_macro_pkg::otp_macro_data_t otp_wdata);
  otp_ctrl_macro_pkg::otp_macro_data_t init_data, rdata, post_data;
  otp_ctrl_macro_pkg::err_e            err;
  bit                                  intg_err;

  cfg.otp_bkdr_read(otp_addr, otp_size, init_data, intg_err);
  cfg.otp_macro_vif.send(raw ? otp_ctrl_macro_pkg::WriteRaw : otp_ctrl_macro_pkg::Write,
                         otp_addr, otp_size, otp_wdata, rdata, err);
  `uvm_info(`gfn, $sformatf("OTP write: addr=0x%0x size=%0d raw=%0b wdata=0x%0x err=%s",
                            otp_addr, otp_size, raw, otp_wdata, err.name()), UVM_MEDIUM)

  if (wr_check) begin
    // Bits can only be set. Writing data that would clear a set bit is flagged as an error, but
    // the set bits are still written.
    bit blank_err = (init_data & otp_wdata) != init_data;
    cfg.otp_bkdr_read(otp_addr, otp_size, post_data, intg_err);
    `DV_CHECK_EQ(err, blank_err ? otp_ctrl_macro_pkg::MacroWriteBlankError :
                                  otp_ctrl_macro_pkg::NoError,
                 $sformatf("OTP write error: addr=0x%0x size=%0d", otp_addr, otp_size))
    `DV_CHECK_EQ(post_data, init_data | otp_wdata,
                 $sformatf("OTP write data: addr=0x%0x size=%0d", otp_addr, otp_size))
    if (!raw) begin
      `DV_CHECK_EQ(intg_err, 1'b0,
                   $sformatf("OTP write integrity: addr=0x%0x size=%0d", otp_addr, otp_size))
    end
  end
endtask : otp_write

task rram_ctrl_base_vseq::otp_zeroize(otp_ctrl_macro_pkg::otp_macro_addr_t otp_addr,
                                      otp_ctrl_macro_pkg::otp_macro_size_t otp_size,
                                      bit                                  rd_check,
                                      output otp_ctrl_macro_pkg::otp_macro_data_t rdata);
  otp_ctrl_macro_pkg::err_e err;
  cfg.otp_macro_vif.send(otp_ctrl_macro_pkg::Zeroize, otp_addr, otp_size, '0, rdata, err);
  `uvm_info(`gfn, $sformatf("OTP zeroize: addr=0x%0x size=%0d rdata=0x%0x err=%s",
                            otp_addr, otp_size, rdata, err.name()), UVM_MEDIUM)

  if (rd_check) begin
    otp_ctrl_macro_pkg::otp_macro_data_t exp_rdata, bkdr_data;
    bit                                  intg_err;
    exp_rdata = '0;
    for (int k = 0; k <= otp_size; k++) begin
      exp_rdata[k * otp_ctrl_macro_pkg::OtpWidth +: otp_ctrl_macro_pkg::OtpWidth] = '1;
    end
    cfg.otp_bkdr_read(otp_addr, otp_size, bkdr_data, intg_err);
    `DV_CHECK_EQ(err, otp_ctrl_macro_pkg::NoError,
                 $sformatf("OTP zeroize error: addr=0x%0x size=%0d", otp_addr, otp_size))
    `DV_CHECK_EQ(rdata, exp_rdata,
                 $sformatf("OTP zeroize read-back: addr=0x%0x size=%0d", otp_addr, otp_size))
    `DV_CHECK_EQ(bkdr_data, exp_rdata,
                 $sformatf("OTP zeroize data: addr=0x%0x size=%0d", otp_addr, otp_size))
  end
endtask : otp_zeroize

task rram_ctrl_base_vseq::rma_req();
  // An RMA wipes the whole data partition, which takes approximately 100ms with a 100MHz OTP
  // clock. Allow twice that.
  time timeout = (20_000 / cfg.otp_clk_rst_vif.clk_freq_mhz) * 1ms;

  cfg.mp_model.rma_requested = 1'b1;
  cfg.misc_vif.cb.rma_seed <= $urandom();
  cfg.misc_vif.cb.rma_req  <= On;
  `uvm_info(`gfn, "Waiting for RMA to complete", UVM_LOW)

  fork
    begin
      // Poll infrequently, since the RMA takes long.
      do begin
        #10ms;
        @(cfg.misc_vif.cb);
      end while (cfg.misc_vif.cb.rma_ack != On);
    end
    begin
      #(timeout);
      `uvm_error(`gfn, $sformatf("RMA was not acknowledged within %0t", timeout))
    end
  join_any
  disable fork;

  // The RMA state machine stays in its final state until reset.
  `uvm_info(`gfn, "RMA complete", UVM_LOW)
endtask : rma_req
