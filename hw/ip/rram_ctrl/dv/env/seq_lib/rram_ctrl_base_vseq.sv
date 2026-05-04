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

  uint write_timeout_ns = 1_000_000;  // 1ms

  logic [KeyWidth-1:0] otp_addr_key;
  logic [KeyWidth-1:0] otp_addr_rand_key;
  logic [KeyWidth-1:0] otp_data_key;
  logic [KeyWidth-1:0] otp_data_rand_key;

  // Standard SV/UVM methods
  extern function new(string name="");

  // Class specific methods
  extern function void set_handles();

  // helper functions
  extern function automatic void update_data_regions();
  extern function automatic page_cfg_t get_current_page_cfg(addr_t addr,
                                                            int word_offset,
                                                            rram_part_e partition);

  extern task pre_start();
  extern task dut_init(string reset_kind = "HARD");
  extern task update_default_region_cfg(input prim_mubi_pkg::mubi4_t wr_en,
                                        input prim_mubi_pkg::mubi4_t rd_en,
                                        input prim_mubi_pkg::mubi4_t scramble_en,
                                        input prim_mubi_pkg::mubi4_t ecc_en);

  extern task update_info_page_cfg(input uint info_page,
                                   input prim_mubi_pkg::mubi4_t en,
                                   input prim_mubi_pkg::mubi4_t wr_en,
                                   input prim_mubi_pkg::mubi4_t rd_en,
                                   input prim_mubi_pkg::mubi4_t scramble_en,
                                   input prim_mubi_pkg::mubi4_t ecc_en);

  extern task update_mp_region(input uint region,
                               input uint page_base,
                               input uint page_size,
                               input prim_mubi_pkg::mubi4_t en,
                               input prim_mubi_pkg::mubi4_t wr_en,
                               input prim_mubi_pkg::mubi4_t rd_en,
                               input prim_mubi_pkg::mubi4_t scramble_en,
                               input prim_mubi_pkg::mubi4_t ecc_en);
  extern task rram_ctrl_init();
  extern task rram_ctrl_write(input rram_ctrl_op_t ctrl_op,
                              input data_q_t data,
                              input logic wr_check = 1'b1);
  extern task rram_ctrl_read(input rram_ctrl_op_t ctrl_op,
                             ref data_q_t data,
                             input logic rd_check = 1'b1);
  extern task rram_ctrl_rewrite(input addr_t addr,
                                input rram_part_e partition);
  extern task rram_ctrl_wait_op_done();
  extern task rram_ctrl_wait_wr_done();
  extern task rram_host_read(input  addr_t addr,
                             input  bit blocking = 0,
                             input  bit check_rdata = 0,
                             input  data_t exp_rdata = '0,
                             input  prim_mubi_pkg::mubi4_t instr_type = prim_mubi_pkg::MuBi4False,
                             output data_t rdata,
                             output bit completed,
                             input  bit exp_err_rsp = 0
                            );

  // semaphore to prevent multiple concurrent accesses to the control port
  semaphore ctrl_port_task_guard;

endclass : rram_ctrl_base_vseq


function rram_ctrl_base_vseq::new(string name="");
  super.new(name);
  ctrl_port_task_guard = new(1);
endfunction : new

function void rram_ctrl_base_vseq::set_handles();
  super.set_handles();
  `downcast(prim_ral, cfg.ral_models[cfg.prim_ral_name]);
endfunction : set_handles

// setup inputs for DUT
task rram_ctrl_base_vseq::pre_start();

    // Create key before mem init
    otp_addr_key      = {$urandom, $urandom, $urandom, $urandom};
    otp_addr_rand_key = {$urandom, $urandom, $urandom, $urandom};
    otp_data_key      = {$urandom, $urandom, $urandom, $urandom};
    otp_data_rand_key = {$urandom, $urandom, $urandom, $urandom};

    cfg.otp_addr_key = otp_addr_key;
    cfg.otp_data_key = otp_data_key;

    cfg.misc_vif.rma_req  <= lc_ctrl_pkg::Off;
    cfg.misc_vif.rma_seed <= lc_ctrl_pkg::LC_NVM_RMA_SEED_DEFAULT;

    cfg.misc_vif.otp_macro_req.valid = '0;
    cfg.misc_vif.otp_macro_req.cmd   = otp_ctrl_macro_pkg::Init;
    cfg.misc_vif.otp_macro_req.addr  = '0;
    cfg.misc_vif.otp_macro_req.size  = '0;
    cfg.misc_vif.otp_macro_req.wdata = '0;

    super.pre_start();

endtask : pre_start

// initializes the DUT
task rram_ctrl_base_vseq::dut_init(string reset_kind = "HARD");

  super.dut_init();

  rram_ctrl_init();
endtask : dut_init

task rram_ctrl_base_vseq::rram_ctrl_init();
  uvm_reg_data_t reg_data;
  bit init_done;

  rram_ctrl_op_t ctrl_op_init;
  data_q_t init_data;

  // poll phy_init_done
  do begin
    csr_rd(.ptr(ral.phy_status), .value(reg_data));
    init_done = get_field_val(ral.phy_status.init_done, reg_data);
    #1us;
  end while (init_done == 1'b0);

  init_data = '{(BusWordsPerPage){0}};
  if (cfg.skip_init_data_array == 1'b0) begin
    // Initialize full RRAM data array to all zero
    ctrl_op_init.num_words = BusWordsPerPage - 1;
    ctrl_op_init.op = RramOpWrite;
    for (int i = 0; i < DataPages; i++) begin
      ctrl_op_init.partition = RramPartData;
      ctrl_op_init.addr = i << (BusAddrByteW - PageW);
      cfg.rram_bkdr_mem_write(ctrl_op_init, init_data, 1'b0);
    end
  end
  if (cfg.skip_init_info_array == 1'b0) begin
    // Initialize full RRAM info array to all zero
    for (int i = 0; i < TotalInfoPages; i++) begin
      ctrl_op_init.partition = RramPartInfo;
      ctrl_op_init.addr = i << (BusAddrByteW - PageW);
      cfg.rram_bkdr_mem_write(ctrl_op_init, init_data, 1'b0);
    end
  end
endtask : rram_ctrl_init

// update data regions with access permission and scrambling, ecc configurations
function automatic void rram_ctrl_base_vseq::update_data_regions();
  for (int i = 0; i < TotalPages; i++) begin
    // No access to OTP pages
    if (i >= OtpStartPage) begin
      cfg.data_pages_cfg[i].scramble_en = MuBi4False;
      cfg.data_pages_cfg[i].ecc_en      = MuBi4True;
      cfg.data_pages_cfg[i].rd_en       = MuBi4False;
      cfg.data_pages_cfg[i].wr_en       = MuBi4False;
    end else begin
      cfg.data_pages_cfg[i].scramble_en = cfg.default_cfg.scramble_en;
      cfg.data_pages_cfg[i].ecc_en      = cfg.default_cfg.ecc_en;
      cfg.data_pages_cfg[i].rd_en       = cfg.default_cfg.rd_en;
      cfg.data_pages_cfg[i].wr_en       = cfg.default_cfg.wr_en;
      for (int k = 0; k < MpRegions; k++) begin
        if (cfg.mp_regions[k].cfg.en == prim_mubi_pkg::MuBi4True) begin
          if ((i >= cfg.mp_regions[k].base) &&
              (i <= cfg.mp_regions[k].base + cfg.mp_regions[k].size)) begin
            cfg.data_pages_cfg[i].scramble_en = cfg.mp_regions[k].cfg.scramble_en;
            cfg.data_pages_cfg[i].ecc_en      = cfg.mp_regions[k].cfg.ecc_en;
            cfg.data_pages_cfg[i].rd_en       = cfg.mp_regions[k].cfg.rd_en;
            cfg.data_pages_cfg[i].wr_en       = cfg.mp_regions[k].cfg.wr_en;
            break;
          end
        end
      end
    end
  end
endfunction : update_data_regions

// get current page configuration at addr + word_offset
function automatic page_cfg_t rram_ctrl_base_vseq::get_current_page_cfg(addr_t addr,
                                                                        int word_offset,
                                                                        rram_part_e partition);
  addr_t     current_addr;
  int        current_page;
  page_cfg_t current_cfg;

  current_addr = addr + word_offset*4;
  current_page = current_addr[BusAddrByteW-1 -: PageW];
  current_cfg  = partition == RramPartData ? cfg.data_pages_cfg[current_page] :
                                             cfg.info_pages_cfg[current_page];
  return current_cfg;
endfunction : get_current_page_cfg

task rram_ctrl_base_vseq::update_default_region_cfg(input prim_mubi_pkg::mubi4_t wr_en,
                                                    input prim_mubi_pkg::mubi4_t rd_en,
                                                    input prim_mubi_pkg::mubi4_t scramble_en,
                                                    input prim_mubi_pkg::mubi4_t ecc_en);
  uvm_reg_data_t data;
  data = 0;
  data = get_csr_val_with_updated_field(ral.default_region.wr_en, data, wr_en);
  data = get_csr_val_with_updated_field(ral.default_region.rd_en, data, rd_en);
  data = get_csr_val_with_updated_field(ral.default_region.scramble_en, data, scramble_en);
  data = get_csr_val_with_updated_field(ral.default_region.ecc_en, data, ecc_en);
  csr_wr(.ptr(ral.default_region), .value(data));

  // write default scrambling information to cfg and update all regions
  cfg.default_cfg.scramble_en = scramble_en;
  cfg.default_cfg.ecc_en = ecc_en;
  cfg.default_cfg.wr_en = wr_en;
  cfg.default_cfg.rd_en = rd_en;
  update_data_regions();
endtask : update_default_region_cfg

task rram_ctrl_base_vseq::update_info_page_cfg(input uint info_page,
                                               input prim_mubi_pkg::mubi4_t en,
                                               input prim_mubi_pkg::mubi4_t wr_en,
                                               input prim_mubi_pkg::mubi4_t rd_en,
                                               input prim_mubi_pkg::mubi4_t scramble_en,
                                               input prim_mubi_pkg::mubi4_t ecc_en);
  uvm_reg_data_t data;
  if (info_page >= TotalInfoPages) begin
    `uvm_error("info-page-cfg-error:", $sformatf("Cannot configure info page=%d",
                info_page));
  end
  // Update info page access config
  data = 0;
  data = get_csr_val_with_updated_field(ral.info_page_cfg[0].en, data, en);
  data = get_csr_val_with_updated_field(ral.info_page_cfg[0].wr_en, data, wr_en);
  data = get_csr_val_with_updated_field(ral.info_page_cfg[0].rd_en, data, rd_en);
  data = get_csr_val_with_updated_field(ral.info_page_cfg[0].scramble_en, data, scramble_en);
  data = get_csr_val_with_updated_field(ral.info_page_cfg[0].ecc_en, data, ecc_en);
  csr_wr(.ptr(ral.info_page_cfg[info_page]), .value(data));

  // Update local struct
  cfg.info_pages_cfg[info_page].scramble_en = prim_mubi_pkg::mubi4_and_hi(en, scramble_en);
  cfg.info_pages_cfg[info_page].ecc_en      = prim_mubi_pkg::mubi4_and_hi(en, ecc_en);
  cfg.info_pages_cfg[info_page].rd_en       = prim_mubi_pkg::mubi4_and_hi(en, rd_en);
  cfg.info_pages_cfg[info_page].wr_en       = prim_mubi_pkg::mubi4_and_hi(en, wr_en);
endtask : update_info_page_cfg

task rram_ctrl_base_vseq::update_mp_region(input uint region,
                                           input uint page_base,
                                           input uint page_size,
                                           input prim_mubi_pkg::mubi4_t en,
                                           input prim_mubi_pkg::mubi4_t wr_en,
                                           input prim_mubi_pkg::mubi4_t rd_en,
                                           input prim_mubi_pkg::mubi4_t scramble_en,
                                           input prim_mubi_pkg::mubi4_t ecc_en);
  uvm_reg_data_t data;

  if ((page_base >= TotalPages) || ((page_base + page_size) >= TotalPages)) begin
    `uvm_error("mp-cfg-error:", $sformatf("Cannot configure page_base=%0d with page_size=%d",
               page_base, page_size));
  end

  // Update mp region with access config
  data = 0;
  data = get_csr_val_with_updated_field(ral.mp_region_cfg[0].en, data, en);
  data = get_csr_val_with_updated_field(ral.mp_region_cfg[0].wr_en, data, wr_en);
  data = get_csr_val_with_updated_field(ral.mp_region_cfg[0].rd_en, data, rd_en);
  data = get_csr_val_with_updated_field(ral.mp_region_cfg[0].scramble_en, data, scramble_en);
  data = get_csr_val_with_updated_field(ral.mp_region_cfg[0].ecc_en, data, ecc_en);
  csr_wr(.ptr(ral.mp_region_cfg[region]), .value(data));

  // Update mp region with page and size
  data = 0;
  data = get_csr_val_with_updated_field(ral.mp_region[0].base, data, page_base);
  data = get_csr_val_with_updated_field(ral.mp_region[0].size, data, page_size);
  csr_wr(.ptr(ral.mp_region[region]), .value(data));

  cfg.mp_regions[region].base            = page_base;
  cfg.mp_regions[region].size            = page_size;
  cfg.mp_regions[region].cfg.en          = en;
  cfg.mp_regions[region].cfg.rd_en       = rd_en;
  cfg.mp_regions[region].cfg.wr_en       = wr_en;
  cfg.mp_regions[region].cfg.scramble_en = scramble_en;
  cfg.mp_regions[region].cfg.ecc_en      = ecc_en;

  update_data_regions();
endtask : update_mp_region

task rram_ctrl_base_vseq::rram_ctrl_wait_op_done();
  uvm_reg_data_t reg_data;
  bit op_done;

  do begin // poll op_done
    csr_rd(.ptr(ral.op_status), .value(reg_data));
    op_done = get_field_val(ral.op_status.done, reg_data);
  end while (op_done == 1'b0);
  reg_data = get_csr_val_with_updated_field(ral.op_status.done, reg_data, 1'b0);
  csr_wr(.ptr(ral.op_status), .value(reg_data));
  ctrl_port_task_guard.put(1);
  @(posedge cfg.clk_rst_vif.clk);
endtask : rram_ctrl_wait_op_done

task rram_ctrl_base_vseq::rram_ctrl_wait_wr_done();
  uvm_reg_data_t reg_data;
  bit wr_busy;

  do begin // poll phy_status.wr_busy
    csr_rd(.ptr(ral.phy_status), .value(reg_data));
    wr_busy = get_field_val(ral.phy_status.wr_busy, reg_data);
  end while (wr_busy == 1'b1);
endtask : rram_ctrl_wait_wr_done

task rram_ctrl_base_vseq::rram_ctrl_write(input rram_ctrl_op_t ctrl_op, input data_q_t data,
                                          input logic wr_check = 1'b1);
  uvm_reg_data_t reg_data;
  int            wr_fifo_level;
  page_cfg_t     current_cfg;

  data_q_t init_data;
  logic exp_err = 1'b0;

  // prevent multiple function entries
  ctrl_port_task_guard.get(1);
  // write start address
  csr_wr(.ptr(ral.addr), .value(ctrl_op.addr));

  // write command register
  reg_data = '0;
  reg_data = get_csr_val_with_updated_field(ral.control.start, reg_data, 1'b1);
  reg_data = get_csr_val_with_updated_field(ral.control.op, reg_data, ctrl_op.op);
  reg_data = get_csr_val_with_updated_field(ral.control.partition, reg_data, ctrl_op.partition);
  reg_data = get_csr_val_with_updated_field(ral.control.num, reg_data, ctrl_op.num_words);
  csr_wr(.ptr(ral.control), .value(reg_data));

  // fill wr-fifo
  wr_fifo_level = 0;
  for (int i = 0; i <= ctrl_op.num_words; i++) begin
    current_cfg = get_current_page_cfg(ctrl_op.addr, i, ctrl_op.partition);
    if (wr_fifo_level == WrFifoDepth - 1) begin
      do begin // poll fifo until there is space available
        csr_rd(.ptr(ral.curr_fifo_lvl), .value(reg_data));
        wr_fifo_level = get_field_val(ral.curr_fifo_lvl.wr, reg_data);
      end while (wr_fifo_level == WrFifoDepth - 1);
    end
    mem_wr(.ptr(ral.wr_fifo), .offset(0), .data(data[i]));
    wr_fifo_level++;
    if ((current_cfg.wr_en != prim_mubi_pkg::MuBi4True) | exp_err) begin
      if (exp_err == 1'b0) init_data = cfg.rram_bkdr_mem_read(ctrl_op, 1'b0, 1'b1);
      data[i] = init_data[i];
      exp_err = 1'b1;
    end
  end
  if (wr_check) begin
    // start background check as soon as the current command has finished (ready is high)
    fork begin
      automatic rram_ctrl_op_t bkdr_ctrl_op = ctrl_op;
      automatic data_q_t wr_data = data;
      data_q_t bkdr_data;
      if (exp_err == '0) begin
        wait(cfg.misc_vif.pwr_nvm.nvm_idle === 1'b0);
      end
      wait(cfg.misc_vif.pwr_nvm.nvm_idle === 1'b1);
      repeat(2) @(posedge cfg.clk_rst_vif.clk);
      bkdr_data = cfg.rram_bkdr_mem_read(bkdr_ctrl_op, 1'b0, 1'b1);
      // check if read data matches with data in RRAM
      for (int i = 0; i <= bkdr_ctrl_op.num_words; i++) begin
        if (wr_data[i] !== bkdr_data[i]) begin
          `uvm_error("Write-error:", $sformatf("data[%0d] exp: %08x is: %08x", i, wr_data[i],
                     bkdr_data[i]))
        end
      end
    end
    join_none
  end
  // wait for command to complete
  rram_ctrl_wait_op_done();
endtask : rram_ctrl_write


task rram_ctrl_base_vseq::rram_ctrl_rewrite(input addr_t addr, input rram_part_e partition);

  uvm_reg_data_t reg_data;

  // prevent multiple function entries
  ctrl_port_task_guard.get(1);

  // write start address
  csr_wr(.ptr(ral.addr), .value(addr));

  // write command register
  reg_data = '0;
  reg_data = get_csr_val_with_updated_field(ral.control.start, reg_data, 1'b1);
  reg_data = get_csr_val_with_updated_field(ral.control.op, reg_data, RramOpRewrite);
  reg_data = get_csr_val_with_updated_field(ral.control.partition, reg_data, partition);
  reg_data = get_csr_val_with_updated_field(ral.control.num, reg_data, 3);
  csr_wr(.ptr(ral.control), .value(reg_data));

  // wait for command to complete
  rram_ctrl_wait_op_done();
endtask : rram_ctrl_rewrite

task rram_ctrl_base_vseq::rram_ctrl_read(input rram_ctrl_op_t ctrl_op, ref data_q_t data,
                                         input logic rd_check = 1'b1);

  uvm_reg_data_t reg_data;
  int            rd_fifo_level;
  data_q_t       bkdr_data;
  logic          bkdr_read_done = 1'b0;
  page_cfg_t     current_cfg;
  logic          exp_err = '0;

  // prevent multiple function entries
  ctrl_port_task_guard.get(1);

  // write start address
  csr_wr(.ptr(ral.addr), .value(ctrl_op.addr));

  // write command register
  reg_data = '0;
  reg_data = get_csr_val_with_updated_field(ral.control.start, reg_data, 1'b1);
  reg_data = get_csr_val_with_updated_field(ral.control.op, reg_data, ctrl_op.op);
  reg_data = get_csr_val_with_updated_field(ral.control.partition, reg_data, ctrl_op.partition);
  reg_data = get_csr_val_with_updated_field(ral.control.num, reg_data, ctrl_op.num_words);
  csr_wr(.ptr(ral.control), .value(reg_data));

  // wait for fifo to be filled and read out
  rd_fifo_level = 0;
  for (int i = 0; i <= ctrl_op.num_words; i++) begin
    current_cfg = get_current_page_cfg(ctrl_op.addr, i, ctrl_op.partition);
    if (rd_fifo_level == 0) begin
      do begin
        csr_rd(.ptr(ral.curr_fifo_lvl), .value(reg_data));
        rd_fifo_level = get_field_val(ral.curr_fifo_lvl.rd, reg_data);
      end while (rd_fifo_level == 0);
    end
    mem_rd(.ptr(ral.rd_fifo), .offset(0), .data(data[i]));
    // backdoor read to RRAM for automatic read check
    if (rd_check & ~bkdr_read_done) begin
      bkdr_data = cfg.rram_bkdr_mem_read(ctrl_op, 1'b0, 1'b1);
      bkdr_read_done = '1;
    end
    if ((current_cfg.rd_en != prim_mubi_pkg::MuBi4True) | exp_err) begin
      bkdr_data[i] = '1;
      exp_err = 1'b1;
    end
    if (rd_check) begin
      // check if read data matches with data in RRAM
      if (data[i] !== bkdr_data[i]) begin
        `uvm_error("Read-error:", $sformatf("data[%0d] exp: %08x is: %08x", i, bkdr_data[i],
                   data[i]))
      end
    end
    rd_fifo_level--;
  end
  // wait for command to complete
  rram_ctrl_wait_op_done();
endtask : rram_ctrl_read

// Task to perform a direct RRAM read at the specified location:
// Timeout is used to match the longest waiting timeout possible for the host, which will happen
// when the host is waiting for the controller to finish a write operation
task rram_ctrl_base_vseq::rram_host_read(
    input  addr_t addr,
    input  bit blocking = 0,
    input  bit check_rdata = 0,
    input  data_t exp_rdata = '0,
    input  prim_mubi_pkg::mubi4_t instr_type = prim_mubi_pkg::MuBi4False,
    output data_t rdata,
    output bit completed,
    input  bit exp_err_rsp = 0);
  bit saw_err;
  tl_access_w_abort(.addr(addr), .write(1'b0), .completed(completed), .saw_err(saw_err),
                    .tl_access_timeout_ns(write_timeout_ns), .mask('1),
                    .data(rdata), .exp_err_rsp(exp_err_rsp),
                    .check_exp_data(check_rdata), .exp_data(exp_rdata),
                    .compare_mask('1), .blocking(blocking), .instr_type(instr_type),
                    .tl_sequencer_h(p_sequencer.tl_sequencer_hs[cfg.host_ral_name]));
endtask : rram_host_read
