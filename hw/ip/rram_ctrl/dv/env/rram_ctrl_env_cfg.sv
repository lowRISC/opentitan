// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rram_ctrl_env_cfg extends cip_base_env_cfg #(.RAL_T(rram_ctrl_core_reg_block));
  `uvm_object_utils(rram_ctrl_env_cfg)

  // Variables that can be controlled through hjson
  // Changing a value here, will impact multiple tests. Consider changing the values in the test
  // configuration of the hjson
  uint scr_en_pct = 50;
  uint reg_en_pct = 100;
  uint wr_en_pct  = 100;
  uint rd_en_pct  = 100;
  uint ecc_en_pct = 100;

  bit skip_init_data_array = 1'b0;
  bit skip_init_info_array = 1'b0;
  bit skip_lc_init         = 1'b0;

  // Currently used otp keys
  logic [KeyWidth-1:0] otp_addr_key;
  logic [KeyWidth-1:0] otp_data_key;

  // Current page configurations
  page_cfg_t [TotalPages-1:0]     data_pages_cfg;
  page_cfg_t [TotalInfoPages-1:0] info_pages_cfg;

  // Current mp region configurations
  mp_region_cfg_t mp_regions[MpRegions];
  page_cfg_t      default_cfg;

  localparam int unsigned RramDataWidth     = rram_ctrl_pkg::DataWidth;
  localparam int unsigned RramAddrW         = rram_ctrl_pkg::AddrW;
  localparam int unsigned RramDataByteWidth = $clog2(RramDataWidth / 8);
  localparam int unsigned RramBusWidth      = rram_ctrl_pkg::BusWidth;
  localparam int unsigned RramBusAddrByteW  = rram_ctrl_pkg::BusAddrByteW;
  localparam int unsigned RramBusAddrW      = rram_ctrl_pkg::BusAddrW;

  // External interfaces
  misc_vif_t misc_vif;

  string host_ral_name = "rram_ctrl_host_reg_block";
  string prim_ral_name = "rram_macro_prim_reg_block";

  // Pointer for bkdr mem task.
  rram_ctrl_bkdr_util mem_bkdr_util_h[rram_ctrl_pkg::rram_part_e];

  // Standard SV/UVM methods
  extern function new(string name="");

  // Class specific methods
  extern function void initialize();

  // Methods to access RRAM via backdoor
  extern function logic [RramDataWidth-1:0] rram_bkdr_word_read(logic [AddrW-1:0] addr,
                                                                rram_part_e part,
                                                                logic descramble,
                                                                logic check_cfg = 1'b0);

  extern function data_q_t rram_bkdr_mem_read(rram_ctrl_op_t rram_ctrl_op,
                                              logic descramble,
                                              logic check_cfg = 1'b0);

  extern function void rram_bkdr_word_write(logic [AddrW-1:0] addr, rram_part_e part,
                                            logic [RramDataWidth-1:0] data,
                                            logic scramble, logic check_cfg = 1'b0);

  extern function void rram_bkdr_mem_write(rram_ctrl_op_t rram_ctrl_op, data_q_t data,
                                           logic scramble, logic check_cfg = 1'b0);

endclass : rram_ctrl_env_cfg


function rram_ctrl_env_cfg::new(string name="");
  super.new(name);
endfunction : new

function void rram_ctrl_env_cfg::initialize();
  list_of_alerts = rram_ctrl_env_pkg::LIST_OF_ALERTS;

  ral_model_names.push_back(host_ral_name);
  clk_freqs_mhz[host_ral_name] = clk_freq_mhz;
  ral_model_names.push_back(prim_ral_name);
  clk_freqs_mhz[prim_ral_name] = clk_freq_mhz;

  super.initialize();

  // configure tl agents:
  m_tl_agent_cfg.max_outstanding_req = 1;
  m_tl_agent_cfgs[prim_ral_name].max_outstanding_req = 1;
  // the host interface can tolerate up to 4 outstanding read requests
  m_tl_agent_cfgs[host_ral_name].max_outstanding_req = 4;

  // Set num_interrupts
  begin
    uvm_reg rg = ral.get_reg_by_name("intr_state");
    if (rg != null) begin
      num_interrupts = ral.intr_state.get_n_used_bits();
    end
  end
endfunction : initialize


// Method to read one full width word of the RRAM
function automatic logic [rram_ctrl_env_cfg::RramDataWidth-1:0]
    rram_ctrl_env_cfg::rram_bkdr_word_read(logic [AddrW-1:0] addr,
                                           rram_part_e part,
                                           logic descramble,
                                           logic check_cfg = 1'b0);

  logic [RramBusAddrByteW-1:0] byte_addr;
  logic [RramBusAddrW-1:0] word_addr;
  logic [RramDataWidth-1:0] data_descrambled, data_mem, data;

  byte_addr = addr << RramDataByteWidth;
  data_mem = mem_bkdr_util_h[part].read128(byte_addr);

  if (check_cfg) begin
    descramble = (part == RramPartData) ?
                  (data_pages_cfg[addr[AddrW-1 -: PageW]].scramble_en == prim_mubi_pkg::MuBi4True) :
                  (info_pages_cfg[addr[AddrW-1 -: PageW]].scramble_en == prim_mubi_pkg::MuBi4True);
  end

  // descramble rram word
  if (descramble) begin
    data_descrambled = mem_bkdr_util_h[part].rram_descramble_data(data_mem, addr,
                                                                  otp_addr_key, otp_data_key);
  end else begin
    data_descrambled = data_mem;
  end
  // remove addr xor
  for (int k = 0; k < RramDataByteWidth; k++) begin
    word_addr = (addr<<2) + k;
    data[k*RramBusWidth +: RramBusWidth] = word_addr ^
        data_descrambled[k*RramBusWidth +: RramBusWidth];
  end

  `uvm_info(`gfn, $sformatf("Back-door read part=%s, data=%x addr=%x\n",
                              part.name(), data, byte_addr), UVM_MEDIUM)

  return data;
endfunction : rram_bkdr_word_read

// Method to read a full rram_ctrl_op to RRAM via backdoor
function automatic data_q_t rram_ctrl_env_cfg::rram_bkdr_mem_read(rram_ctrl_op_t rram_ctrl_op,
                                                                  logic descramble,
                                                                  logic check_cfg = 1'b0);

  logic [RramDataWidth-1:0] rd_data;
  logic [RramAddrW-1:0] addr;
  data_q_t data;

  addr = rram_ctrl_op.addr >> RramDataByteWidth;

  // addr must be aligend to RRAM word boundaries
  for (int i = 0; i <= rram_ctrl_op.num_words; i++) begin
    if (i%4 == 0) begin
      rd_data = rram_bkdr_word_read(addr, rram_ctrl_op.partition, descramble, check_cfg);
      addr = addr + 1;
    end
    data[i] = rd_data[(i%4)*RramBusWidth +: RramBusWidth];
    `uvm_info(`gfn, $sformatf("Back-door read data=%x",
                              data[i]), UVM_MEDIUM)
  end
  return data;

endfunction : rram_bkdr_mem_read

// Method to write one full width word of the RRAM
function automatic void rram_ctrl_env_cfg::rram_bkdr_word_write(logic [AddrW-1:0] addr,
                                                                rram_part_e part,
                                                                logic [RramDataWidth-1:0] data,
                                                                logic scramble,
                                                                logic check_cfg = 1'b0);
  logic [RramBusAddrByteW-1:0] byte_addr;
  logic [RramBusAddrW-1:0] word_addr;
  logic [RramDataWidth-1:0] data_xor, data_scrambled, data_descrambled;

  if (check_cfg) begin
    scramble = (part == RramPartData) ?
                  (data_pages_cfg[addr[AddrW-1 -: PageW]].scramble_en == prim_mubi_pkg::MuBi4True) :
                  (info_pages_cfg[addr[AddrW-1 -: PageW]].scramble_en == prim_mubi_pkg::MuBi4True);
  end

  byte_addr = addr << RramDataByteWidth;
  // add addr xor
  for (int k = 0; k < rram_ctrl_pkg::WidthMultiple; k++) begin
    word_addr = (addr<<2) + k;
    data_xor[k*RramBusWidth +: RramBusWidth] = word_addr ^
        data[k*RramBusWidth +: RramBusWidth];
  end
  // scramble data
  if (scramble) begin
    data_scrambled = mem_bkdr_util_h[part].rram_scramble_data(data_xor, addr,
                                                              otp_addr_key, otp_data_key);
  end else begin
    data_scrambled = data_xor;
  end

  `uvm_info(`gfn, $sformatf("Back-door write part=%s, data_scrambled=%x addr=%x\n",
                            part.name(), data_scrambled, byte_addr), UVM_MEDIUM)
  mem_bkdr_util_h[part].write128(byte_addr, data_scrambled);
endfunction : rram_bkdr_word_write

// Method to write a full rram_ctrl_op to RRAM via backdoor
function automatic void rram_ctrl_env_cfg::rram_bkdr_mem_write(rram_ctrl_op_t rram_ctrl_op,
                                                               data_q_t data,
                                                               logic scramble,
                                                               logic check_cfg = 1'b0);

  logic [RramDataWidth-1:0] wr_data;
  logic [RramAddrW-1:0] addr;

  addr = rram_ctrl_op.addr >> RramDataByteWidth;

  // addr must be aligend to rram word boundaries
  for (int i = 0; i <= rram_ctrl_op.num_words; i++) begin
    wr_data[(i%4)*RramBusWidth +: RramBusWidth] = data[i];

    `uvm_info(`gfn, $sformatf("Back-door write data=%x",
                              data[i]), UVM_MEDIUM)
    // full word, write to RRAM
    if (i%4 == 3) begin
      rram_bkdr_word_write(addr, rram_ctrl_op.partition, wr_data, scramble, check_cfg);
      addr = addr + 1;
      wr_data = '0;
    end
  end

endfunction : rram_bkdr_mem_write
