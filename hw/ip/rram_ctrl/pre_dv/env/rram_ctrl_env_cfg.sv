// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rram_ctrl_env_cfg extends cip_base_env_cfg #(.RAL_T(rram_ctrl_core_reg_block));
  `uvm_object_utils(rram_ctrl_env_cfg)

  // Clock and reset for the otp_ctrl interface, present at the DUT's clk_otp_i and
  // rst_otp_ni ports.
  virtual clk_rst_if otp_clk_rst_vif;

  // Life cycle, RMA, key manager and power manager signals.
  misc_vif_t misc_vif;

  // otp_ctrl macro interface, in the OTP clock domain.
  otp_macro_vif_t otp_macro_vif;

  // Name of the RAL model tied to the host interface (tl_host), which accesses the
  // RRAM data array.
  string host_ral_name = "rram_ctrl_host_reg_block";
  // Name of the RAL model tied to the RRAM macro's primitive interface (tl_prim).
  string prim_ral_name = "rram_macro_prim_reg_block";

  // The configured depth of the DUT's write/read FIFOs (WrFifoDepth/RdFifoDepth). Retrieved
  // from uvm_config_db in the environment's build_phase - tb.sv is the source of truth, since
  // it elaborates the DUT with these values directly.
  int unsigned m_wr_fifo_depth;
  int unsigned m_rd_fifo_depth;

  // Probability in percent that a randomly configured region or page gets the corresponding
  // property enabled. Set through plusargs, see rram_ctrl_base_test.
  uint scr_en_pct = 50;
  uint reg_en_pct = 100;
  uint wr_en_pct  = 100;
  uint rd_en_pct  = 100;
  uint ecc_en_pct = 100;

  // Skip zeroing the data or info array through the backdoor during initialization.
  bit skip_init_data_array = 1'b0;
  bit skip_init_info_array = 1'b0;
  // Skip starting the controller's initialization (INIT register) in rram_ctrl_init(), so that a
  // test can do it itself.
  bit skip_lc_init         = 1'b0;

  // Scrambling keys returned to the DUT by the OTP key drivers. Set by rram_ctrl_env.
  bit [KeyWidth-1:0] otp_addr_key;
  bit [KeyWidth-1:0] otp_data_key;

  // Effective page configuration, kept up to date by the scoreboard.
  rram_ctrl_mp_model mp_model;

  // Backdoor access to the data and info arrays, and to the OTP region within the data array.
  // Set by rram_ctrl_env.
  rram_ctrl_bkdr_util     mem_bkdr_util_h[rram_part_e];
  rram_ctrl_otp_bkdr_util otp_bkdr_util_h;

  // Standard SV/UVM methods
  extern function new(string name="");

  // Class specific methods
  extern function void initialize(bit inherit_ral_models = 1'b0);

  // Reads RRAM word `word_addr` of partition `part` via the backdoor.
  //
  // Descrambles the data if `descramble` is set, and removes the address infection of each bus
  // word if `addr_xor` is set.
  // If `check_cfg` is set, `descramble` is instead taken from the current page configuration.
  extern function rram_word_t rram_bkdr_word_read(int unsigned word_addr,
                                                  rram_part_e  part,
                                                  bit          descramble,
                                                  bit          addr_xor = 1'b1,
                                                  bit          check_cfg = 1'b0);

  // Writes RRAM word `word_addr` of partition `part` via the backdoor.
  //
  // Infects each bus word with its address and scrambles the data if `scramble` is set, which
  // is how the controller stores data.
  // If `check_cfg` is set, `scramble` is instead taken from the current page configuration.
  extern function void rram_bkdr_word_write(int unsigned word_addr,
                                            rram_part_e  part,
                                            rram_word_t  data,
                                            bit          scramble,
                                            bit          check_cfg = 1'b0);

  // Reads all bus words of `op` via the backdoor. See rram_bkdr_word_read().
  // The start address must be aligned to RRAM words.
  extern function data_q_t rram_bkdr_mem_read(rram_ctrl_op_t op,
                                              bit            descramble,
                                              bit            check_cfg = 1'b0);

  // Writes `data` to all bus words of `op` via the backdoor. See rram_bkdr_word_write().
  // The start address must be aligned to RRAM words and `op` must cover full RRAM words.
  extern function void rram_bkdr_mem_write(rram_ctrl_op_t op,
                                           data_q_t       data,
                                           bit            scramble,
                                           bit            check_cfg = 1'b0);

  // Reads `otp_size` + 1 OTP words starting at `otp_addr` via the backdoor, and checks them
  // against the stored integrity.
  // `intg_err` is set if the integrity of the surrounding 64-bit chunk does not match.
  extern function void otp_bkdr_read(otp_ctrl_macro_pkg::otp_macro_addr_t otp_addr,
                                     otp_ctrl_macro_pkg::otp_macro_size_t otp_size,
                                     output otp_ctrl_macro_pkg::otp_macro_data_t otp_data,
                                     output bit intg_err);

  // Returns the page of byte address `addr`.
  extern function int unsigned get_page(addr_t addr);
endclass : rram_ctrl_env_cfg


function rram_ctrl_env_cfg::new(string name="");
  super.new(name);
endfunction : new

function void rram_ctrl_env_cfg::initialize(bit inherit_ral_models = 1'b0);
  list_of_alerts = rram_ctrl_env_pkg::LIST_OF_ALERTS;

  ral_model_names[host_ral_name] = 1'b0;
  clk_freqs_mhz[host_ral_name] = clk_freq_mhz;
  ral_model_names[prim_ral_name] = 1'b0;
  clk_freqs_mhz[prim_ral_name] = clk_freq_mhz;

  super.initialize(inherit_ral_models);

  // Configure tl agents. Everything defaults to 1 outstanding request, except the
  // host interface (tl_host), which can tolerate up to 2 outstanding read requests.
  m_tl_agent_cfg.max_outstanding_req = 1;
  m_tl_agent_cfgs[prim_ral_name].max_outstanding_req = 1;
  m_tl_agent_cfgs[host_ral_name].max_outstanding_req = rram_ctrl_pkg::NumOutstandingRdReq;

  // Set num_interrupts
  begin
    uvm_reg rg = ral.get_reg_by_name("intr_state");
    if (rg != null) begin
      num_interrupts = ral.intr_state.get_n_used_bits();
      `DV_CHECK_EQ_FATAL(num_interrupts, rram_ctrl_env_pkg::NumRramCtrlIntr,
                          "num_interrupts does not match rram_ctrl_intr_e")
    end
  end

  mp_model = rram_ctrl_mp_model::type_id::create("mp_model");
  mp_model.initialize(ral);
endfunction : initialize

function rram_word_t rram_ctrl_env_cfg::rram_bkdr_word_read(int unsigned word_addr,
                                                            rram_part_e  part,
                                                            bit          descramble,
                                                            bit          addr_xor = 1'b1,
                                                            bit          check_cfg = 1'b0);
  rram_word_t data_mem, data;

  data_mem = mem_bkdr_util_h[part].read128(word_addr << DataByteWidth);

  if (check_cfg) begin
    descramble = mp_model.get_sw_page_cfg(part, word_addr >> WordW).scramble_en == MuBi4True;
  end

  data = descramble ? mem_bkdr_util_h[part].rram_descramble_data(data_mem, word_addr,
                                                                 otp_addr_key, otp_data_key) :
                      data_mem;

  // Remove the address infection of each bus word.
  if (addr_xor) begin
    for (int k = 0; k < WidthMultiple; k++) begin
      data[k*BusWidth +: BusWidth] ^= BusWidth'((word_addr << WordSelW) + k);
    end
  end

  `uvm_info(`gfn, $sformatf("Backdoor read part=%s, word_addr=0x%0x, data=0x%0x",
                            part.name(), word_addr, data), UVM_HIGH)
  return data;
endfunction : rram_bkdr_word_read

function void rram_ctrl_env_cfg::rram_bkdr_word_write(int unsigned word_addr,
                                                      rram_part_e  part,
                                                      rram_word_t  data,
                                                      bit          scramble,
                                                      bit          check_cfg = 1'b0);
  if (check_cfg) begin
    scramble = mp_model.get_sw_page_cfg(part, word_addr >> WordW).scramble_en == MuBi4True;
  end

  // Infect each bus word with its address.
  for (int k = 0; k < WidthMultiple; k++) begin
    data[k*BusWidth +: BusWidth] ^= BusWidth'((word_addr << WordSelW) + k);
  end

  if (scramble) begin
    data = mem_bkdr_util_h[part].rram_scramble_data(data, word_addr, otp_addr_key, otp_data_key);
  end

  `uvm_info(`gfn, $sformatf("Backdoor write part=%s, word_addr=0x%0x, stored data=0x%0x",
                            part.name(), word_addr, data), UVM_HIGH)
  mem_bkdr_util_h[part].write128(word_addr << DataByteWidth, data);
endfunction : rram_bkdr_word_write

function data_q_t rram_ctrl_env_cfg::rram_bkdr_mem_read(rram_ctrl_op_t op,
                                                        bit            descramble,
                                                        bit            check_cfg = 1'b0);
  rram_word_t  rd_data;
  int unsigned word_addr = op.addr >> DataByteWidth;
  data_q_t     data;

  `DV_CHECK_EQ(op.addr[DataByteWidth-1:0], 0, "Backdoor reads must be RRAM word aligned")
  for (int i = 0; i <= op.num_words; i++) begin
    if (i % WidthMultiple == 0) begin
      rd_data = rram_bkdr_word_read(word_addr, op.partition, descramble, 1'b1, check_cfg);
      word_addr++;
    end
    data.push_back(rd_data[(i % WidthMultiple) * BusWidth +: BusWidth]);
  end
  return data;
endfunction : rram_bkdr_mem_read

function void rram_ctrl_env_cfg::rram_bkdr_mem_write(rram_ctrl_op_t op,
                                                     data_q_t       data,
                                                     bit            scramble,
                                                     bit            check_cfg = 1'b0);
  rram_word_t  wr_data;
  int unsigned word_addr = op.addr >> DataByteWidth;

  `DV_CHECK_EQ(op.addr[DataByteWidth-1:0], 0, "Backdoor writes must be RRAM word aligned")
  `DV_CHECK_EQ((op.num_words + 1) % WidthMultiple, 0, "Backdoor writes must cover RRAM words")
  for (int i = 0; i <= op.num_words; i++) begin
    wr_data[(i % WidthMultiple) * BusWidth +: BusWidth] = data[i];
    if (i % WidthMultiple == WidthMultiple - 1) begin
      rram_bkdr_word_write(word_addr, op.partition, wr_data, scramble, check_cfg);
      word_addr++;
    end
  end
endfunction : rram_bkdr_mem_write

function void rram_ctrl_env_cfg::otp_bkdr_read(otp_ctrl_macro_pkg::otp_macro_addr_t otp_addr,
                                               otp_ctrl_macro_pkg::otp_macro_size_t otp_size,
                                               output otp_ctrl_macro_pkg::otp_macro_data_t otp_data,
                                               output bit intg_err);
  localparam int unsigned ChunkBytes   = OtpIntgDataWidth / 8;
  localparam int unsigned OtpWordBytes = otp_ctrl_macro_pkg::OtpWidth / 8;
  // Byte offset of the OTP integrity page in the data array, see rram_ctrl_otp.sv.
  localparam int unsigned OtpIntgByteOffset = OtpStartPage << (BusAddrByteW - PageW);

  int unsigned               byte_addr  = otp_addr << otp_ctrl_macro_pkg::OtpAddrShift;
  int unsigned               chunk_addr = byte_addr - (byte_addr % ChunkBytes);
  bit [OtpIntgDataWidth-1:0] chunk;
  bit [OtpIntgWidth-1:0]     intg_mem;
  bit [71:0]                 codeword;

  chunk    = otp_bkdr_util_h.read64(chunk_addr);
  intg_mem = mem_bkdr_util_h[RramPartData].read8(OtpIntgByteOffset + chunk_addr / ChunkBytes);
  codeword = prim_secded_pkg::prim_secded_hamming_72_64_enc(chunk);
  intg_err = intg_mem != codeword[71:64];

  otp_data = '0;
  for (int k = 0; k <= otp_size; k++) begin
    otp_data[k * otp_ctrl_macro_pkg::OtpWidth +: otp_ctrl_macro_pkg::OtpWidth] =
        chunk[(byte_addr % ChunkBytes + k * OtpWordBytes) * 8 +: otp_ctrl_macro_pkg::OtpWidth];
  end
endfunction : otp_bkdr_read

function int unsigned rram_ctrl_env_cfg::get_page(addr_t addr);
  return addr >> (BusAddrByteW - PageW);
endfunction : get_page
