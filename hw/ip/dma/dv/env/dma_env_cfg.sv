// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dma_env_cfg extends cip_base_env_cfg #(.RAL_T(dma_reg_block));
  // TL Port Configuration
  tl_agent_cfg tl_agent_dma_host_cfg;
  tl_agent_cfg tl_agent_dma_ctn_cfg;
  tl_agent_cfg tl_agent_dma_sys_cfg;

  // Interfaces
  dma_vif               dma_vif;
  dma_sys_tl_vif        dma_sys_tl_vif;
  virtual clk_rst_if    clk_rst_vif;

  // Scoreboard
  dma_scoreboard        scoreboard_h;

  // Waive full testing of the SoC System bus within block level DV?
  bit dma_dv_waive_system_bus;
  // Note: Currently we have only a 32-bit TL-UL model of the SoC System bus when full testing of
  // the System bus has been explicitly waived.
  logic [31:0] soc_system_hi_addr;

  // Names of interfaces used in DMA block
  // These variables are used to store names of FIFO that are used
  // in scoreboard and environment
  string fifo_names[3];
  // Names of a_channel_fifo
  string dma_a_fifo[string];
  // Names of d_channel_fifo
  string dma_d_fifo[string];
  // Names of dir_channel_fifo
  string dma_dir_fifo[string];

  // Source data for the entire transfer; this must be presented in chunks via the memory model
  // or FIFO because chunks overlap each other when auto-increment is not being used with the
  // memory address.
  bit [7:0] src_data[];

  // For each TLUL interface declare a mem_model instance and a
  //  dma_handshake_mode_fifo instance to emulate either memory or a
  // FIFO depending on handshake_mode_en
  // These models are used in TL device sequences
  // Data comparison is done in scoreboard
  dma_handshake_mode_fifo#(.AddrWidth(HOST_ADDR_WIDTH)) fifo_host;
  dma_handshake_mode_fifo#(.AddrWidth(CTN_ADDR_WIDTH)) fifo_ctn;
  dma_handshake_mode_fifo#(.AddrWidth(SYS_ADDR_WIDTH)) fifo_sys;
  mem_model#(.AddrWidth(HOST_ADDR_WIDTH), .DataWidth(HOST_DATA_WIDTH)) mem_host;
  mem_model#(.AddrWidth(CTN_ADDR_WIDTH), .DataWidth(CTN_DATA_WIDTH)) mem_ctn;
  mem_model#(.AddrWidth(SYS_ADDR_WIDTH), .DataWidth(SYS_DATA_WIDTH)) mem_sys;

  // Associative array with mapping of ASID encoding to interface name; for textual output.
  string asid_names[asid_encoding_e];

  `uvm_object_utils_begin(dma_env_cfg)
    `uvm_field_object(tl_agent_dma_host_cfg, UVM_DEFAULT)
    `uvm_field_object(tl_agent_dma_ctn_cfg, UVM_DEFAULT)
    `uvm_field_object(tl_agent_dma_sys_cfg, UVM_DEFAULT)
  `uvm_object_utils_end
  `uvm_object_new

  // Function for Initialization
  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = dma_env_pkg::LIST_OF_ALERTS;
    // Populate FIFO names
    fifo_names = '{"host", "ctn", "sys"};
    foreach (fifo_names[i]) begin
      dma_a_fifo[fifo_names[i]] = $sformatf("tl_a_%s_fifo", fifo_names[i]);
      dma_d_fifo[fifo_names[i]] = $sformatf("tl_d_%s_fifo", fifo_names[i]);
      dma_dir_fifo[fifo_names[i]] = $sformatf("tl_dir_%s_fifo", fifo_names[i]);
    end
    // Initialize mapping
    asid_names[OtInternalAddr] = "host";
    asid_names[SocControlAddr] = "ctn";
    asid_names[SocSystemAddr]  = "sys";

    // Initialize cip_base_env_cfg
    super.initialize(csr_base_addr);

    // Interrupt count
    num_interrupts = ral.intr_state.get_n_used_bits();

    // TL Agent Configuration objects - Non RAL
    `uvm_create_obj(tl_agent_cfg, tl_agent_dma_host_cfg)
    tl_agent_dma_host_cfg.max_outstanding_req = dma_pkg::NUM_MAX_OUTSTANDING_REQS;
    tl_agent_dma_host_cfg.if_mode = dv_utils_pkg::Device;

    `uvm_create_obj(tl_agent_cfg, tl_agent_dma_ctn_cfg)
    tl_agent_dma_ctn_cfg.max_outstanding_req = dma_pkg::NUM_MAX_OUTSTANDING_REQS;
    tl_agent_dma_ctn_cfg.if_mode = dv_utils_pkg::Device;

    `uvm_create_obj(tl_agent_cfg, tl_agent_dma_sys_cfg)
    tl_agent_dma_sys_cfg.max_outstanding_req = dma_pkg::NUM_MAX_OUTSTANDING_REQS;
    tl_agent_dma_sys_cfg.if_mode = dv_utils_pkg::Device;

    // TL Agent Configuration - RAL based
    m_tl_agent_cfg.max_outstanding_req = 1;

  endfunction: initialize

endclass
