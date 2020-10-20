// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otp_ctrl_scoreboard extends cip_base_scoreboard #(
    .CFG_T(otp_ctrl_env_cfg),
    .RAL_T(otp_ctrl_reg_block),
    .COV_T(otp_ctrl_env_cov)
  );
  `uvm_component_utils(otp_ctrl_scoreboard)

  // local variables

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(push_pull_item#(SRAM_DATA_SIZE))  sram_fifo[NumSramKeyReqSlots];
  uvm_tlm_analysis_fifo #(push_pull_item#(OTBN_DATA_SIZE))  otbn_fifo;
  uvm_tlm_analysis_fifo #(push_pull_item#(FLASH_DATA_SIZE)) flash_addr_fifo;
  uvm_tlm_analysis_fifo #(push_pull_item#(FLASH_DATA_SIZE)) flash_data_fifo;

  // local queues to hold incoming packets pending comparison

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    for (int i = 0; i < NumSramKeyReqSlots; i++) begin
      sram_fifo[i] = new($sformatf("sram_fifo[%0d]", i), this);
    end
    otbn_fifo       = new("otbn_fifo", this);
    flash_addr_fifo = new("flash_addr_fifo", this);
    flash_data_fifo = new("flash_data_fifo", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
    join_none
  endtask

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel = DataChannel);
    uvm_reg csr;
    bit     do_read_check     = 1'b0;
    bit     write             = item.is_write();
    uvm_reg_addr_t csr_addr   = get_normalized_addr(item.a_addr);
    bit [TL_AW-1:0] addr_mask = cfg.csr_addr_map_size - 1;

    bit addr_phase_read   = (!write && channel == AddrChannel);
    bit addr_phase_write  = (write && channel == AddrChannel);
    bit data_phase_read   = (!write && channel == DataChannel);
    bit data_phase_write  = (write && channel == DataChannel);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.csr_addrs}) begin
      csr = ral.default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    // memories
    // TODO: memory read check, change hardcoded to parameters once design finalized
    end else if ((csr_addr & addr_mask) inside
        {[SW_WINDOW_BASE_ADDR : SW_WINDOW_BASE_ADDR + SW_WINDOW_SIZE],
         [TEST_ACCESS_BASE_ADDR : TEST_ACCESS_BASE_ADDR + TEST_ACCESS_WINDOW_SIZE]}) begin
      return;
    end else begin
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
      // add individual case item for each csr
      "intr_state": begin
        // FIXME
        do_read_check = 1'b0;
      end
      "intr_enable": begin
        // FIXME
      end
      "intr_test": begin
        // FIXME
      end
      default: begin
        //`uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
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
