// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rom_ctrl_scoreboard extends cip_base_scoreboard #(
    .CFG_T(rom_ctrl_env_cfg),
    .RAL_T(rom_ctrl_regs_reg_block),
    .COV_T(rom_ctrl_env_cov)
  );
  `uvm_component_utils(rom_ctrl_scoreboard)

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(kmac_app_item) kmac_req_fifo;
  uvm_tlm_analysis_fifo #(kmac_app_item) kmac_rsp_fifo;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    kmac_req_fifo = new("kmac_req_fifo", this);
    kmac_rsp_fifo = new("kmac_rsp_fifo", this);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_kmac_req_fifo();
      process_kmac_rsp_fifo();
      monitor_rom_ctrl_if();
    join
  endtask

  virtual task process_kmac_req_fifo();
    kmac_app_item kmac_req;
    forever begin
      kmac_req_fifo.get(kmac_req);
      `uvm_info(`gfn, $sformatf("Detected a KMAC req:\n%0s", kmac_req.sprint()), UVM_HIGH)
    end
  endtask


  virtual task process_kmac_rsp_fifo();
    kmac_app_item kmac_rsp;
    forever begin
      kmac_rsp_fifo.get(kmac_rsp);
      `uvm_info(`gfn, $sformatf("Detected a KMAC response:\n%0s", kmac_rsp.sprint()), UVM_HIGH)
    end
  endtask

  // Montitor and check outputs sent to pwrmgr and keymgr
  virtual task monitor_rom_ctrl_if();
    forever begin
      @(cfg.rom_ctrl_vif.pwrmgr_data or cfg.rom_ctrl_vif.keymgr_data or cfg.under_reset);
      if (cfg.under_reset) continue;
    end
  endtask

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg csr;
    bit     do_read_check   = 1'b1;
    bit     write           = item.is_write();
    uvm_reg_addr_t csr_addr = ral.get_word_aligned_addr(item.a_addr);

    bit addr_phase_read   = (!write && channel == AddrChannel);
    bit addr_phase_write  = (write && channel == AddrChannel);
    bit data_phase_read   = (!write && channel == DataChannel);
    bit data_phase_write  = (write && channel == DataChannel);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.csr_addrs[ral_name]}) begin
      csr = ral.default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end
    else begin
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
      "alert_test": begin
        // do_nothing
      end
      "fatal_alert_cause": begin
        // do_nothing
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
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
