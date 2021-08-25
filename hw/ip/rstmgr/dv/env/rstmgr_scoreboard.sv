// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rstmgr_scoreboard extends cip_base_scoreboard #(
  .CFG_T(rstmgr_env_cfg),
  .RAL_T(rstmgr_reg_block),
  .COV_T(rstmgr_env_cov)
);
  `uvm_component_utils(rstmgr_scoreboard)

  // local variables

  // TLM agent fifos

  // local queues to hold incoming packets pending comparison

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // TODO: remove once support alert checking
    do_alert_check = 0;
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
    join_none
  endtask

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg        csr;
    bit            do_read_check = 1'b1;
    bit            write = item.is_write();
    uvm_reg_addr_t csr_addr = ral.get_word_aligned_addr(item.a_addr);

    bit            addr_phase_read = (!write && channel == AddrChannel);
    bit            addr_phase_write = (write && channel == AddrChannel);
    bit            data_phase_read = (!write && channel == DataChannel);
    bit            data_phase_write = (write && channel == DataChannel);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = ral.default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    // if incoming access is a write to a valid csr, then make updates right away
    if (addr_phase_write) begin
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
    end

    // process the csr req:
    // for write, update local variable and fifo at address phase,
    // for read, update predication at address phase and compare at data phase.
    // TODO Add support for reading registers with separate write-enable.
    case (csr.get_name())
      // add individual case item for each csr
      "alert_test": begin
        // Write only.
        do_read_check = 1'b0;
      end
      "reset_info": begin
        // RW1C.
        do_read_check = 1'b0;
      end
      "alert_regwen": begin
        // RW0C.
        // do_read_check = 1'b0;
      end
      "alert_info_ctrl": begin
        // The en bit is cleared by the hardware.
        do_read_check = 1'b0;
      end
      "alert_info_attr": begin
        // Read only.
        do_read_check = 1'b0;
      end
      "alert_info": begin
        // Read only.
        do_read_check = 1'b0;
      end
      "cpu_regwen": begin
        // RW0C.
        // do_read_check = 1'b0;
      end
      "cpu_info_ctrl": begin
        // The en bit is cleared by the hardware.
        do_read_check = 1'b0;
      end
      "cpu_info_attr": begin
        // Read only.
        do_read_check = 1'b0;
      end
      "cpu_info": begin
        // Read only.
        do_read_check = 1'b0;
      end
      "sw_rst_regen": begin
      end
      "sw_rst_ctrl_n": begin
        // TODO Check with bitwise enables from sw_rst_regen.
        do_read_check = 1'b0;
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
      end
    endcase

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (data_phase_read) begin
      if (do_read_check) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data, $sformatf(
                     "reg name: %0s", csr.get_full_name()))
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
