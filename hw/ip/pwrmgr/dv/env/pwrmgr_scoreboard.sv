// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwrmgr_scoreboard extends cip_base_scoreboard #(
    .CFG_T(pwrmgr_env_cfg),
    .RAL_T(pwrmgr_reg_block),
    .COV_T(pwrmgr_env_cov)
  );
  `uvm_component_utils(pwrmgr_scoreboard)

  // local variables

  // TLM agent fifos

  // local queues to hold incoming packets pending comparison

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
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
      `uvm_info(`gfn, $sformatf("Writing 0x%x to %s", item.a_data, csr.get_full_name()), UVM_LOW)
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
    end

    // process the csr req
    // for write, update local variable and fifo at address phase
    // for read, update predication at address phase and compare at data phase
    case (csr.get_name())
      // add individual case item for each csr
      "intr_state": begin
        // rw1c: write 1 clears, write 0 is no-op.
        do_read_check = 1'b0;
      end
      "intr_enable": begin
        // FIXME
      end
      "intr_test": begin
        // Write-only, so it can't be read.
        do_read_check = 1'b0;
      end
      "ctrl_cfg_regwen": begin
        // Read-only. Hardware clears this bit when going to low power mode,
        //  and sets it in active mode.
        do_read_check = 1'b0;
      end
      "control": begin
        // Only some bits can be checked on reads. Bit 0 is cleared by hardware
        // on low power transition or when registering a valid resets.
      end
      "cfg_cdc_sync": begin
        // rw1c: When written to 1 this bit self-clears when the slow clock domain
        // syncs.
        do_read_check = 1'b0;
      end
      "wakeup_en_regwen": begin
        // Write with 0 clears (so write with 1 is a no-op).
        do_read_check = 1'b0;
      end
      "wakeup_en": begin
        // What do the bits control?
      end
      "wake_status": begin
        // Read-only.
        do_read_check = 1'b0;
      end
      "reset_en_regwen": begin
        // rw0c, so writing a 1 is a no-op.
      end
      "reset_en": begin
        // What do the bits control?
      end
      "reset_status": begin
        // Read-only.
        do_read_check = 1'b0;
      end
      "escalate_reset_status": begin
        // Read-only.
        do_read_check = 1'b0;
      end
      "wake_info_capture_dis": begin
      end
      "wake_info": begin
        // rw1c: write 1 clears, write 0 is no-op.
        do_read_check = 1'b0;
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
      end
    endcase

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (data_phase_read) begin
      `uvm_info(`gfn, $sformatf("Reading 0x%x from %s", item.d_data, csr.get_full_name()), UVM_LOW)
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
