// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_scoreboard extends cip_base_scoreboard #(
    .CFG_T(i2c_env_cfg),
    .RAL_T(i2c_reg_block),
    .COV_T(i2c_env_cov)
  );
  `uvm_component_utils(i2c_scoreboard)

  //****************************************************************
  // TODO: this class will be completed later with i2c_sanity test
  // TODO: no need for review
  //****************************************************************
  virtual i2c_if i2c_vif;

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(i2c_item) i2c_fifo;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    i2c_fifo = new("i2c_fifo", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_i2c_fifo();
    join_none
  endtask

  virtual task process_i2c_fifo();
    // TODO
  endtask : process_i2c_fifo

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel = DataChannel);
    uvm_reg csr;
    bit do_read_check = 1'b0;
    bit write = item.is_write();
    uvm_reg_addr_t csr_addr = get_normalized_addr(item.a_addr);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.csr_addrs}) begin
      csr = ral.default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end else begin
      `uvm_fatal(`gfn, $sformatf("access unexpected addr 0x%0h", csr_addr))
    end

    if (channel == AddrChannel) begin
      // if incoming access is a write to a valid csr, then make updates right away
      if (write) begin
        void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
      end
    end

    // process the csr req
    // for write, update local variable and fifo at address phase
    // for read, update predication at address phase and compare at data phase
    case (csr.get_name())
      // add individual case item for each csr
      default: begin
        //`uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
      end
    endcase

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (!write && channel == DataChannel) begin
      if (do_read_check) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
                     $sformatf("reg name: %0s", csr.get_full_name()))
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end
  endtask

  function void compare(i2c_item act, i2c_item exp, string dir = "TX");
    if (!act.compare(exp)) begin
      `uvm_error(`gfn, $sformatf("%s item mismatch!\nexp:\n%0s\nobs:\n%0s",
                                  dir, exp.sprint(), act.sprint()))
    end
    else begin
      `uvm_info(`gfn, $sformatf("%s item match!\nexp:\n%0s\nobs:\n%0s",
                                 dir, exp.sprint(), act.sprint()), UVM_HIGH)
    end
  endfunction : compare

  virtual function void reset(string kind = "HARD");
    // reset local fifos queues and variables
    super.reset(kind);
  endfunction : reset

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
  endfunction

endclass : i2c_scoreboard
