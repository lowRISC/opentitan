// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

% if is_cip:
class ${name}_scoreboard extends cip_base_scoreboard #(
% else:
class ${name}_scoreboard extends dv_base_scoreboard #(
% endif
    .CFG_T(${name}_env_cfg),
% if has_ral:
    .RAL_T(${name}_reg_block),
% endif
    .COV_T(${name}_env_cov)
  );
  `uvm_component_utils(${name}_scoreboard)

  // local variables

  // TLM agent fifos
% for agent in env_agents:
  uvm_tlm_analysis_fifo #(${agent}_item) ${agent}_fifo;
% endfor

  // local queues to hold incoming packets pending comparison
% for agent in env_agents:
  ${agent}_item ${agent}_q[$];
% endfor

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
% for agent in env_agents:
    ${agent}_fifo = new("${agent}_fifo", this);
% endfor
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
% for agent in env_agents:
      process_${agent}_fifo();
% endfor
    join_none
  endtask
% for agent in env_agents:

  virtual task process_${agent}_fifo();
    ${agent}_item item;
    forever begin
      ${agent}_fifo.get(item);
      `uvm_info(`gfn, $sformatf("received ${agent} item:\n%0s", item.sprint()), UVM_HIGH)
    end
  endtask
% endfor
% if is_cip:

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel = DataChannel);
    uvm_reg csr;
    bit     do_read_check   = 1'b1;
    bit     write           = item.is_write();
    uvm_reg_addr_t csr_addr = ral.get_word_aligned_addr(item.a_addr);

    bit addr_phase_read   = (!write && channel == AddrChannel);
    bit addr_phase_write  = (write && channel == AddrChannel);
    bit data_phase_read   = (!write && channel == DataChannel);
    bit data_phase_write  = (write && channel == DataChannel);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.csr_addrs}) begin
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
% endif

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset local fifos queues and variables
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
  endfunction

endclass
