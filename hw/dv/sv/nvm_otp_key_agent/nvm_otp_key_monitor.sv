// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Watches both request/acknowledge pairs of nvm_otp_key_if.
//
// - When a request line rises, a request item (only `kind` set) is written to req_analysis_port.
//   The agent connects that port to the sequencer's request FIFO, from which the device sequence
//   builds the response.
// - When the request and its ack are seen high together (the handshake), a completed item with
//   the key that was on the bus is written to analysis_port, for the scoreboard.
//
// The monitor also maintains cfg.in_reset from the interface's reset.
class nvm_otp_key_monitor extends dv_reactive_monitor #(
  .ITEM_T (nvm_otp_key_item),
  .CFG_T  (nvm_otp_key_agent_cfg),
  .COV_T  (nvm_otp_key_agent_cov)
);
  `uvm_component_utils(nvm_otp_key_monitor)

  extern function new(string name, uvm_component parent);
  extern task run_phase(uvm_phase phase);
  extern virtual task monitor_ready_to_end();

  // Keeps cfg.in_reset in sync with the interface's reset.
  extern protected virtual task monitor_reset();

  extern protected virtual task collect_trans();

  // Returns the request and ack lines for the given key from the monitor's clocking block.
  extern protected virtual function void sample_lines(nvm_otp_key_kind_e kind,
                                                      output bit req,
                                                      output bit ack);

  // Sends a request item for `kind` to the sequencer.
  extern protected virtual function void write_req(nvm_otp_key_kind_e kind);

  // Builds a completed item from the response bus and sends it to the scoreboard.
  extern protected virtual function void write_handshake(nvm_otp_key_kind_e kind,
                                                         int unsigned       req_to_ack_cycles);
endclass : nvm_otp_key_monitor

function nvm_otp_key_monitor::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction : new

task nvm_otp_key_monitor::run_phase(uvm_phase phase);
  fork
    monitor_reset();
    super.run_phase(phase);
  join
endtask : run_phase

task nvm_otp_key_monitor::monitor_reset();
  forever begin
    // Anything other than a clean 1 (including X at time zero) counts as reset.
    cfg.in_reset = 1'b1;
    wait (cfg.vif.rst_n === 1'b1);
    `uvm_info(`gfn, "Out of reset", UVM_HIGH)
    cfg.in_reset = 1'b0;
    wait (cfg.vif.rst_n !== 1'b1);
    `uvm_info(`gfn, "Reset detected", UVM_HIGH)
  end
endtask : monitor_reset

task nvm_otp_key_monitor::collect_trans();
  // A request is pending from the first cycle its line is seen high until its handshake.
  bit          pending[NumNvmOtpKeyKinds];
  int unsigned pending_cycles[NumNvmOtpKeyKinds];

  forever begin
    @(cfg.vif.mon_cb);
    if (cfg.in_reset) begin
      pending = '{default: 1'b0};
      continue;
    end

    for (int i = 0; i < NumNvmOtpKeyKinds; i++) begin
      nvm_otp_key_kind_e kind = nvm_otp_key_kind_e'(i);
      bit req, ack;
      sample_lines(kind, req, ack);

      if (req && !pending[i]) begin
        pending[i]        = 1'b1;
        pending_cycles[i] = 0;
        write_req(kind);
      end

      if (pending[i]) begin
        if (req && ack) begin
          write_handshake(kind, pending_cycles[i]);
          pending[i] = 1'b0;
        end else begin
          pending_cycles[i]++;
        end
      end
    end
  end
endtask : collect_trans

task nvm_otp_key_monitor::monitor_ready_to_end();
  forever begin
    ok_to_end = !(cfg.vif.mon_cb.req.addr_req || cfg.vif.mon_cb.req.data_req);
    @(cfg.vif.mon_cb);
  end
endtask : monitor_ready_to_end

function void nvm_otp_key_monitor::sample_lines(nvm_otp_key_kind_e kind,
                                                output bit req,
                                                output bit ack);
  if (kind == NvmOtpKeyAddr) begin
    req = cfg.vif.mon_cb.req.addr_req;
    ack = cfg.vif.mon_cb.rsp.addr_ack;
  end else begin
    req = cfg.vif.mon_cb.req.data_req;
    ack = cfg.vif.mon_cb.rsp.data_ack;
  end
endfunction : sample_lines

function void nvm_otp_key_monitor::write_req(nvm_otp_key_kind_e kind);
  nvm_otp_key_item item = nvm_otp_key_item::type_id::create("req_item");
  item.kind = kind;
  `uvm_info(`gfn, $sformatf("%0s key requested", kind.name()), UVM_HIGH)
  req_analysis_port.write(item);
endfunction : write_req

function void nvm_otp_key_monitor::write_handshake(nvm_otp_key_kind_e kind,
                                                   int unsigned       req_to_ack_cycles);
  nvm_otp_key_item item = nvm_otp_key_item::type_id::create("item");
  item.kind              = kind;
  item.key               = cfg.vif.mon_cb.rsp.key;
  item.rand_key          = cfg.vif.mon_cb.rsp.rand_key;
  item.seed_valid        = cfg.vif.mon_cb.rsp.seed_valid;
  item.req_to_ack_cycles = req_to_ack_cycles;
  `uvm_info(`gfn, $sformatf("Handshake complete:\n%0s", item.sprint()), UVM_MEDIUM)
  analysis_port.write(item);
  if (cfg.en_cov) cov.handshake_cg.sample(item);
endfunction : write_handshake
