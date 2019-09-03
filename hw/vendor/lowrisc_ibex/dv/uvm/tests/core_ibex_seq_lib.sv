// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Base sequence
class core_base_seq #(type REQ = uvm_sequence_item) extends uvm_sequence#(REQ);

  rand int unsigned  interval;
  rand int unsigned  delay;
  int unsigned       num_of_iterations; // 0: infinite until stopped
  int unsigned       iteration_cnt;
  int unsigned       max_interval;
  int unsigned       max_delay = 500;
  virtual clk_if     clk_vif;
  bit                stop_seq;
  bit                seq_finished;

  `uvm_object_param_utils(core_base_seq#(REQ))
  `uvm_object_new

  constraint reasonable_interval_c {
    interval dist {[0                 : max_interval/10]    :/ 1,
                   [max_interval/10   : 9*max_interval/10]  :/ 1,
                   [9*max_interval/10 : max_interval]       :/ 1
    };
  }

  constraint reasonable_delay_c {
    delay inside {[max_delay/10 : max_delay]};
  }

  virtual task body();
    if(!uvm_config_db#(virtual clk_if)::get(null, "", "clk_if", clk_vif)) begin
       `uvm_fatal(get_full_name(), "Cannot get clk_if")
    end
    void'(randomize(delay));
    clk_vif.wait_clks(delay);
    `uvm_info(get_full_name(), "Starting sequence...", UVM_LOW)
    while (!stop_seq) begin
      send_req();
      iteration_cnt++;
      void'(randomize(interval));
      clk_vif.wait_clks(interval);
      if (num_of_iterations > 0 && iteration_cnt >= num_of_iterations) begin
        break;
      end
    end
    seq_finished = 1'b1;
    `uvm_info(get_full_name(), "Exiting sequence", UVM_LOW)
  endtask

  virtual task send_req();
    `uvm_fatal(get_full_name(), "This task must be implemented in the extended class")
  endtask

  virtual task stop();
    stop_seq = 1'b1;
    `uvm_info(get_full_name(), "Stopping sequence", UVM_LOW)
    wait (seq_finished == 1'b1);
  endtask

endclass

// Interrupt sequence
class irq_seq extends core_base_seq#(irq_seq_item);

  `uvm_object_utils(irq_seq)
  `uvm_object_new

  virtual task send_req();
    irq_seq_item irq;
    irq = irq_seq_item::type_id::create($sformatf("irq[%0d]", iteration_cnt));
    start_item(irq);
    `DV_CHECK_RANDOMIZE_FATAL(irq)
    finish_item(irq);
    get_response(irq);
  endtask

endclass

// Simple debug sequence
// debug_req is just a single bit sideband signal, use the interface to drive it directly
class debug_seq extends core_base_seq;

  virtual core_ibex_dut_probe_if dut_vif;

  `uvm_object_utils(debug_seq)
  `uvm_object_new

  virtual task body();
    if (!uvm_config_db#(virtual core_ibex_dut_probe_if)::get(null, "", "dut_if", dut_vif)) begin
      `uvm_fatal(get_full_name(), "Cannot get dut_if")
    end
    dut_vif.debug_req <= 1'b0;
    super.body();
  endtask

  virtual task send_req();
    `uvm_info(get_full_name(), "Sending debug request", UVM_HIGH)
    dut_vif.debug_req <= 1'b1;
    clk_vif.wait_clks($urandom_range(10, 30));
    dut_vif.debug_req <= 1'b0;
  endtask

endclass
