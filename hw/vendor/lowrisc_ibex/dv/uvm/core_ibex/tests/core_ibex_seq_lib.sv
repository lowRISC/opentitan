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
  virtual clk_rst_if clk_vif;
  bit                is_started;
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
    if(!uvm_config_db#(virtual clk_rst_if)::get(null, "", "clk_if", clk_vif)) begin
       `uvm_fatal(get_full_name(), "Cannot get clk_if")
    end
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(delay)
    clk_vif.wait_clks(delay);
    `uvm_info(get_full_name(), "Starting sequence...", UVM_LOW)
    if (!is_started) is_started = 1'b1;
    while (!stop_seq) begin
      send_req();
      iteration_cnt++;
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(interval)
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
    is_started = 1'b0;
  endtask

endclass

// Interrupt sequences

class irq_base_seq extends core_base_seq #(irq_seq_item);

  `uvm_object_utils(irq_base_seq)
  `uvm_object_new

  bit no_nmi;
  bit no_fast;

  virtual task send_req();
    irq_seq_item irq;
    irq = irq_seq_item::type_id::create($sformatf("irq_seq_item[%0d]", iteration_cnt));
    start_item(irq);
    randomize_item(irq);
    finish_item(irq);
    get_response(irq);
  endtask

  virtual function void randomize_item(irq_seq_item irq);
    `uvm_fatal(`gfn, "This task must be implemented in extended irq sequences")
  endfunction

endclass

class irq_raise_seq extends irq_base_seq;

  `uvm_object_utils(irq_raise_seq)
  `uvm_object_new

  bit no_nmi;
  bit no_fast;

  virtual function void randomize_item(irq_seq_item irq);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(irq, num_of_interrupt > 1;
                                        if (no_nmi) {
                                          irq_nm == 0;
                                        }
                                        if (no_fast) {
                                          irq_fast == '0;
                                        })
  endfunction

endclass

class irq_raise_single_seq extends irq_base_seq;

  `uvm_object_utils(irq_raise_single_seq)
  `uvm_object_new

  bit no_nmi;
  bit no_fast;

  virtual function void randomize_item(irq_seq_item irq);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(irq, num_of_interrupt == 1;
                                        if (no_nmi) {
                                          irq_nm == 0;
                                        }
                                        if (no_fast) {
                                          irq_fast == '0;
                                        })
  endfunction

endclass

class irq_raise_nmi_seq extends irq_base_seq;

  `uvm_object_utils(irq_raise_nmi_seq)
  `uvm_object_new

  virtual function void randomize_item(irq_seq_item irq);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(irq, num_of_interrupt == 1;
                                        irq_nm == 1;)
  endfunction

endclass

// Irq sequence to deassert all interrupt lines, since Ibex interrupts are level sensitive
class irq_drop_seq extends irq_base_seq;

  `uvm_object_utils(irq_drop_seq)
  `uvm_object_new

  // TODO(udinator) - for nested interrupt tests, test scenarios where a random number of interrupts
  // are dropped
  virtual function void randomize_item(irq_seq_item irq);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(irq, num_of_interrupt == 0;)
  endfunction

endclass

// Simple debug sequence
// debug_req is just a single bit sideband signal, use the interface to drive it directly
class debug_seq extends core_base_seq#(irq_seq_item);
  virtual core_ibex_dut_probe_if dut_vif;

  `uvm_object_utils(debug_seq)
  `uvm_object_new

  int unsigned drop_delay = 75;

  virtual task body();
    if (!uvm_config_db#(virtual core_ibex_dut_probe_if)::get(null, "", "dut_if", dut_vif)) begin
      `uvm_fatal(get_full_name(), "Cannot get dut_if")
    end
    dut_vif.dut_cb.debug_req <= 1'b0;
    super.body();
  endtask

  virtual task send_req();
    `uvm_info(get_full_name(), "Sending debug request", UVM_HIGH)
    dut_vif.dut_cb.debug_req <= 1'b1;
    clk_vif.wait_clks(drop_delay);
    dut_vif.dut_cb.debug_req <= 1'b0;
  endtask

endclass
