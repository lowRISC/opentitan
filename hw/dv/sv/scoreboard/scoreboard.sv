// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Multi queues scoreboard
// - Collect items from variable number of source and destination ports and perform
//   queue based checking.
// - Support configure checking policy for each queue
//   - In order checking, out of order checking, custom checking
// - Support multi-cast
// - Support data transform from source to destination

class scoreboard#(type ITEM_T = uvm_object,
                  type RAL_T  = dv_base_reg_block,
                  type CFG_T  = dv_base_env_cfg,
                  type COV_T  = dv_base_env_cov) extends dv_base_scoreboard#(RAL_T, CFG_T, COV_T);

  uvm_tlm_analysis_fifo #(ITEM_T)   item_fifos[string];
  // Port direction
  port_dir_e                        port_dir[string];
  // Queues for pending items
  scoreboard_queue#(ITEM_T)         item_queues[string];
  int unsigned                      timeout_cycle_limit = 10000;
  bit [63:0]                        ref_timer;
  bit [63:0]                        last_activity_cycle;
  int unsigned                      num_of_exp_item;
  int unsigned                      num_of_act_item;
  int unsigned                      timeout_check_cycle_interval = 100;
  bit                               enable_logging = 1'b0;
  uvm_phase                         run_phase_h;
  semaphore                         token;
  string                            log_filename;
  int                               log_fd;
  virtual clk_rst_if                clk_vif;
  bit                               allow_packet_drop;
  bit                               disable_scoreboard;

  `uvm_component_param_utils(scoreboard#(ITEM_T, dv_base_reg_block,
                                         dv_base_env_cfg, dv_base_env_cov))
  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    void'($value$plusargs("scb_logging=%d", enable_logging));
    if (!uvm_config_db#(virtual clk_rst_if)::get(this, "", "clk_rst_vif", clk_vif)) begin
      `uvm_fatal(get_full_name(), "Cannot get clk interface")
    end
    if (enable_logging) begin
      log_filename = {get_full_name(), ".log"};
      `uvm_info(get_full_name(), $sformatf(
                "Transaction logging enabled, log will be saved to %0s", log_filename), UVM_LOW)
      log_fd = $fopen(log_filename, "w");
    end
    // Add a default in order check queue
    add_item_queue("default");
    token = new(1);
  endfunction

  virtual function void add_item_port(string port_name, port_dir_e direction);
    if (item_fifos.exists(port_name)) begin
      `uvm_error(get_full_name(), $sformatf(
                 "Port %0s already exists, cannot be added again", port_name))
    end
    `uvm_info(get_full_name(), $sformatf(
              "Adding port :%0s(%0s)", port_name, direction.name()), UVM_HIGH)
    port_dir[port_name] = direction;
    item_fifos[port_name] = new(port_name, this);
  endfunction

  virtual function void add_item_queue(string queue_name,
                                       checking_policy_e policy = kInOrderCheck);
    if (item_queues.exists(queue_name)) begin
      `uvm_fatal(get_full_name(), $sformatf(
                 "Queue %0s already exists, cannot be added again", queue_name))
    end
    `uvm_info(get_full_name(), $sformatf(
              "Adding queue :%0s(%0s)", queue_name, policy.name()), UVM_HIGH)
    item_queues[queue_name] = scoreboard_queue#(ITEM_T)::type_id::
                              create($sformatf("%0s_%0s", get_full_name(), queue_name));
    item_queues[queue_name].policy = policy;
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    run_phase_h = phase;
    if (disable_scoreboard) return;
    fork
      timeout_monitor();
      ref_timer_thread();
    join_none
    foreach(item_fifos[port_name]) begin
      fork
        automatic string t_port_name = port_name;
        port_monitor(t_port_name);
      join_none
    end
    wait fork;
  endtask: run_phase

  // Collect items from analysis FIFO, send to corresponding queues
  virtual task port_monitor(string port_name);
    ITEM_T tr;
    ITEM_T transformed_tr[$];
    string queue_name;
    while(1) begin
      item_fifos[port_name].get(tr);
      last_activity_cycle = ref_timer;
      `uvm_info(get_full_name(), $sformatf("Got an item from port %0s:\n%0s",
                port_name, tr.sprint()), UVM_HIGH)
      if (port_dir[port_name] == kSrcPort) begin
        process_src_packet(tr, port_name, transformed_tr);
        foreach(transformed_tr[i]) begin
          queue_name = get_queue_name(transformed_tr[i], port_name);
          // destination ports
          if (!item_queues.exists(queue_name)) begin
             `uvm_fatal(get_full_name(), $sformatf("%0s queue doesn't exist", queue_name))
          end
          if (enable_logging) begin
            $fwrite(log_fd, $sformatf("EXP @%0t [%0s][%0s] %0s\n", $realtime, port_name,
                                     queue_name, transformed_tr[i].convert2string()));
          end
          token.get();
          num_of_exp_item++;
          token.put();
          item_queues[queue_name].add_expected_item(transformed_tr[i], ref_timer);
        end
      end else begin
        ITEM_T tr_modified;
        queue_name = get_queue_name(tr, port_name);
        // destination ports
        if (!item_queues.exists(queue_name)) begin
           `uvm_fatal(get_full_name(), $sformatf("%0s queue doesn't exist", queue_name))
        end
        process_dst_packet(tr, port_name, tr_modified);
        #0; // avoid race condition when item is received in both queue in same cycle
        if (enable_logging) begin
          $fwrite(log_fd, $sformatf("ACT @%0t [%0s][%0s] %0s\n", $realtime, port_name,
                                     queue_name, tr_modified.convert2string()));
        end
        token.get();
        num_of_act_item++;
        token.put();
        item_queues[queue_name].add_actual_item(tr_modified, ref_timer);
      end
    end
  endtask

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    if ((num_of_act_item != num_of_exp_item) && !allow_packet_drop) begin
      `uvm_error(get_full_name(), $sformatf("Expected item cnt %0d != actual item cnt %0d",
                 num_of_exp_item, num_of_act_item))
      foreach(item_queues[queue_name]) begin
        `uvm_info(get_full_name(), $sformatf("Queue[%0s] expected items %0d, actual items %0d",
                  queue_name, item_queues[queue_name].expected_items.size(),
                  item_queues[queue_name].actual_items.size()), UVM_LOW)
      end
    end else begin
      `uvm_info(get_full_name(), $sformatf("Totally %0d items processed",
                 num_of_act_item), UVM_LOW)
    end
    foreach (item_queues[i]) item_queues[i].final_queue_size_check(i);
    foreach (item_fifos[i]) `DV_EOT_PRINT_TLM_FIFO_CONTENTS(ITEM_T, item_fifos[i]);
  endfunction

  // Transform the original item before sending to queue
  // - Support original transaction fields modification
  // - Support multi-cast original transaction to multiple destinations
  // This step is optional, the default implementation is pass through the original
  // transaction without any modification.
  virtual function void process_src_packet(input ITEM_T  tr,
                                           input string  port_name,
                                           output ITEM_T transformed_tr[$]);
    transformed_tr = {tr};
  endfunction

  // Process the destination packet before comparing
  virtual function void process_dst_packet(input ITEM_T  tr,
                                           input string  port_name,
                                           output ITEM_T transformed_tr);
    transformed_tr = tr;
  endfunction

  // Get scoreboard queue name based on the transaction and port name
  // This function should be implemented with actual transaction to queue mapping
  virtual function string get_queue_name(ITEM_T tr, string port_name);
    return "default";
  endfunction

  // Scoreboard timeout detection
  virtual task timeout_monitor;
    if (timeout_cycle_limit > 0) begin
      while(1) begin
        repeat(timeout_check_cycle_interval) @(posedge clk_vif.clk);
        if ((ref_timer - last_activity_cycle > timeout_cycle_limit) &&
           (num_of_act_item != num_of_exp_item)) begin
          if (!allow_packet_drop) begin
            `uvm_error(get_full_name(), $sformatf("Scoreboard timeout, act/exp items = %0d/%0d",
                                       num_of_act_item, num_of_exp_item))
            foreach(item_queues[q]) begin
              if (item_queues[q].expected_items.size() > 0) begin
                `uvm_info(get_full_name(), $sformatf("Queue[%0s] pending item[0]:%0s", q,
                          item_queues[q].expected_items[0].convert2string()), UVM_LOW)
              end
            end
          end else begin
            `uvm_info(get_full_name(), $sformatf(
                      "Scoreboard timeout caused by packet drop, act/exp items = %0d/%0d",
                      num_of_act_item, num_of_exp_item), UVM_LOW)
          end
        end
      end
    end
  endtask

  virtual task ref_timer_thread();
    ref_timer = 0;
    forever begin
      @(posedge clk_vif.clk);
      ref_timer++;
    end
  endtask

  virtual function void reset(string kind = "HARD");
    last_activity_cycle = ref_timer;
    foreach (item_fifos[i])  item_fifos[i].flush();
    foreach (item_queues[i]) item_queues[i].reset();
    num_of_act_item = 0;
    num_of_exp_item = 0;
  endfunction

endclass
