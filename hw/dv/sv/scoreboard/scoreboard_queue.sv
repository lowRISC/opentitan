// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class scoreboard_queue#(type SEQ_ITEM = uvm_object) extends uvm_object;

  SEQ_ITEM           expected_items[$];
  SEQ_ITEM           actual_items[$];
  bit [63:0]         expected_items_timestamp[$];
  bit [63:0]         actual_items_timestamp[$];
  checking_policy_e  policy;
  semaphore          token;
  // Maximum pending items in the queue, 0 means unlimited.
  int unsigned       max_pending_items;
  uvm_comparer       out_of_order_comparator;
  // Statistic counter
  int unsigned       num_of_check_pass;
  int unsigned       num_of_check_fail;

  `uvm_object_param_utils(scoreboard_queue#(SEQ_ITEM))

  function new(string name = "");
    super.new(name);
    token = new(1);
    // Setup comparator for out-of-order checking
    out_of_order_comparator = new();
    // Use high verbosity for out-of-order checking mismatches since it may not be a
    // real issue.
    out_of_order_comparator.verbosity = UVM_HIGH;
  endfunction

  task add_expected_item(SEQ_ITEM tr, bit [63:0] current_cycle_cnt);
    token.get(1);
    if (max_pending_items > 0) begin
      if (expected_items.size() > max_pending_items) begin
        `uvm_error(get_full_name(), $sformatf("Number of expected items %0d exceeds limit %0d",
                         expected_items.size(), max_pending_items))
      end
    end
    expected_items.push_back(tr);
    expected_items_timestamp.push_back(current_cycle_cnt);
    if (actual_items.size() != 0) void'(check_item());
    token.put(1);
  endtask

  task add_actual_item(SEQ_ITEM tr, bit [63:0] current_cycle_cnt);
    token.get(1);
    if (max_pending_items > 0) begin
      if (actual_items.size() > max_pending_items) begin
        `uvm_error(get_full_name(), $sformatf("Number of actected items %0d exceeds limit %0d",
                         actual_items.size(), max_pending_items))
      end
    end
    actual_items.push_back(tr);
    actual_items_timestamp.push_back(current_cycle_cnt);
    if (expected_items.size() != 0) void'(check_item());
    token.put(1);
  endtask

  virtual function bit check_item();
    if (expected_items.size() == 0 || actual_items.size() == 0) begin
      `uvm_error(get_full_name(), $sformatf(
        "Cannot check with empty queue, expected items: %0d, actual items: %0d",
        expected_items.size(),  actual_items.size()))
      return 1'b0;
    end
    case(policy)
      // In order check : compare the first item in the expected and actual item queue
      kInOrderCheck: begin
        bit check_pass;
        if (actual_items[0].compare(expected_items[0])) begin
          `uvm_info(get_full_name(), $sformatf(
                    "IN ORDER CHECK PASS:\n Expected item:\n%0s Actual item:\n%0s",
                    expected_items[0].sprint(), actual_items[0].sprint()), UVM_HIGH)
           num_of_check_pass++;
           check_pass = 1'b1;
        end else begin
          `uvm_error(get_full_name(), $sformatf(
                     "IN ORDER CHECK FAIL:\n Expected item:\n%0s Actual item:\n%0s",
                     expected_items[0].sprint(), actual_items[0].sprint()))
           num_of_check_fail++;
           check_pass = 1'b0;
        end
        void'(actual_items.pop_front());
        void'(actual_items_timestamp.pop_front());
        void'(expected_items.pop_front());
        void'(expected_items_timestamp.pop_front());
        return check_pass;
      end
      // Out of order check: search through the expected item queue to find an item that matches
      // the first actual item
      kOutOfOrderCheck: begin
        foreach(expected_items[i]) begin
          if (actual_items[0].compare(expected_items[i], out_of_order_comparator)) begin
            `uvm_info(get_full_name(),
                $sformatf("OUT OF ORDER CHECK PASS:\n Expected item[%0d]:\n%0s Actual item:\n%0s",
                i, expected_items[i].sprint(), actual_items[0].sprint()), UVM_HIGH)
            void'(actual_items.pop_front());
            void'(actual_items_timestamp.pop_front());
            expected_items.delete(i);
            expected_items_timestamp.delete(i);
            num_of_check_pass++;
            return 1'b1;
          end
        end
        `uvm_error(get_full_name(), $sformatf(
                "OUT OF ORDER CHECK FAIL: Cannot find any item matching:\n%0s",
                actual_items[0].sprint()))
        void'(actual_items.pop_front());
        void'(actual_items_timestamp.pop_front());
        num_of_check_fail++;
        return 1'b0;
      end
      // Custom checking policy
      kCustomCheck: begin
        void'(custom_check());
      end
      default: begin
        `uvm_error(get_full_name(), $sformatf("%0s check policy is not supported", policy.name()))
        return 1'b0;
      end
    endcase
  endfunction

  virtual function bit custom_check();
    `uvm_fatal(get_full_name(), "custom_check must be implemented for kCustomCheck policy")
  endfunction

  // delete all the queues once reset
  virtual function void reset();
    expected_items.delete();
    actual_items.delete();
    expected_items_timestamp.delete();
    actual_items_timestamp.delete();
  endfunction

  // check all the queues are empty at the end of simulation
  virtual function void final_queue_size_check(string queue_name);
    `DV_CHECK_EQ(expected_items.size(),           0, {queue_name, "::expected_items"})
    `DV_CHECK_EQ(actual_items.size(),             0, {queue_name, "::actual_items"})
    `DV_CHECK_EQ(expected_items_timestamp.size(), 0, {queue_name, "::expected_items_timestamp"})
    `DV_CHECK_EQ(actual_items_timestamp.size(),   0, {queue_name, "::actual_items_timestamp"})
  endfunction
endclass
