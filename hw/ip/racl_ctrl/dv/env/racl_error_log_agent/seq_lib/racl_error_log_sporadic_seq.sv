// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An infinite sequence that generates occasional single error log items. These alternate between
// "one error" and "no errors" and each item has a large delay.

class racl_error_log_sporadic_seq
  extends dv_base_seq #(.REQ        (racl_error_log_vec_driver_item),
                        .CFG_T      (racl_error_log_agent_cfg),
                        .SEQUENCER_T(racl_error_log_sequencer));

  `uvm_object_utils(racl_error_log_sporadic_seq)

  // If this bit is set then the sequence will finish as soon as is practical (completing as soon as
  // the driver finishes the current item, rather than starting the next item).
  local bit stopping;

  extern function new (string name="");

  extern task body();

  // Tell the sequence to stop sending new items to the driver. This does not cause an instant stop
  // if there is an item currently being driven (which may take a while, because of delays).
  // Instead, the task waits until the sequence is no longer running (either because it has finished
  // or because it has never been started).
  extern task request_end();
endclass

function racl_error_log_sporadic_seq::new(string name="");
  super.new(name);
endfunction

task racl_error_log_sporadic_seq::body();
  while (!stopping) begin
    racl_error_log_vec_driver_item item = racl_error_log_vec_driver_item::type_id::create("item");

    start_item(item);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(item,
                                   subscribers_with_errors.size() dist { 0 :/ 1, 1 :/ 10, 2 :/ 1 };
                                   foreach(subscribers_with_errors[i]) {
                                     subscribers_with_errors[i] < cfg.num_subscribing_ips;
                                   }
                                   delay dist { [1:99] :/ 1, [100:1000] :/ 10 };)
    finish_item(item);
  end
endtask

task racl_error_log_sporadic_seq::request_end();
  stopping = 1'b1;
  wait_for_sequence_state(UVM_CREATED | UVM_STOPPED | UVM_FINISHED);
endtask
