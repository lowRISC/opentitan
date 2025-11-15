// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A predictor for the arbiter that listens to updates in the error_logs at racl_error_i and
// racl_error_external_i.

class racl_ctrl_error_arb_predictor extends uvm_component;
  `uvm_component_utils(racl_ctrl_error_arb_predictor)

  typedef uvm_tlm_analysis_fifo #(racl_error_log_item)     error_fifo_t;
  typedef uvm_tlm_analysis_fifo #(racl_error_log_vec_item) error_vec_fifo_t;

  // A handle to the environment cfg
  racl_ctrl_env_cfg cfg;

  // Analysis fifos for messages from the monitors of the two error log agents.
  error_vec_fifo_t internal_errors_fifo;
  error_vec_fifo_t external_errors_fifo;

  // An output with merged errors
  error_fifo_t merged_errors_fifo;

  extern function new(string name, uvm_component parent);
  extern function void build_phase(uvm_phase phase);
  extern task run_phase(uvm_phase phase);

  // Update the model to match a reset of racl_ctrl
  extern task on_reset();

  // Watch error inputs, collecting up values in the two fifos and pairing them up.
  extern local task watch_errors();

  // Flush the contents of a nonempty fifo of racl_error_log_vec_item objects and return the last
  // item that had been in there.
  extern local function racl_error_log_vec_item flush_vec_fifo(error_vec_fifo_t fifo);
endclass

function racl_ctrl_error_arb_predictor::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction

function void racl_ctrl_error_arb_predictor::build_phase(uvm_phase phase);
  internal_errors_fifo = new("internal_errors_fifo", this);
  external_errors_fifo = new("external_errors_fifo", this);
  merged_errors_fifo = new("merged_errors_fifo", this);
endfunction

task racl_ctrl_error_arb_predictor::run_phase(uvm_phase phase);
  fork
    super.run_phase(phase);
    watch_errors();
  join
endtask

task racl_ctrl_error_arb_predictor::on_reset();
  internal_errors_fifo.flush();
  external_errors_fifo.flush();
  merged_errors_fifo.flush();
endtask

task racl_ctrl_error_arb_predictor::watch_errors();
  forever begin
    racl_error_log_item items[int unsigned];
    bit                 saw_internal, saw_external;

    // Wait until something appears in a fifo. Since the two fifos are on the same clock, we add a
    // tiny delay to collect both sides if something turns up in both at the same time.
    fork begin : isolation_fork
      fork
        begin
          racl_error_log_vec_item internal_item;
          internal_errors_fifo.peek(internal_item);
          saw_internal = 1'b1;
          #1ps;
        end
        begin
          racl_error_log_vec_item external_item;
          external_errors_fifo.peek(external_item);
          saw_external = 1'b1;
          #1ps;
        end
      join_any
      disable fork;
    end join

    // At this point we're just after a clock edge and we have seen an error log item on at least
    // one fifo. Pair up the last item on each of the two inputs, writing its components to items.
    if (saw_internal) begin
      racl_error_log_vec_item vec_item = flush_vec_fifo(internal_errors_fifo);
      foreach (vec_item.errors[i]) begin
        `DV_CHECK(`gfn, i < cfg.internal_error_agent_cfg.num_subscribing_ips)
        items[i] = vec_item.errors[i];
      end
    end
    if (saw_external) begin
      racl_error_log_vec_item vec_item = flush_vec_fifo(external_errors_fifo);
      `DV_CHECK_FATAL(vec_item != null)
      foreach (vec_item.errors[i]) begin
        `DV_CHECK(`gfn, i < cfg.external_error_agent_cfg.num_subscribing_ips)
        items[cfg.internal_error_agent_cfg.num_subscribing_ips + i] = vec_item.errors[i];
      end
    end

    // We've now got a single array of errors in items and it's time to do the arbitration. Take the
    // first error, which will be the first item in the array, but unconditionally register an
    // overflow if there is more than one item.
    begin
      int unsigned first_idx;
      uvm_object   arb_item_obj;
      racl_error_log_item arb_item;

      `DV_CHECK(items.first(first_idx));
      `downcast(arb_item, items[first_idx].clone())
      arb_item.overflow |= items.size() > 1;

      merged_errors_fifo.write(arb_item);
    end
  end
endtask

function racl_error_log_vec_item
  racl_ctrl_error_arb_predictor::flush_vec_fifo(error_vec_fifo_t fifo);

  racl_error_log_vec_item ret;
  while (!fifo.is_empty()) `DV_CHECK_FATAL(fifo.try_get(ret))
  `DV_CHECK_FATAL(ret != null)
  return ret;
endfunction
