// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class mbx_stress_vseq extends mbx_base_vseq;

  `uvm_object_utils(mbx_stress_vseq)

  // Constrain the iteration and transaction counts to produce a longer stress test and,
  // importantly, perform multiple request and responses without an intervening block reset.
  constraint num_iters_c { num_iters inside {[5:8]}; }
  constraint num_txns_c { num_txns inside {[2:12]}; }

  // Whether to produce these stimuli to stress the DUT.
  rand bit aborts_en;  // Aborts from the SoC side.
  rand bit errors_en;  // Errors from the Core side.
  rand bit panics_en;  // FW-initiated reset/Abort clear from the Core side.

  constraint stressors_en_c {
    aborts_en dist {0:/75, 1:/25};
    errors_en dist {0:/75, 1:/25};
    panics_en dist {0:/75, 1:/25};
  }

  // TODO: decide how often errors and aborts should be generated; sequences shall probably want
  // to override the behavior, but we shall also want some kind of sensible default. Perhaps
  // randomize the number of clock cycles until we raise an abort, rather than treating each clock
  // cycle as an independent event?

  // Raise an Abort request from the SoC side?
  virtual task do_abort(ref bit aborted);
    if (aborts_en && !($urandom() % 1024)) begin
      `uvm_info(`gfn, "Setting ABORT condition", UVM_LOW)
      mbx_abort();
      aborted = 1'b1;
    end
  endtask

  // Raise an Error from the Core side?
  virtual task do_error(ref bit errored);
    if (errors_en && !($urandom() % 1024)) begin
      `uvm_info(`gfn, "Setting ERROR condition", UVM_LOW)
      ral.control.error.set(1'b1);
      csr_update(ral.control);
      errored = 1'b1;
    end
  endtask

  // Raise a FW-initiated Reset from the Core side?
  virtual task do_panic(ref bit panicked);
    if (panics_en && !($urandom() % 1024)) begin
      `uvm_info(`gfn, "Setting FW RESET/ABORT ACK condition", UVM_LOW)
      ral.control.abort.set(1'b1);
      csr_update(ral.control);
      panicked = 1'b1;
    end
  endtask

  // Decide upon the access delays for this transaction.
  virtual function bit choose_access_delays(output int min_acc_delay, output int max_acc_delay);
    min_acc_delay = $urandom_range(0, 5);
    max_acc_delay = $urandom_range(min_acc_delay, 20);
    return 1'b1;
  endfunction

  virtual function bit choose_response_delays(output int min_rsp_delay, output int max_rsp_delay);
    min_rsp_delay = $urandom_range(0, 5);
    max_rsp_delay = $urandom_range(min_rsp_delay, 20);
    return 1'b1;
  endfunction

  function new(string name = "mbx_stress_vseq");
    super.new(name);
  endfunction : new

  virtual task body();
    `uvm_info(get_full_name(), "body -- stress test -- Start", UVM_DEBUG)

    `uvm_info(`gfn, $sformatf("aborts_en = %0b", aborts_en), UVM_LOW)
    `uvm_info(`gfn, $sformatf("errors_en = %0b", errors_en), UVM_LOW)
    `uvm_info(`gfn, $sformatf("panics_en = %0b", panics_en), UVM_LOW)

    super.body();
    `uvm_info(get_full_name(), "body -- stress test -- End", UVM_DEBUG)
  endtask : body

endclass : mbx_stress_vseq
