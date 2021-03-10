// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class sram_ctrl_smoke_vseq extends sram_ctrl_base_vseq;
  `uvm_object_utils(sram_ctrl_smoke_vseq)

  `uvm_object_new

  // Indicates the number of memory accesses to be performed
  // before requesting a new scrambling key
  rand int num_ops;

  // Indicates the number of memory accesses to be performed
  // when SRAM comes out of reset
  rand int num_ops_after_reset;

  // An SRAM "transaction" is a full round of:
  //  - Provisioning a new scrambling key from OTP
  //  - Executing a random number of memory accesses to SRAM
  constraint num_trans_c {
    num_trans == 1;
  }

  // TODO: 10_000 iterations takes roughly 150s CPU time during simulation.
  //       If this is too much, modify the constraint.
  constraint num_ops_c {
    num_ops dist {
      [1    : 999 ] :/ 1,
      [1000 : 4999] :/ 3,
      [5000 : 9999] :/ 5,
      10_000        :/ 1
    };
  }

  // This can be much smaller than `num_ops`, as we only perform some memory accesses
  // after reset to make sure that things are working normally.
  constraint num_ops_after_reset_c {
    num_ops_after_reset inside {[20 : 50]};
  }

  task body();

    // do some memory transactions right after reset (zeroed key and nonce)
    `uvm_info(`gfn,
              $sformatf("Performing %0d random memory accesses after reset!", num_ops_after_reset),
              UVM_LOW)
    do_rand_ops(num_ops_after_reset);

    `uvm_info(`gfn, $sformatf("Starting %0d SRAM transactions", num_trans), UVM_LOW)
    for (int i = 0; i < num_trans; i++) begin
      `uvm_info(`gfn, $sformatf("iteration: %0d", i), UVM_LOW)

      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(num_ops)

      // Request a new scrambling key
      req_scr_key();

      // wait for a valid KDI transaction to be completed
      //
      // STATUS.scr_key_seed_valid return value will be checked by scoreboard
      csr_spinwait(.ptr(ral.status.scr_key_valid), .exp_data(1'b1));

      // Do some random memory accesses
      `uvm_info(`gfn,
                $sformatf("Performing %0d random memory accesses!", num_ops),
                UVM_LOW)
      if (stress_pipeline) begin
        for (int i = 0; i < num_ops; i++) begin
          do_stress_ops($urandom(), $urandom_range(5, 20));
        end
      end else begin
        do_rand_ops(num_ops);
      end
    end
  endtask : body

endclass : sram_ctrl_smoke_vseq
