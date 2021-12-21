// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class sram_ctrl_smoke_vseq extends sram_ctrl_base_vseq;
  `uvm_object_utils(sram_ctrl_smoke_vseq)

  `uvm_object_new

  bit access_during_key_req = 0;

  bit en_ifetch = 0;

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

  constraint num_ops_c {
    if (cfg.smoke_test) {
      num_ops == 100;
    } else {
      num_ops dist {
        [1    : 999 ] :/ 1,
        [1000 : 4999] :/ 3,
        [5000 : 9999] :/ 5,
        10_000        :/ 1
      };
    }
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
    do_rand_ops(.num_ops(num_ops_after_reset),
                .en_ifetch(en_ifetch));

    `uvm_info(`gfn, $sformatf("Starting %0d SRAM transactions", num_trans), UVM_LOW)
    for (int i = 0; i < num_trans; i++) begin
      `uvm_info(`gfn, $sformatf("iteration: %0d", i), UVM_LOW)

      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(num_ops)

      if (access_during_key_req) begin
        // request new key or issue mem init, in the meanwhile, do some random SRAM operations
        fork
          begin
            // during key or init req, sram access shouldn't be taken
            randcase
              1: begin
                // If we only do scrambling without re-initializing the mem, data intg will be wrong
                // since it's data intg passthru mem, it doesn't matter, just don't check it.
                cfg.disable_d_user_data_intg_check_for_passthru_mem = 1;
                req_scr_key();
              end
              1: begin
                req_mem_init();
                cfg.disable_d_user_data_intg_check_for_passthru_mem = 0;
              end
            endcase
          end
          begin
            // add 2 cycles to avoid issuing key_scr/init and mem access happen at the same time,
            // as it's hard to handle this case in scb
            // Also need to enable zero_delays, otherwise, the CSR programming may take random
            // cycles to finish
            cfg.clk_rst_vif.wait_clks(2);
            `uvm_info(`gfn, "accessing during key req", UVM_HIGH)

            // SRAM init is basically to write all the mem with random value.
            // When a read happens right after init, it's read-after-write hazard. SCB expects the
            // read value is from memory directly, but it's actually from the last write of init.
            // To avoid this case, don't access the last address in this parallel `do_rand_ops`
            do_rand_ops(.num_ops($urandom_range(100, 500)),
                        .abort(1),
                        .en_ifetch(en_ifetch),
                        .not_use_last_addr(1));
            csr_utils_pkg::wait_no_outstanding_access();
          end
        join
      end else if ($urandom_range(0, 1)) begin
        req_mem_init();
      end


      // Do some random memory accesses
      `uvm_info(`gfn,
                $sformatf("Performing %0d random memory accesses!", num_ops),
                UVM_LOW)
      if (stress_pipeline) begin
        bit [TL_AW-1:0] stress_addr;
        for (int i = 0; i < num_ops; i++) begin
          `DV_CHECK_STD_RANDOMIZE_FATAL(stress_addr)
          do_stress_ops(stress_addr, $urandom_range(5, 20));
        end
      end else begin
        do_rand_ops(.num_ops(num_ops),
                    .en_ifetch(en_ifetch));
      end
    end
    csr_utils_pkg::wait_no_outstanding_access();
  endtask : body

endclass : sram_ctrl_smoke_vseq
