// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// one thread running the hmac_stress_all sequence
// another thread randomly insert reset
// after reset, check if all readable csrs are set to default reset value

class hmac_reset_vseq extends hmac_base_vseq;
  `uvm_object_utils(hmac_reset_vseq)

  rand uint delay;

  `uvm_object_new

  constraint delay_c {
    delay dist {
      0                   :/ 1,
      [1      :100]       :/ 1,
      [101    :10_000]    :/ 8,
      [10_001 :1_000_000] :/ 1
    };
  }

  task body();
    for (int i = 1; i <= num_trans; i++) begin
      bit reset_flag;
      fork
        begin : seq_wo_reset
          hmac_stress_all_vseq hmac_vseq = new;

          // dut_init (reset) is skipped because reset is randomly asserted in the reset thread
           if (i > 0) hmac_vseq.do_dut_init = 0;

          hmac_vseq.set_sequencer(p_sequencer);
          `DV_CHECK_RANDOMIZE_FATAL(hmac_vseq)
          hmac_vseq.start(p_sequencer);
        end

        begin : reset
          `DV_CHECK_MEMBER_RANDOMIZE_FATAL(delay)
          cfg.clk_rst_vif.wait_clks(delay);
          csr_utils_pkg::wait_no_outstanding_access(); // TODO : temp wait, need support
          reset_flag = 1'b1;
        end
      join_any
      disable fork;

      if (reset_flag) begin // trigger reset
        `uvm_info(`gfn, "hmac_reset triggered", UVM_LOW)
        apply_reset("HARD");
        read_and_check_all_csrs();
        reset_flag = 1'b0;
      end
    end // end for loop
  endtask : body

endclass
