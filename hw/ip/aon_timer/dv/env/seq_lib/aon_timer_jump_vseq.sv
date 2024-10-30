// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// jump test vseq
class aon_timer_jump_vseq extends aon_timer_base_vseq;
  `uvm_object_utils(aon_timer_jump_vseq)

  // Overrides constraint in parent vseq:
  extern constraint thold_count_c;

  extern function new (string name="");
  extern task body();
  extern task jump_configure();

endclass : aon_timer_jump_vseq

constraint aon_timer_jump_vseq::thold_count_c {
  solve wkup_thold before wkup_count;
  solve aim_bite, wdog_bark_thold, wdog_bite_thold before wdog_count;
  wkup_thold      <= (2**64-1);
  wdog_bark_thold <= (2**32-1);
  wdog_bite_thold <= (2**32-1);

  wkup_count inside {[wkup_thold-10:wkup_thold+10]};
  !aim_bite -> wdog_count inside {[wdog_bark_thold-10:wdog_bark_thold+10]};
  aim_bite  -> wdog_count inside {[wdog_bite_thold-10:wdog_bite_thold+10]};
}

function aon_timer_jump_vseq::new (string name="");
  super.new(name);
endfunction : new

task aon_timer_jump_vseq::body();
  aon_timer_init();
  jump_configure();
  wait_for_interrupt();
  aon_timer_shutdown();
endtask : body

task aon_timer_jump_vseq::jump_configure();

  // Write random value to the COUNT registers
  csr_utils_pkg::csr_wr(ral.wkup_count_lo, wkup_count[31:0]);
  csr_utils_pkg::csr_wr(ral.wkup_count_hi, wkup_count[63:32]);
  `uvm_info(`gfn,
            $sformatf("\n\t Writing random COUNT value of %d to WKUP", wkup_count),
            UVM_HIGH)

  csr_utils_pkg::csr_wr(ral.wdog_count, wdog_count);
  `uvm_info(`gfn,
            $sformatf("\n\t Writing random COUNT value of %d to WDOG", wdog_count),
            UVM_HIGH)

  cfg.aon_clk_rst_vif.wait_clks(1);

  `uvm_info(`gfn, "Enabling AON Timer. Writing 1 to WKUP_CTRL and WDOG_CTRL", UVM_HIGH)
  csr_utils_pkg::csr_wr(ral.wdog_ctrl.enable, 1'b1);
  csr_utils_pkg::csr_wr(ral.wkup_ctrl.enable, 1'b1);

  `uvm_info(`gfn, "\n\t Waiting for AON Timer to finish (interrupt)", UVM_HIGH)
endtask : jump_configure
