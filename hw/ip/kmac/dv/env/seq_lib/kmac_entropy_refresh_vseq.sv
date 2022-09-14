// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This sequence enables entropy refresh by changing the `entropy_refresh_c` constraint:
// 1). Allow `hash_threshold` to be any random value.
// 2). Allow `hash_cnt_clr` to clear the current hash_cnt.
// 2). Allow `entropy_req` to request another entropy data.
class kmac_entropy_refresh_vseq extends kmac_app_with_partial_data_vseq;

  `uvm_object_utils(kmac_entropy_refresh_vseq)
  `uvm_object_new

  constraint entropy_refresh_c {
    hash_cnt_clr dist {0 :/ 19, 1 :/ 1};
  }

  virtual task body();
    fork
      begin
        super.body();
      end
      begin
        repeat (10) begin
          int wait_cycs = $urandom_range(20_000, 100_000);
          cfg.clk_rst_vif.wait_clks(wait_cycs);
          csr_wr(.ptr(ral.cmd.entropy_req), .value(1));
        end
      end
    join
  endtask
endclass
