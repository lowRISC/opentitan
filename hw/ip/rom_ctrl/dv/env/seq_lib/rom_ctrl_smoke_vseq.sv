// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class rom_ctrl_smoke_vseq extends rom_ctrl_base_vseq;
  `uvm_object_utils(rom_ctrl_smoke_vseq)

  `uvm_object_new

  task body();
    do_rand_ops($urandom_range(20, 50));
    read_digest_regs();
    dut_init();
    configure_kmac_digest(1'b1);
    do_rand_ops($urandom_range(20, 50));
    read_digest_regs();
  endtask : body

endclass : rom_ctrl_smoke_vseq
