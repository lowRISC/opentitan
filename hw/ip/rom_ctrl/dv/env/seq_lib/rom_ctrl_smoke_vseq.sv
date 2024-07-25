// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rom_ctrl_smoke_vseq extends rom_ctrl_base_vseq;
  `uvm_object_utils(rom_ctrl_smoke_vseq)
  `uvm_object_new

  task body();
    bit send_expected = $urandom_range(0, 1);

    // Tell the KMAC app agent whether generate the digest that was expected in the ROM.
    configure_kmac_digest(send_expected);

    // Queue up some memory operations. These will block until the rom check completes.
    do_rand_ops($urandom_range(20, 50));

    // Read all the digest and exp_digest registers, checking they match the values we expect.
    read_digest_regs();
  endtask : body

endclass : rom_ctrl_smoke_vseq
