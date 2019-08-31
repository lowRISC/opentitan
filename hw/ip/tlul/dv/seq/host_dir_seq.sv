// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
class host_dir_seq extends xbar_seq_base;

  function new(string name);
    super.new(name);
  endfunction : new

  task body();
    logic [31:0] rdata, rdata2;

    write('h4, 'h DEAD_BEEF, 'hF);

    read('h4, rdata);
    $display("Data received");
    assert(rdata == 'h DEAD_BEEF)
      else $error("Data mismatch: ADDR(0x%08x) EXP(0x%08x) GOT(0x%08x)",
      'h4, 'h DEAD_BEEF, rdata);

    // Read back twice to check if correct randomized data received
    read('hFF0, rdata);
    read('hFF0, rdata2);

    assert(rdata == rdata2)
      else $error("Read twice test failed: ADDR(0x%08x) RD1(0x%08x) RD2(0x%08x)",
      'hFF0, rdata, rdata2);

  endtask : body

endclass
