// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_common_vseq extends chip_stub_cpu_base_vseq;
  `uvm_object_utils(chip_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  virtual task apply_reset(string kind = "HARD");
    // The CSR tests (handled by this class) need to wait until the rom_ctrl block has finished
    // running KMAC before they can start issuing reads and writes. Otherwise, they might write to a
    // KMAC register while KMAC is in operation. This would have no effect and a subsequent read
    // from the register would show a mismatched value. We handle this by considering rom_ctrl's
    // operation as "part of reset".
    //
    // Once the base class reset is finished, we're just after a chip reset. In a second, rom_ctrl
    // is going to start asking KMAC to do an operation. At that point, KMAC's CFG_REGWEN register
    // will go low. When the operation is finished, it will go high again. Wait until then.
    int unsigned rc_phase = 0;

    super.apply_reset(kind);

    `uvm_info(`gfn, "waiting for rom_ctrl after reset", UVM_MEDIUM)
    while (rc_phase < 2) begin
      bit [BUS_DW-1:0] rd_data;
      tl_access(.addr(ral.kmac.cfg_regwen.get_address()),
                .write(1'b0),
                .data(rd_data),
                .blocking(1'b1));
      if (rd_data[0] == rc_phase[0]) begin
        `uvm_info(`gfn, "KMAC's cfg_regwen has changed; bumping phase", UVM_HIGH)
        rc_phase++;
      end
    end
    `uvm_info(`gfn, "rom_ctrl done after reset", UVM_HIGH)
  endtask

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

endclass
