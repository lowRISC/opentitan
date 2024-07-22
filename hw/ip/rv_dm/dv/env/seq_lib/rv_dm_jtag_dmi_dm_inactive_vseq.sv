// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_jtag_dmi_dm_inactive_vseq extends rv_dm_common_vseq;
  `uvm_object_utils(rv_dm_jtag_dmi_dm_inactive_vseq)
  `uvm_object_new

  // Write random data to the given register
  task randomise_register(input uvm_object ptr);
    uvm_reg_data_t wdata = $urandom_range(0, 1000);
    csr_wr(.ptr(ptr), .value(wdata));
  endtask

  // Check that the given register has its reset value
  task check_rst_value(input uvm_object ptr);
    uvm_reg as_reg;
    uvm_reg_data_t rdata;

    `DV_CHECK_FATAL($cast(as_reg, ptr));

    csr_rd(.ptr(ptr), .value(rdata));
    `DV_CHECK_EQ(rdata, as_reg.get_reset());
  endtask

  task body();
    uvm_object ptrs[] = {jtag_dmi_ral.abstractdata[0],
                         jtag_dmi_ral.abstractdata[1],
                         jtag_dmi_ral.progbuf[0],
                         jtag_dmi_ral.progbuf[1]};
    bit is_active = 1'b0;

    // Start by setting dmactive=0, which should put the debug module into a reset state.
    csr_wr(.ptr(jtag_dmi_ral.dmcontrol.dmactive), .value(is_active), .blocking(1), .predict(1));

    repeat (20) begin
      uvm_object ptr = ptrs[$urandom_range(ptrs.size() - 1)];

      randcase
        10 * !is_active: randomise_register(.ptr(ptr));
        10:              check_rst_value(.ptr(ptr));
        1: begin
          is_active = !is_active;
          csr_wr(.ptr(jtag_dmi_ral.dmcontrol.dmactive),
                 .value(is_active), .blocking(1), .predict(1));
        end
      endcase

      if (cfg.stop_transaction_generators()) return;
    end
  endtask

endclass : rv_dm_jtag_dmi_dm_inactive_vseq
