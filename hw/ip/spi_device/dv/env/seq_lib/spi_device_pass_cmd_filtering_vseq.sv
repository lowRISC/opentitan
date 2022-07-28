// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Passthrough mode filtering of commands scenario, filter on and off
class spi_device_pass_cmd_filtering_vseq extends spi_device_pass_base_vseq;
  `uvm_object_utils(spi_device_pass_cmd_filtering_vseq)
  `uvm_object_new

  virtual task body();

    allow_set_cmd_info_invalid = 1;
    allow_use_invalid_opcode = 1;
    spi_device_flash_pass_init(PassthroughMode);

    for (int i = 0; i < num_trans; ++i) begin
      randomize_op_addr_size();
      `uvm_info(`gfn, $sformatf("running iteration %0d, test op = 0x%0h", i, opcode), UVM_LOW)

      // test 2 cases:
      //  - disable cmd filter, test cmd passthrough to downstream
      // - enable cmd filter, test cmd is blocked
      for (int cmd_filter = 0; cmd_filter < 2;  cmd_filter++) begin
        // Make sure filter is not blocking command opcode
        `uvm_info(`gfn, $sformatf("sending op 0x%0h with filter = %0d", opcode, cmd_filter),
                  UVM_MEDIUM)
        cfg_cmd_filter(cmd_filter, opcode);
        // Prepare data for transfer
        spi_host_xfer_flash_item(opcode, payload_size, read_start_addr);
        cfg.clk_rst_vif.wait_clks(10);
      end
    end

  endtask : body

endclass : spi_device_pass_cmd_filtering_vseq
