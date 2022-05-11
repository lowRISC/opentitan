// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Passthrough mode filtering of commands scenario, filter on and off
class spi_device_pass_cmd_filtering_vseq extends spi_device_pass_base_vseq;
  `uvm_object_utils(spi_device_pass_cmd_filtering_vseq)
  `uvm_object_new

  virtual task body();
    bit [7:0]  op;
    bit [7:0] opcode_q[$];
    uint payload_size;
    spi_device_flash_pass_init(PassthroughMode);

    // cmd_infos index is the opcode, get all opcode
    opcode_q = cfg.m_spi_agent_cfg.cmd_infos.find_index() with ('1);
    for (int i = 0; i < num_trans; ++i) begin
      `uvm_info(`gfn, $sformatf("running iteration %0d", i), UVM_LOW)
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(op,
          op inside {opcode_q};)
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(payload_size,
          // TODO, use distribution later
          payload_size <= 256;)

      // test 2 cases:
      //  - disable cmd filter, test cmd passthrough to downstream
      // - enable cmd filter, test cmd is blocked
      for (int cmd_filter = 0; cmd_filter < 2;  cmd_filter++) begin
        // Make sure filter is not blocking command opcode
        cfg_cmd_filter(cmd_filter, op);
        // Prepare data for transfer
        spi_host_xfer_flash_item(op, cfg.m_spi_agent_cfg.cmd_infos[op].addr_bytes, payload_size);
      end
    end

  endtask : body

endclass : spi_device_pass_cmd_filtering_vseq
