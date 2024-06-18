// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TODO: fix description
// Enable all passthrough/flash related features during init, and then randomly send valid commands
class spi_device_flash_mode_ignore_cmds_vseq extends spi_device_flash_all_vseq;
  `uvm_object_utils(spi_device_flash_mode_ignore_cmds_vseq)
  `uvm_object_new

  bit         busy;
  bit [7:0]   valid_ignored_while_busy_opcode_q[$];

  virtual task body();
    super.body();
  endtask : body

  virtual task knobs_before_randomize_op_addr_size();
    super.knobs_before_randomize_op_addr_size();
    get_flash_status_busy(busy);
    wait_on_busy = 0;
  endtask

  function void randomize_op_addr_size();
    super.randomize_op_addr_size();

    if(busy) begin
      // 1 - populate a queue of commands which may get ignored
      valid_ignored_while_busy_opcode_q.push_back(WREN);
      valid_ignored_while_busy_opcode_q.push_back(WRDI);
      valid_ignored_while_busy_opcode_q.push_back(EN4B);
      valid_ignored_while_busy_opcode_q.push_back(EX4B);
      // The above plus upload commands that are valid
      foreach (cfg.spi_host_agent_cfg.cmd_infos[idx])  begin
        if(ral.cmd_info[idx].upload && ral.cmd_info[idx].valid && ral.cmd_info[idx].busy) begin
          valid_ignored_while_busy_opcode_q.push_back(cfg.spi_host_agent_cfg.cmd_infos[idx].opcode);
        end
        if(!std::randomize(opcode) with {opcode inside {valid_ignored_while_busy_opcode_q}; })
          `uvm_fatal(`gfn, "Randomization Failure")
      end
    end // if (busy)

  endfunction // randomize_op_addr_size

endclass : spi_device_flash_mode_ignore_cmds_vseq
