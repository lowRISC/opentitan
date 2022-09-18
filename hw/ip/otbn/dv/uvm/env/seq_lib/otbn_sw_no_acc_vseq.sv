// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that writes to 1st Kib of address in DMEM which is inaccessible on TLUL.

class otbn_sw_no_acc_vseq extends otbn_single_vseq;
  `uvm_object_utils(otbn_sw_no_acc_vseq)

  `uvm_object_new

  task body();
    bit write;
    bit [BUS_AW-1:0] addr;
    bit [BUS_DW-1:0] data;
    bit [BUS_DW-1:0] rdata;
    logic [127:0]    key;
    logic [63:0]     nonce;
    bit [31:0] err_val = 32'd1 << 21;
    bit [11:0] offset;

    key = cfg.get_dmem_key();
    nonce = cfg.get_dmem_nonce();
    cfg.en_scb_tl_err_chk = 0;

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(data, $countones(data) != BUS_DW;)
    `DV_CHECK_STD_RANDOMIZE_FATAL(write)
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(offset,
                                       offset dist {12'hC00           :/ 5,
                                                    [12'hC00:12'hFFC] :/ 1,
                                                    12'hFFC           :/ 5};)
    addr = cfg.ral.get_addr_from_offset('h8000 + offset);
    `uvm_info(`gfn, $sformatf("addr = %h", addr), UVM_LOW)

    super.body();
    `DV_WAIT(cfg.model_agent_cfg.vif.status == otbn_pkg::StatusIdle)
      if (write) begin
        tl_access(.addr(addr), .write(1), .data(data), .exp_err_rsp(1));
        `uvm_info(`gfn,
                  $sformatf("\n\t ----| Writing %h to a memory", data),
                  UVM_LOW)
         rdata = cfg.read_dmem_word(offset / (4 * BaseWordsPerWLEN), key, nonce);
        `DV_CHECK_FATAL(rdata != data)
      end else begin
        tl_access(.addr(addr), .write(0), .data(data), .exp_err_rsp(1));
        `uvm_info(`gfn,
                  $sformatf("\n\t ----| Reading %h from a memory", data),
                  UVM_LOW)
        `DV_CHECK_FATAL(data == '1)
      end
    cfg.en_scb_tl_err_chk = 1;
  endtask

endclass
