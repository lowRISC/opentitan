// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence to do illegal read and write accesses to the imem when the otbn is busy

class otbn_illegal_mem_acc_vseq extends otbn_single_vseq;
  `uvm_object_utils(otbn_illegal_mem_acc_vseq)
  `uvm_object_new

  task body();
    fork
      begin
        super.body();
      end
      begin
        do_mem_acc();
      end
    join
  endtask: body

  task do_mem_acc();
    bit write;
    uvm_mem mem;
    bit [BUS_AW-1:0] offset;
    bit [BUS_DW-1:0] data;
    // Pick either dmem or imem to access randomly
    bit is_imem;
    bit [31:0] err_val = 32'd1 << 21;


    `DV_CHECK_STD_RANDOMIZE_FATAL(is_imem)
    `DV_CHECK_STD_RANDOMIZE_FATAL(data)
    `DV_CHECK_STD_RANDOMIZE_FATAL(write)

    // Pick on which memory we will be working on
    mem = is_imem ? ral.imem : ral.dmem;
    wait (cfg.model_agent_cfg.vif.status == otbn_pkg::StatusBusyExecute);
    offset = $urandom_range(0, mem.get_n_bytes() - 1);
    cfg.en_scb_tl_err_chk = 0;
    fork
      begin
        string tl_dmem_req_path = "tb.dut.dmem_req_bus";
        string tl_imem_req_path = "tb.dut.imem_req_bus";
        bit tl_dmem_req, tl_imem_req;
        while (1) begin
          // Check the paths at negedge, any memory accesses from TL bus while executing
          // regardless of it being driven by this sequence should cause a "ILLEGAL_BUS_ACCESS"
          // fatal error.
          `DV_CHECK_FATAL(uvm_hdl_read(tl_dmem_req_path, tl_dmem_req))
          `DV_CHECK_FATAL(uvm_hdl_read(tl_imem_req_path, tl_imem_req))
          if (tl_dmem_req | tl_imem_req) begin
            // This will actually take half-cycle since we are already at a negedge
            cfg.clk_rst_vif.wait_clks(1);
            // Let model know we have the fatal error.
            cfg.model_agent_cfg.vif.send_err_escalation(err_val);
            break;
          end
          cfg.clk_rst_vif.wait_n_clks(1);
        end
      end
      begin
        if (write) begin
          csr_utils_pkg::mem_wr(mem, offset, data);
          `uvm_info(`gfn,
                    $sformatf("\n\t ----| Writing %d to a memory", data),
                    UVM_LOW)
        end else begin
          csr_utils_pkg::mem_rd(mem, offset, data);
          `uvm_info(`gfn,
                    $sformatf("\n\t ----| Reading %d from a memory", data),
                    UVM_LOW)
          `DV_CHECK_FATAL(data == '0)
        end
      end
    join
    reset_if_locked();
    cfg.en_scb_tl_err_chk = 1;
  endtask

endclass : otbn_illegal_mem_acc_vseq
