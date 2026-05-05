// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rram_ctrl_concurrent_rd_wr_vseq extends rram_ctrl_base_vseq;
  `uvm_object_utils(rram_ctrl_concurrent_rd_wr_vseq)

  localparam int unsigned NumTrans = 20;

  rand data_q_t rram_data;
  rand rram_ctrl_op_t rram_ctrl_op;
  rand mubi4_t scramble_en;

  bit completed;

  constraint scramble_en_c {
    scramble_en dist {
      MuBi4False := 50,
      MuBi4True  := 50
    };
  }

  constraint addr_c {
    rram_ctrl_op.addr < TotalBytes - TotalOtpBytes;
    rram_ctrl_op.addr[3:0] == '0;
  }

  // solve number of words
  constraint rram_ctrl_op_c {
    rram_ctrl_op.num_words%4 == 3;
    rram_ctrl_op.num_words < ((TotalBytes - TotalOtpBytes - rram_ctrl_op.addr) >> 2);
    rram_ctrl_op.partition == RramPartData;
    rram_ctrl_op.op == RramOpWrite;
  }

  // rram ctrl operation data queue
  constraint rram_data_c {
    solve rram_ctrl_op before rram_data;
    rram_data.size() == (rram_ctrl_op.num_words + 1);
  }

  // Standard SV/UVM methods
  extern function new(string name="");
  extern task body();
endclass : rram_ctrl_concurrent_rd_wr_vseq


function rram_ctrl_concurrent_rd_wr_vseq::new(string name="");
  super.new(name);
endfunction : new

task rram_ctrl_concurrent_rd_wr_vseq::body();

  logic completed;

  begin
    // 1. initialize rram default region
    rram_ctrl_base_vseq::update_default_region_cfg(MuBi4True, MuBi4True, scramble_en, MuBi4True);

    // 2. initial write
    rram_ctrl_base_vseq::rram_ctrl_write(rram_ctrl_op, rram_data);

    for (int k = 0; k < NumTrans; k++) begin
      data_q_t rram_data_last = rram_data;
      rram_ctrl_op_t rram_ctrl_op_last = rram_ctrl_op;
      addr_t start_addr, last_start_addr;
      addr_t end_addr, last_end_addr;

      last_start_addr = rram_ctrl_op_last.addr;
      last_end_addr = rram_ctrl_op_last.addr + ((rram_ctrl_op_last.num_words+1)*4);

      // Rerandomize variables for next iteration
      do begin
        if (!randomize()) begin
            `uvm_fatal(`gfn, "Randomization failed!")
        end
        start_addr = rram_ctrl_op.addr;
        end_addr = rram_ctrl_op.addr + (rram_ctrl_op.num_words+1)*4;
      end while (!((last_end_addr < start_addr) || (end_addr <= last_start_addr)));

      `uvm_info(`gfn, $sformatf("Starting a transaction with: num_words=%d, addr=%08x,",
                rram_ctrl_op.num_words, rram_ctrl_op.addr), UVM_LOW)

      fork
        begin
          // 2. write random data (triggers data hazard in odd iterations)
          rram_ctrl_base_vseq::rram_ctrl_write(rram_ctrl_op, rram_data);
        end
        begin
          // 3. read back data of previous iteration over host interface
          for (int i = 0; i <= rram_ctrl_op_last.num_words; i++) begin
            data_t rdata;
            rram_ctrl_base_vseq::rram_host_read(.addr(rram_ctrl_op_last.addr + 4*i),
                                                .blocking(1'b0),
                                                .check_rdata(1'b1), .exp_rdata(rram_data_last[i]),
                                                .instr_type(MuBi4False), .rdata(rdata),
                                                .completed(completed), .exp_err_rsp(1'b0));
          end
          csr_utils_pkg::wait_no_outstanding_access();
        end
      join
      #10us;
    end
  end

endtask : body
