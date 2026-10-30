// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Sends an RMA request while the controller interface writes new data and the host interface
// reads back previously written data, and waits for the RMA to be acknowledged.
class rram_ctrl_rma_vseq extends rram_ctrl_base_vseq;
  `uvm_object_utils(rram_ctrl_rma_vseq)

  rand data_q_t       rram_data;
  rand rram_ctrl_op_t rram_ctrl_op;
  rand mubi4_t        scramble_en;

  constraint scramble_en_c {
    scramble_en dist {
      MuBi4False := 50,
      MuBi4True  := 50
    };
  }

  // RRAM word aligned start address outside the OTP region
  constraint addr_c {
    rram_ctrl_op.addr < TotalBytes - TotalOtpBytes;
    rram_ctrl_op.addr[DataByteWidth-1:0] == '0;
  }

  // Writes of whole RRAM words to the data partition
  constraint rram_ctrl_op_c {
    rram_ctrl_op.num_words % WidthMultiple == WidthMultiple - 1;
    rram_ctrl_op.num_words < (TotalBytes - TotalOtpBytes - rram_ctrl_op.addr) / BusBytes;
    rram_ctrl_op.partition == RramPartData;
    rram_ctrl_op.op == RramOpWrite;
  }

  constraint rram_data_c {
    solve rram_ctrl_op before rram_data;
    rram_data.size() == rram_ctrl_op.num_words + 1;
  }

  // Standard SV/UVM methods
  extern function new(string name="");
  extern task body();
endclass : rram_ctrl_rma_vseq


function rram_ctrl_rma_vseq::new(string name="");
  super.new(name);
endfunction : new

task rram_ctrl_rma_vseq::body();
  data_q_t       prev_data;
  rram_ctrl_op_t prev_op;

  update_default_region_cfg(MuBi4True, MuBi4True, scramble_en, MuBi4True);

  // Initial write
  rram_ctrl_write(rram_ctrl_op, rram_data);
  prev_data = rram_data;
  prev_op   = rram_ctrl_op;
  `DV_CHECK_FATAL(randomize(rram_ctrl_op, rram_data))

  // Once the RMA starts, all accesses are denied and the RRAM is wiped. So neither the write nor
  // the host reads are checked.
  fork
    rram_ctrl_write(rram_ctrl_op, rram_data, .wr_check(1'b0));
    begin
      bit completed;
      for (int i = 0; i <= prev_op.num_words; i++) begin
        data_t rdata;
        rram_host_read(.addr(prev_op.addr + BusBytes * i), .blocking(1'b0), .rdata(rdata),
                       .completed(completed));
      end
      csr_utils_pkg::wait_no_outstanding_access();
    end
    begin
      #($urandom_range(1, 100) * 1us);
      rma_req();
    end
  join
endtask : body
