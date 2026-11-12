// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Reads back data over the host interface right after it was written through the controller
// interface, while the phy may still be writing it.
// Every second write goes to the same location as the previous one, so that the host reads hit
// data that is being overwritten.
class rram_ctrl_data_hazard_vseq extends rram_ctrl_base_vseq;
  `uvm_object_utils(rram_ctrl_data_hazard_vseq)

  // Number of write operations.
  rand int unsigned num_ops;
  constraint num_ops_c { num_ops inside {[10:20]}; }

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

  // Short writes of whole RRAM words to the data partition
  constraint rram_ctrl_op_c {
    rram_ctrl_op.num_words % WidthMultiple == WidthMultiple - 1;
    rram_ctrl_op.num_words <= 15;
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
endclass : rram_ctrl_data_hazard_vseq


function rram_ctrl_data_hazard_vseq::new(string name="");
  super.new(name);
endfunction : new

task rram_ctrl_data_hazard_vseq::body();
  update_default_region_cfg(MuBi4True, MuBi4True, scramble_en, MuBi4True);

  for (int k = 0; k < num_ops; k++) begin
    bit completed;

    `uvm_info(`gfn, $sformatf("Starting op %0d/%0d: num_words=%0d, addr=0x%0x", k + 1, num_ops,
                              rram_ctrl_op.num_words, rram_ctrl_op.addr), UVM_LOW)

    rram_ctrl_write(rram_ctrl_op, rram_data);

    // Read back the data over the host interface
    for (int i = 0; i <= rram_ctrl_op.num_words; i++) begin
      data_t rdata;
      rram_host_read(.addr(rram_ctrl_op.addr + BusBytes * i), .blocking(1'b0),
                     .check_rdata(1'b1), .exp_rdata(rram_data[i]), .rdata(rdata),
                     .completed(completed));
    end
    csr_utils_pkg::wait_no_outstanding_access();

    // Write to the same location in the next iteration after every even one
    if (k % 2 == 0) begin
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(rram_data)
    end else begin
      `DV_CHECK_FATAL(randomize(rram_ctrl_op, rram_data))
    end
  end
endtask : body
