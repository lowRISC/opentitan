// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rram_ctrl_smoke_vseq extends rram_ctrl_base_vseq;
  `uvm_object_utils(rram_ctrl_smoke_vseq)

  import prim_mubi_pkg::MuBi4True;
  import prim_mubi_pkg::MuBi4False;
  import prim_mubi_pkg::mubi4_t;

  localparam int unsigned NumTrans = 10;

  rand data_q_t rram_data;
  rand rram_ctrl_op_t rram_ctrl_op;
  rand mubi4_t scramble_en;

  data_q_t rram_data_rd;
  bit completed;

  constraint scramble_en_c {
    scramble_en dist {
      MuBi4False := 50,
      MuBi4True  := 50
    };
  }

  // choose a random partition
  constraint partition_c {
    rram_ctrl_op.partition dist {
      RramPartData := 95,
      RramPartInfo := 5
    };
  }

  // solve address depending on partition
  constraint addr_c {
    solve rram_ctrl_op.partition before rram_ctrl_op.addr;
    rram_ctrl_op.addr < ((rram_ctrl_op.partition == RramPartInfo) ?
                         // access to full InfoPartition
                         TotalInfoBytes :
                         // access to DataPartition without OtpPartition
                         TotalBytes - TotalOtpBytes);
    rram_ctrl_op.addr[3:0] == '0;
  }

  // solve number of words
  constraint rram_ctrl_op_c {
    solve rram_ctrl_op.addr, rram_ctrl_op.partition before rram_ctrl_op.num_words;
    rram_ctrl_op.num_words%4 == 3;
    rram_ctrl_op.num_words < ((rram_ctrl_op.partition == RramPartInfo) ?
                              // stay inside info partition
                              (TotalInfoBytes - rram_ctrl_op.addr) >> 2 :
                              // stay inside data partition
                              (TotalBytes - TotalOtpBytes - rram_ctrl_op.addr) >> 2);
  }

  // rram ctrl operation data queue
  constraint rram_data_c {
    solve rram_ctrl_op.num_words before rram_data;
    rram_data.size() == rram_ctrl_op.num_words + 1;
  }

  // Standard SV/UVM methods
  extern function new(string name="");
  extern task body();
endclass : rram_ctrl_smoke_vseq


function rram_ctrl_smoke_vseq::new(string name="");
  super.new(name);
endfunction : new

task rram_ctrl_smoke_vseq::body();

  // 1. test rw-access to scratch register
  uvm_reg_data_t data;
  `uvm_info(`gfn, "Test to write to a register", UVM_LOW)

  csr_rd(ral.scratch, data);
  `uvm_info(`gfn, $sformatf("Read data: 0x%0h", data), UVM_LOW)
  csr_wr(ral.scratch, 32'hDEADBEEF);
  csr_rd(ral.scratch, data);
  `uvm_info(`gfn, $sformatf("Read data: 0x%0h", data), UVM_LOW)

  // 2. initialize rram default region
  data = 0;
  data = get_csr_val_with_updated_field(ral.default_region.wr_en, data, MuBi4True);
  data = get_csr_val_with_updated_field(ral.default_region.rd_en, data, MuBi4True);
  data = get_csr_val_with_updated_field(ral.default_region.scramble_en, data, scramble_en);
  data = get_csr_val_with_updated_field(ral.default_region.ecc_en, data, MuBi4False);
  csr_wr(.ptr(ral.default_region), .value(data));

  // 3. initialize rram info page regions
  data = 0;
  data = get_csr_val_with_updated_field(ral.info_page_cfg[0].en, data, MuBi4True);
  data = get_csr_val_with_updated_field(ral.info_page_cfg[0].wr_en, data, MuBi4True);
  data = get_csr_val_with_updated_field(ral.info_page_cfg[0].rd_en, data, MuBi4True);
  data = get_csr_val_with_updated_field(ral.info_page_cfg[0].scramble_en, data, scramble_en);
  data = get_csr_val_with_updated_field(ral.info_page_cfg[0].ecc_en, data, MuBi4True);
  for (uint i = 0; i < 8; i++) begin
    csr_wr(.ptr(ral.info_page_cfg[i]), .value(data));
  end

  // 4. randomized write + readback to rram
  for (int k = 0; k < NumTrans; k++) begin
    `uvm_info(`gfn, $sformatf("Starting a transaction with: num_words=%d, addr=%08x, partition=%d",
              rram_ctrl_op.num_words, rram_ctrl_op.addr, rram_ctrl_op.partition), UVM_LOW)
    // write random data
    rram_ctrl_op.op = rram_ctrl_pkg::RramOpWrite;
    rram_ctrl_base_vseq::rram_ctrl_write(rram_ctrl_op, rram_data);

    // read back data over ctrl interface
    rram_ctrl_op.op = rram_ctrl_pkg::RramOpRead;
    rram_ctrl_base_vseq::rram_ctrl_read(rram_ctrl_op, rram_data_rd);

    // read back data over host interface
    if (rram_ctrl_op.partition == RramPartData) begin
      logic completed;
      for (int i = 0; i <= rram_ctrl_op.num_words; i++) begin
        data_t rdata;
        rram_ctrl_base_vseq::rram_host_read(.addr(rram_ctrl_op.addr + 4*i), .blocking(1'b1),
                                            .check_rdata(1'b1), .exp_rdata(rram_data[i]),
                                            .instr_type(MuBi4False), .rdata(rdata),
                                            .completed(completed), .exp_err_rsp(1'b0));
      end
      wait(completed == 1'b1);

    end
    // check if data matches with written values
    for (int i = 0; i < rram_data_rd.size(); i++) begin
      if (rram_data[i] !== rram_data_rd[i]) begin
          `uvm_error("Read-back error:", $sformatf("data[%0d] exp: %08x is: %08x", i, rram_data[i],
                     rram_data_rd[i]))
      end
    end

    rram_data.delete();
    rram_data_rd.delete();
    // Rerandomize variables for next iteration
    if (!randomize()) begin
        `uvm_fatal(`gfn, "Randomization failed!")
    end
  end


endtask : body
