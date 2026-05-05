// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rram_ctrl_smoke_vseq extends rram_ctrl_base_vseq;
  `uvm_object_utils(rram_ctrl_smoke_vseq)

  localparam int unsigned NumTrans = 20;

  rand data_q_t rram_data;
  rand rram_ctrl_op_t rram_ctrl_op;
  rand mubi4_t scramble_en;
  rand mubi4_t region_en;
  rand mubi4_t rd_en;
  rand mubi4_t wr_en;
  rand mubi4_t ecc_en;

  data_q_t rram_data_rd;

  constraint mubi_c {
    scramble_en dist { MuBi4False := 100-cfg.scr_en_pct, MuBi4True := cfg.scr_en_pct};
    region_en dist   { MuBi4False := 100-cfg.reg_en_pct, MuBi4True := cfg.reg_en_pct};
    wr_en dist       { MuBi4False := 100-cfg.wr_en_pct,  MuBi4True := cfg.wr_en_pct};
    rd_en dist       { MuBi4False := 100-cfg.rd_en_pct,  MuBi4True := cfg.rd_en_pct};
    ecc_en dist      { MuBi4False := 100-cfg.ecc_en_pct, MuBi4True := cfg.ecc_en_pct};
  }

  constraint rd_en_c {
    solve wr_en before rd_en;
    if (rd_en == MuBi4True) wr_en == MuBi4True;
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
    rram_ctrl_op.addr < ((rram_ctrl_op.partition == RramPartInfo) ?
                         // access to full InfoPartition
                         TotalInfoBytes :
                         // access to DataPartition
                         TotalBytes);
    rram_ctrl_op.addr[3:0] == '0;
  }

  // solve number of words
  constraint rram_ctrl_op_c {
    rram_ctrl_op.num_words%4 == 3;
    rram_ctrl_op.num_words < ((rram_ctrl_op.partition == RramPartInfo) ?
                              // stay inside info partition
                              (TotalInfoBytes - rram_ctrl_op.addr) >> 2 :
                              // stay inside data partition
                              (TotalBytes - rram_ctrl_op.addr) >> 2);
  }

  // rram ctrl operation data queue
  constraint rram_data_c {
    solve rram_ctrl_op before rram_data;
    rram_data.size() == rram_ctrl_op.num_words + 1;
  }

  // constraints for MP
  rand logic [PageW-1:0] start_page;
  rand logic [PageW-1:0] page_size;

  constraint page_size_c {
    solve start_page before page_size;
    int'(start_page) + int'(page_size) < TotalPages;
  }

  // Standard SV/UVM methods
  extern function new(string name="");
  extern task body();
endclass : rram_ctrl_smoke_vseq


function rram_ctrl_smoke_vseq::new(string name="");
  super.new(name);
endfunction : new

task rram_ctrl_smoke_vseq::body();

  page_cfg_t current_cfg;
  logic      exp_err;
  data_q_t   rram_bkdr_data;

  // 1. test rw-access to scratch register
  uvm_reg_data_t data;
  `uvm_info(`gfn, "Test to write to a register", UVM_LOW)

  csr_rd(ral.scratch, data);
  `uvm_info(`gfn, $sformatf("Read data: 0x%0h", data), UVM_LOW)
  csr_wr(ral.scratch, 32'hDEADBEEF);
  csr_rd(ral.scratch, data);
  `uvm_info(`gfn, $sformatf("Read data: 0x%0h", data), UVM_LOW)

  // 2. initialize rram default region
  rram_ctrl_base_vseq::update_default_region_cfg(wr_en, rd_en, scramble_en, ecc_en);

  for (uint i = 0; i < MpRegions; i++) begin
    if (!randomize(scramble_en, region_en, wr_en, rd_en, ecc_en, start_page, page_size)) begin
      `uvm_fatal(`gfn, "Randomization failed!")
    end
    rram_ctrl_base_vseq::update_mp_region(i, start_page, page_size, region_en, wr_en,
                                          rd_en, scramble_en, ecc_en);
  end

  // 3. initialize rram info page regions
  for (uint i = 0; i < TotalInfoPages; i++) begin
    if (!randomize(scramble_en, region_en, wr_en, rd_en, ecc_en)) begin
      `uvm_fatal(`gfn, "Randomization failed!")
    end
    rram_ctrl_base_vseq::update_info_page_cfg(i, MuBi4True, wr_en, rd_en, scramble_en,
                                              ecc_en);
  end

  // 4. randomized write + readback to rram
  for (int k = 0; k < NumTrans; k++) begin
    `uvm_info(`gfn, $sformatf("Starting a transaction with: num_words=%0d, addr=%08x, partition=%d",
                              rram_ctrl_op.num_words, rram_ctrl_op.addr, rram_ctrl_op.partition),
              UVM_LOW)

    exp_err = '0;
    // write random data
    rram_ctrl_op.op = rram_ctrl_pkg::RramOpWrite;
    rram_ctrl_base_vseq::rram_ctrl_write(rram_ctrl_op, rram_data);

    fork
      // read back data over ctrl interface
      begin
        rram_ctrl_op.op = rram_ctrl_pkg::RramOpRead;
        rram_ctrl_base_vseq::rram_ctrl_read(rram_ctrl_op, rram_data_rd);
      end

      // issue rewrite commands
      begin
        automatic addr_t rewrite_addr;
        automatic rram_part_e rewrite_partition;
        repeat ($urandom_range(1, 1000)) @(posedge cfg.clk_rst_vif.clk);
        rewrite_addr = rram_ctrl_op.addr + $urandom_range(0, int'(rram_ctrl_op.num_words));
        rewrite_addr[3:0] = '0;
        rewrite_partition = rram_ctrl_op.partition;
        rram_ctrl_base_vseq::rram_ctrl_rewrite(rewrite_addr, rewrite_partition);
      end

      // read back data over host interface in random order
      begin
        if (rram_ctrl_op.partition == RramPartData) begin
          logic completed;
          logic host_exp_err;
          int indices[] = new[rram_ctrl_op.num_words + 1];
          foreach (indices[k]) indices[k] = k;
          indices.shuffle();
          wait(cfg.misc_vif.pwr_nvm.nvm_idle === 1'b1);
          rram_bkdr_data = cfg.rram_bkdr_mem_read(rram_ctrl_op, 1'b0, 1'b1);
          for (int i = 0; i <= rram_ctrl_op.num_words; i++) begin
            data_t rdata, rdata_exp;
            current_cfg = rram_ctrl_base_vseq::get_current_page_cfg(rram_ctrl_op.addr, indices[i],
                                                                    RramPartData);
            if ((current_cfg.rd_en != prim_mubi_pkg::MuBi4True)) begin
              rdata_exp = '1;
              host_exp_err = 1'b1;
            end else begin
              rdata_exp = rram_bkdr_data[indices[i]];
              host_exp_err = 1'b0;
            end
            rram_ctrl_base_vseq::rram_host_read(.addr(rram_ctrl_op.addr + 4*indices[i]),
                                                .blocking(1'b0), .check_rdata(1'b1),
                                                .exp_rdata(rdata_exp), .instr_type(MuBi4False),
                                                .rdata(rdata), .completed(completed),
                                                .exp_err_rsp(host_exp_err));
          end
          csr_utils_pkg::wait_no_outstanding_access();
        end
      end
    join

    // check if data matches with written values
    for (int i = 0; i <= rram_ctrl_op.num_words; i++) begin
      current_cfg = rram_ctrl_base_vseq::get_current_page_cfg(rram_ctrl_op.addr, i,
                                                              rram_ctrl_op.partition);
      if ((current_cfg.rd_en != prim_mubi_pkg::MuBi4True) | exp_err) begin
        rram_data[i] = '1;
        exp_err = 1'b1;
      end
      if (rram_data[i] !== rram_data_rd[i]) begin
          `uvm_error("Read-back error:", $sformatf("data[%0d] exp: %08x is: %08x", i, rram_data[i],
                     rram_data_rd[i]))
      end
    end

    // Rerandomize variables for next iteration
    if (!randomize()) begin
        `uvm_fatal(`gfn, "Randomization failed!")
    end
  end

endtask : body
