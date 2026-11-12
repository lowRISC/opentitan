// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Smoke test of all RRAM interfaces.
//
// Configures the default region, all memory protection regions and all info pages randomly, then
// repeatedly writes random data through the controller interface and, concurrently, reads it back
// through the controller and host interfaces, rewrites words and accesses the OTP region through
// the OTP macro interface.
class rram_ctrl_smoke_vseq extends rram_ctrl_base_vseq;
  `uvm_object_utils(rram_ctrl_smoke_vseq)

  // Number of write operations.
  rand int unsigned num_ops;
  constraint num_ops_c { num_ops inside {[10:20]}; }

  // Number of OTP commands issued during each write operation's read-back.
  localparam int unsigned NumOtpCmds = 10;

  rand data_q_t       rram_data;
  rand rram_ctrl_op_t rram_ctrl_op;

  // Region and page properties
  rand mubi4_t scramble_en;
  rand mubi4_t region_en;
  rand mubi4_t rd_en;
  rand mubi4_t wr_en;
  rand mubi4_t ecc_en;

  constraint mubi_c {
    scramble_en dist { MuBi4False := 100 - cfg.scr_en_pct, MuBi4True := cfg.scr_en_pct };
    region_en   dist { MuBi4False := 100 - cfg.reg_en_pct, MuBi4True := cfg.reg_en_pct };
    wr_en       dist { MuBi4False := 100 - cfg.wr_en_pct,  MuBi4True := cfg.wr_en_pct  };
    rd_en       dist { MuBi4False := 100 - cfg.rd_en_pct,  MuBi4True := cfg.rd_en_pct  };
    ecc_en      dist { MuBi4False := 100 - cfg.ecc_en_pct, MuBi4True := cfg.ecc_en_pct };
  }

  // Readable pages are also writable, so that reads return data written by this sequence.
  constraint rd_en_c {
    solve wr_en before rd_en;
    if (rd_en == MuBi4True) wr_en == MuBi4True;
  }

  // Mostly access the data partition
  constraint partition_c {
    rram_ctrl_op.partition dist {
      RramPartData := 95,
      RramPartInfo := 5
    };
  }

  // RRAM word aligned start address within the partition
  constraint addr_c {
    rram_ctrl_op.addr < ((rram_ctrl_op.partition == RramPartInfo) ? TotalInfoBytes : TotalBytes);
    rram_ctrl_op.addr[DataByteWidth-1:0] == '0;
  }

  // Whole RRAM words that stay within the partition
  constraint rram_ctrl_op_c {
    rram_ctrl_op.op == RramOpWrite;
    rram_ctrl_op.num_words % WidthMultiple == WidthMultiple - 1;
    rram_ctrl_op.num_words < ((rram_ctrl_op.partition == RramPartInfo) ?
                              (TotalInfoBytes - rram_ctrl_op.addr) / BusBytes :
                              (TotalBytes - rram_ctrl_op.addr) / BusBytes);
  }

  constraint rram_data_c {
    solve rram_ctrl_op before rram_data;
    rram_data.size() == rram_ctrl_op.num_words + 1;
  }

  // Memory protection region placement
  rand bit [PageW-1:0] start_page;
  rand bit [PageW-1:0] page_size;

  constraint page_size_c {
    solve start_page before page_size;
    int'(start_page) + int'(page_size) < TotalDataPages;
  }

  // OTP commands
  rand otp_ctrl_macro_pkg::otp_macro_data_t otp_wdata;
  rand otp_ctrl_macro_pkg::otp_macro_addr_t otp_addr;
  rand otp_ctrl_macro_pkg::otp_macro_size_t otp_size;
  rand otp_ctrl_macro_pkg::cmd_e            otp_cmd;

  // Legal sizes are 0, 1 and 3 for 16b, 32b and 64b transactions
  constraint otp_size_c {
    otp_size inside {2'b00, 2'b01, 2'b11};
  }

  constraint otp_cmd_c {
    otp_cmd != otp_ctrl_macro_pkg::Init;
  }

  // Only the transferred words carry data
  constraint otp_data_c {
    solve otp_size before otp_wdata;
    if (otp_size == 0) {
      otp_wdata[otp_ctrl_macro_pkg::OtpIfWidth-1:16] == '0;
    } else if (otp_size == 1) {
      otp_wdata[otp_ctrl_macro_pkg::OtpIfWidth-1:32] == '0;
    }
  }

  // Transfers are aligned to their size and stay within the OTP
  constraint otp_addr_c {
    solve otp_size before otp_addr;
    int'(otp_addr) + int'(otp_size) < otp_ctrl_macro_pkg::OtpDepth;
    if (otp_size == 1) {
      otp_addr[0] == 1'b0;
    } else if (otp_size == 3) {
      otp_addr[1:0] == 2'b0;
    }
  }

  // Standard SV/UVM methods
  extern function new(string name="");
  extern task body();

  // Class specific methods

  // Randomly configures the default region, all memory protection regions and all info pages.
  extern task configure_regions();

  // Issues a random OTP command and checks its result.
  extern task otp_random_cmd();
endclass : rram_ctrl_smoke_vseq


function rram_ctrl_smoke_vseq::new(string name="");
  super.new(name);
endfunction : new

task rram_ctrl_smoke_vseq::configure_regions();
  update_default_region_cfg(wr_en, rd_en, scramble_en, ecc_en);

  for (uint i = 0; i < MpRegions; i++) begin
    `DV_CHECK_FATAL(randomize(scramble_en, region_en, wr_en, rd_en, ecc_en, start_page,
                              page_size))
    update_mp_region(i, start_page, page_size, region_en, wr_en, rd_en, scramble_en, ecc_en);
  end

  for (uint i = 0; i < TotalInfoPages; i++) begin
    `DV_CHECK_FATAL(randomize(scramble_en, region_en, wr_en, rd_en, ecc_en))
    update_info_page_cfg(i, MuBi4True, wr_en, rd_en, scramble_en, ecc_en);
  end
endtask : configure_regions

task rram_ctrl_smoke_vseq::otp_random_cmd();
  otp_ctrl_macro_pkg::otp_macro_data_t otp_rdata;
  `DV_CHECK_FATAL(randomize(otp_wdata, otp_addr, otp_size, otp_cmd))
  case (otp_cmd)
    otp_ctrl_macro_pkg::Write:    otp_write(otp_addr, otp_size, 1'b0, 1'b1, otp_wdata);
    otp_ctrl_macro_pkg::Read:     otp_read(otp_addr, otp_size, 1'b0, 1'b1, otp_rdata);
    otp_ctrl_macro_pkg::WriteRaw: otp_write(otp_addr, otp_size, 1'b1, 1'b1, otp_wdata);
    otp_ctrl_macro_pkg::ReadRaw:  otp_read(otp_addr, otp_size, 1'b1, 1'b1, otp_rdata);
    otp_ctrl_macro_pkg::Zeroize:  otp_zeroize(otp_addr, otp_size, 1'b1, otp_rdata);
    default: `uvm_fatal(`gfn, $sformatf("Unexpected OTP command %s", otp_cmd.name()))
  endcase
endtask : otp_random_cmd

task rram_ctrl_smoke_vseq::body();
  uvm_reg_data_t data;

  // Read and write the scratch register
  csr_rd_check(.ptr(ral.scratch), .compare_vs_ral(1'b1));
  csr_wr(.ptr(ral.scratch), .value($urandom()));
  csr_rd_check(.ptr(ral.scratch), .compare_vs_ral(1'b1));

  configure_regions();

  for (int k = 0; k < num_ops; k++) begin
    data_q_t rram_data_rd;

    `uvm_info(`gfn, $sformatf("Starting op %0d/%0d: num_words=%0d, addr=0x%0x, partition=%s",
                              k + 1, num_ops, rram_ctrl_op.num_words, rram_ctrl_op.addr,
                              rram_ctrl_op.partition.name()), UVM_LOW)

    rram_ctrl_write(rram_ctrl_op, rram_data);

    fork
      // Read back the data over the controller interface
      begin
        rram_ctrl_op_t rd_op = rram_ctrl_op;
        rd_op.op = RramOpRead;
        rram_ctrl_read(rd_op, rram_data_rd);
      end

      // Rewrite a word, either in the OTP region or one of the words just written
      begin
        addr_t      rewrite_addr;
        rram_part_e rewrite_partition;
        cfg.clk_rst_vif.wait_clks($urandom_range(1, 1000));
        if (k < num_ops / 10) begin
          rewrite_addr      = TotalBytes - TotalOtpBytes + $urandom_range(0, TotalOtpBytes - 1);
          rewrite_partition = RramPartData;
        end else begin
          rewrite_addr      = rram_ctrl_op.addr + $urandom_range(0, rram_ctrl_op.num_words) *
                              BusBytes;
          rewrite_partition = rram_ctrl_op.partition;
        end
        rewrite_addr[DataByteWidth-1:0] = '0;
        rram_ctrl_rewrite(rewrite_addr, rewrite_partition);
      end

      // Read back the data over the host interface in random order
      begin
        if (rram_ctrl_op.partition == RramPartData) begin
          bit      completed;
          data_q_t exp_data;
          int      indices[] = new[rram_ctrl_op.num_words + 1];
          foreach (indices[i]) indices[i] = i;
          indices.shuffle();
          cfg.misc_vif.wait_nvm_idle();
          exp_data = get_exp_host_data(rram_ctrl_op);
          foreach (indices[i]) begin
            data_t rdata;
            rram_host_read(.addr(rram_ctrl_op.addr + BusBytes * indices[i]), .blocking(1'b0),
                           .check_rdata(1'b1), .exp_rdata(exp_data[indices[i]]),
                           .rdata(rdata), .completed(completed));
          end
          csr_utils_pkg::wait_no_outstanding_access();
        end
      end

      // Access the OTP region
      begin
        repeat (NumOtpCmds) begin
          otp_random_cmd();
          cfg.clk_rst_vif.wait_clks($urandom_range(1, 1000));
        end
      end
    join

    `DV_CHECK_FATAL(randomize(rram_ctrl_op, rram_data))
  end
endtask : body
