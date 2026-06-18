// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rram_ctrl_read_seed_vseq extends rram_ctrl_base_vseq;
  `uvm_object_utils(rram_ctrl_read_seed_vseq)

  rand data_q_t rram_data;
  rand rram_ctrl_op_t rram_ctrl_op;

  data_q_t rram_data_rd;
  data_q_t rram_data_bkdr_rd;
  data_q_t rram_data_exp[3];

  // rram ctrl operation data queue
  constraint rram_data_c {
    rram_data.size() == (rram_ctrl_op.num_words + 1);
  }

  rand lc_tx_t creator_seed_sw_rw;
  rand lc_tx_t owner_seed_sw_rw;
  rand lc_tx_t iso_part_seed_sw_rd;
  rand lc_tx_t iso_part_seed_sw_wr;

  constraint seeds_sw_rw_c {
    creator_seed_sw_rw  dist { On := 50, Off := 50 };
    owner_seed_sw_rw    dist { On := 50, Off := 50 };
    iso_part_seed_sw_rd dist { On := 50, Off := 50 };
    iso_part_seed_sw_wr dist { On := 50, Off := 50 };
  }

  // Standard SV/UVM methods
  extern function new(string name="");
  extern task body();
endclass : rram_ctrl_read_seed_vseq


function rram_ctrl_read_seed_vseq::new(string name="");
  super.new(name);
endfunction : new

task rram_ctrl_read_seed_vseq::body();

  uvm_reg_data_t data;

  logic [rram_ctrl_pkg::NumSeeds-1:0][rram_ctrl_pkg::SeedWidth-1:0] seeds, seeds_exp;

  uvm_reg_data_t reg_data;
  bit init_done;
  bit mp_err, exp_mp_err;

  // 1. fill info partition with random seeds
  rram_ctrl_op.op        = RramOpWrite;
  rram_ctrl_op.partition = RramPartInfo;
  rram_ctrl_op.num_words = BusWordsPerPage - 1;

  for (uint i = CreatorInfoPage; i <= IsolatedInfoPage; i++) begin
    int ind = i - CreatorInfoPage;
    // Randomize rram_data
    if (!randomize(rram_data)) begin
      `uvm_fatal(`gfn, "Randomization failed!")
    end
    rram_ctrl_op.addr = i * (BusWordsPerPage << 2);
    cfg.rram_bkdr_mem_write(rram_ctrl_op, rram_data, 1'b1, 1'b0);
    rram_data_exp[ind] = rram_data;
    for (int k = 0; k < SeedWidth/BusWidth; k++) begin
      seeds_exp[ind][k*BusWidth +: BusWidth] = rram_data[k];
    end
  end

  // 2. initialize reading of seeds
  cfg.misc_vif.lc_seed_hw_rd_en = On;
  csr_wr(.ptr(ral.init), .value('b1));

  // poll init_done
  do begin
    csr_rd(.ptr(ral.status), .value(reg_data));
    init_done = get_field_val(ral.status.init_done, reg_data);
    #1us;
  end while (init_done == 1'b0);

  // 3. check seeds at rram_ctrl output
  seeds = cfg.misc_vif.keymgr;

  for (uint i = CreatorInfoPage; i <= OwnerInfoPage; i++) begin
    int ind = i - CreatorInfoPage;
    if (seeds[ind] !== seeds_exp[ind]) begin
      `uvm_error("Seed error", $sformatf("seed[%0d] exp: %08x is: %08x", ind, seeds_exp[ind],
        seeds[ind]))
    end
  end

  // 4. perform controller read
  // initialize info page access settings

  // allow software read
  cfg.misc_vif.lc_creator_seed_sw_rw_en = On;
  cfg.misc_vif.lc_owner_seed_sw_rw_en   = On;
  cfg.misc_vif.lc_iso_part_sw_rd_en     = On;

  for (uint i = CreatorInfoPage; i <= IsolatedInfoPage; i++) begin
    int ind = i - CreatorInfoPage;
    rram_ctrl_base_vseq::update_info_page_cfg(i, MuBi4True, MuBi4True, MuBi4True, MuBi4True,
                                              MuBi4True);
    // read back data over ctrl interface
    rram_ctrl_op.op        = RramOpRead;
    rram_ctrl_op.partition = RramPartInfo;
    rram_ctrl_op.num_words = BusWordsPerPage - 1;
    rram_ctrl_op.addr      = i * (BusWordsPerPage << 2);
    rram_ctrl_base_vseq::rram_ctrl_read(rram_ctrl_op, rram_data_rd, 1'b0);

    // check if data matches with written values
    for (int k = 0; k <= rram_ctrl_op.num_words; k++) begin
      if (rram_data_exp[ind][k] !== rram_data_rd[k]) begin
        `uvm_error("Read-back error", $sformatf("data[%0d] exp: %08x is: %08x", k,
                   rram_data_exp[ind][k], rram_data_rd[k]))
      end
    end
  end

  // 5. overwrite seeds and read back. In case no access was given, an error is expected
  cfg.misc_vif.lc_creator_seed_sw_rw_en = creator_seed_sw_rw;
  cfg.misc_vif.lc_owner_seed_sw_rw_en   = owner_seed_sw_rw;
  cfg.misc_vif.lc_iso_part_sw_rd_en     = iso_part_seed_sw_rd;
  cfg.misc_vif.lc_iso_part_sw_wr_en     = iso_part_seed_sw_wr;

  // try to access each special info page with random permission settings
  rram_ctrl_op.partition = RramPartInfo;

  for (uint i = CreatorInfoPage; i <= IsolatedInfoPage; i++) begin
    int ind = i - CreatorInfoPage;

    rram_ctrl_op.num_words = $urandom_range(1, BusWordsPerPage/4)*4 - 1;
    rram_ctrl_op.op        = RramOpWrite;
    rram_ctrl_op.addr      = i * (BusWordsPerPage << 2);
    `uvm_info(`gfn, $sformatf("num_words=%d",
                              rram_ctrl_op.num_words), UVM_MEDIUM)

    // Randomize rram_data
    if (!randomize(rram_data)) begin
      `uvm_fatal(`gfn, "Randomization failed!")
    end
    // write to rram
    rram_ctrl_base_vseq::rram_ctrl_write(rram_ctrl_op, rram_data, 1'b0);

    // read error register
    csr_rd(.ptr(ral.err_code), .value(reg_data));
    mp_err = get_field_val(ral.err_code.mp_err, reg_data);
    // and clear fields
    csr_wr(.ptr(ral.err_code), .value(reg_data));

    // determine if transaction must have caused an error or not
    case (i)
      CreatorInfoPage:  exp_mp_err = creator_seed_sw_rw == Off;
      OwnerInfoPage:    exp_mp_err = owner_seed_sw_rw == Off;
      IsolatedInfoPage: exp_mp_err = iso_part_seed_sw_wr == Off;
      default:
        exp_mp_err = 1'b0;
    endcase

    if (mp_err !== exp_mp_err) begin
      `uvm_error("Info page access error", $sformatf("page[%0d]: exp_mp_err: %01x mp_err: %01x", i,
                 exp_mp_err, mp_err))
    end

    rram_ctrl_base_vseq::rram_ctrl_wait_wr_done();
    rram_data_bkdr_rd = cfg.rram_bkdr_mem_read(rram_ctrl_op, 1'b1, 1'b0);

    // check if data matches with written values
    for (int k = 0; k <= rram_ctrl_op.num_words; k++) begin
      if (mp_err == 0) begin
        if (rram_data[k] !== rram_data_bkdr_rd[k]) begin
          `uvm_error("Write-error", $sformatf("page[%0d]: data[%0d] exp: %08x is: %08x", i, k,
                     rram_data[k], rram_data_bkdr_rd[k]))
        end
      end
    end

    // try reading the info pages
    rram_ctrl_op.op = RramOpRead;
    rram_ctrl_base_vseq::rram_ctrl_read(rram_ctrl_op, rram_data_rd, 1'b0);
    // read error register
    csr_rd(.ptr(ral.err_code), .value(reg_data));
    mp_err = get_field_val(ral.err_code.mp_err, reg_data);
    // and clear fields
    csr_wr(.ptr(ral.err_code), .value(reg_data));

    // determine if transaction must have caused an error or not
    case (i)
      CreatorInfoPage:  exp_mp_err = creator_seed_sw_rw == Off;
      OwnerInfoPage:    exp_mp_err = owner_seed_sw_rw == Off;
      IsolatedInfoPage: exp_mp_err = iso_part_seed_sw_rd == Off;
      default:
        exp_mp_err = 1'b0;
    endcase

    // check if data matches with rram values
    for (int k = 0; k <= rram_ctrl_op.num_words; k++) begin
      if (mp_err == 0) begin
        if (rram_data_rd[k] !== rram_data_bkdr_rd[k]) begin
          `uvm_error("Read-error", $sformatf("page[%0d]: data[%0d] exp: %08x is: %08x", i, k,
                     rram_data_bkdr_rd[k], rram_data_rd[k]))
        end
      end
    end
  end

  // 6. check seeds again. They cannot have changed due to the write
  seeds = cfg.misc_vif.keymgr;

  for (uint i = CreatorInfoPage; i <= OwnerInfoPage; i++) begin
    int ind = i - CreatorInfoPage;
    if (seeds[ind] !== seeds_exp[ind]) begin
      `uvm_error("Seed error", $sformatf("seed[%0d] exp: %08x is: %08x", ind, seeds_exp[ind],
        seeds[ind]))
    end
  end

  #1us;

endtask : body
