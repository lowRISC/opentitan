// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Checks that the controller's initialization reads the creator and owner seeds from their info
// pages and provides them to the key manager, and that the life cycle controller gates software
// access to the creator, owner and isolated info pages.
//
// Requires +skip_lc_init=1, since the seeds must be in place before the initialization starts.
class rram_ctrl_read_seed_vseq extends rram_ctrl_base_vseq;
  `uvm_object_utils(rram_ctrl_read_seed_vseq)

  // Number of bus words per seed.
  localparam int unsigned SeedWords = SeedWidth / BusWidth;

  rand data_q_t rram_data;

  constraint rram_data_c {
    rram_data.size() == BusWordsPerPage;
  }

  // Life cycle enables for software access to the special info pages
  rand lc_tx_t creator_seed_sw_rw_en;
  rand lc_tx_t owner_seed_sw_rw_en;
  rand lc_tx_t iso_part_sw_rd_en;
  rand lc_tx_t iso_part_sw_wr_en;

  constraint lc_sw_en_c {
    creator_seed_sw_rw_en dist { On := 50, Off := 50 };
    owner_seed_sw_rw_en   dist { On := 50, Off := 50 };
    iso_part_sw_rd_en     dist { On := 50, Off := 50 };
    iso_part_sw_wr_en     dist { On := 50, Off := 50 };
  }

  // Standard SV/UVM methods
  extern function new(string name="");
  extern task body();

  // Class specific methods

  // Checks that the seeds at the key manager interface match `exp_seeds` and are valid.
  extern function void check_seeds(bit [NumSeeds-1:0][SeedWidth-1:0] exp_seeds);

  // Waits until a change of the life cycle enables has propagated through the DUT's
  // synchronizers.
  extern task wait_lc_sync();

  // Reads and clears ERR_CODE, and checks that ERR_CODE.MP_ERR matches `exp_mp_err`.
  extern task check_mp_err(bit exp_mp_err, string msg);
endclass : rram_ctrl_read_seed_vseq


function rram_ctrl_read_seed_vseq::new(string name="");
  super.new(name);
endfunction : new

function void rram_ctrl_read_seed_vseq::check_seeds(bit [NumSeeds-1:0][SeedWidth-1:0] exp_seeds);
  `DV_CHECK_EQ(cfg.misc_vif.keymgr_creator_seed.seed_valid, 1'b1, "Creator seed valid")
  `DV_CHECK_EQ(cfg.misc_vif.keymgr_creator_seed.seed, exp_seeds[CreatorSeedIdx], "Creator seed")
  `DV_CHECK_EQ(cfg.misc_vif.keymgr_owner_seed.seed_valid, 1'b1, "Owner seed valid")
  `DV_CHECK_EQ(cfg.misc_vif.keymgr_owner_seed.seed, exp_seeds[OwnerSeedIdx], "Owner seed")
endfunction : check_seeds

task rram_ctrl_read_seed_vseq::wait_lc_sync();
  cfg.clk_rst_vif.wait_clks(4);
endtask : wait_lc_sync

task rram_ctrl_read_seed_vseq::check_mp_err(bit exp_mp_err, string msg);
  uvm_reg_data_t err_code;
  csr_rd(.ptr(ral.err_code), .value(err_code));
  csr_wr(.ptr(ral.err_code), .value(err_code));
  `DV_CHECK_EQ(get_field_val(ral.err_code.mp_err, err_code), exp_mp_err, msg)
endtask : check_mp_err

task rram_ctrl_read_seed_vseq::body();
  bit [NumSeeds-1:0][SeedWidth-1:0] exp_seeds;
  data_q_t                          exp_page_data[TotalInfoPages];
  rram_ctrl_op_t                    ctrl_op;
  data_q_t                          rdata;

  `DV_CHECK_EQ(cfg.skip_lc_init, 1'b1, "This sequence must run with +skip_lc_init=1")

  // 1. Fill the special info pages with random data, scrambled the way the life cycle manager
  //    reads them.
  ctrl_op.partition = RramPartInfo;
  ctrl_op.num_words = BusWordsPerPage - 1;
  for (int page = CreatorInfoPage; page <= IsolatedInfoPage; page++) begin
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(rram_data)
    ctrl_op.addr = page * BusWordsPerPage * BusBytes;
    cfg.rram_bkdr_mem_write(ctrl_op, rram_data, .scramble(1'b1));
    exp_page_data[page] = rram_data;
  end
  foreach (SeedInfoPageSel[i]) begin
    for (int k = 0; k < SeedWords; k++) begin
      exp_seeds[i][k * BusWidth +: BusWidth] = exp_page_data[SeedInfoPageSel[i]][k];
    end
  end

  // 2. Initialize the controller with hardware seed reading enabled.
  cfg.misc_vif.lc_seed_hw_rd_en = On;
  wait_lc_sync();
  csr_wr(.ptr(ral.init), .value(1'b1));
  csr_spinwait(.ptr(ral.status.init_done), .exp_data(1'b1));

  // 3. The key manager gets the seeds.
  check_seeds(exp_seeds);

  // 4. Software can read all special info pages if the life cycle controller allows it.
  cfg.misc_vif.lc_creator_seed_sw_rw_en = On;
  cfg.misc_vif.lc_owner_seed_sw_rw_en   = On;
  cfg.misc_vif.lc_iso_part_sw_rd_en     = On;
  wait_lc_sync();
  for (int page = CreatorInfoPage; page <= IsolatedInfoPage; page++) begin
    update_info_page_cfg(page, MuBi4True, MuBi4True, MuBi4True, MuBi4True, MuBi4True);
    ctrl_op.op   = RramOpRead;
    ctrl_op.addr = page * BusWordsPerPage * BusBytes;
    rram_ctrl_read(ctrl_op, rdata);
    foreach (rdata[k]) begin
      `DV_CHECK_EQ(rdata[k], exp_page_data[page][k], $sformatf("Info page %0d word %0d", page, k))
    end
  end

  // 5. Write and read back the special info pages with random life cycle enables. Accesses
  //    without permission fail with a memory protection error. rram_ctrl_write() and
  //    rram_ctrl_read() check the data, since the memory protection model follows the life cycle
  //    enables.
  `DV_CHECK_FATAL(randomize(creator_seed_sw_rw_en, owner_seed_sw_rw_en, iso_part_sw_rd_en,
                            iso_part_sw_wr_en))
  cfg.misc_vif.lc_creator_seed_sw_rw_en = creator_seed_sw_rw_en;
  cfg.misc_vif.lc_owner_seed_sw_rw_en   = owner_seed_sw_rw_en;
  cfg.misc_vif.lc_iso_part_sw_rd_en     = iso_part_sw_rd_en;
  cfg.misc_vif.lc_iso_part_sw_wr_en     = iso_part_sw_wr_en;
  wait_lc_sync();
  `uvm_info(`gfn, $sformatf({"Software access: creator rw=%s, owner rw=%s, isolated rd=%s, ",
                             "isolated wr=%s"}, creator_seed_sw_rw_en.name(),
                            owner_seed_sw_rw_en.name(), iso_part_sw_rd_en.name(),
                            iso_part_sw_wr_en.name()), UVM_LOW)

  for (int page = CreatorInfoPage; page <= IsolatedInfoPage; page++) begin
    ctrl_op.addr      = page * BusWordsPerPage * BusBytes;
    ctrl_op.num_words = $urandom_range(1, BusWordsPerPage / WidthMultiple) * WidthMultiple - 1;
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(rram_data)

    ctrl_op.op = RramOpWrite;
    rram_ctrl_write(ctrl_op, rram_data);
    check_mp_err(!cfg.mp_model.sw_wr_allowed(RramPartInfo, page),
                 $sformatf("Write to info page %0d", page));
    rram_ctrl_wait_wr_done();

    ctrl_op.op = RramOpRead;
    rram_ctrl_read(ctrl_op, rdata);
    check_mp_err(!cfg.mp_model.sw_rd_allowed(RramPartInfo, page),
                 $sformatf("Read of info page %0d", page));
  end

  // 6. The seeds read during initialization do not change.
  check_seeds(exp_seeds);
endtask : body
