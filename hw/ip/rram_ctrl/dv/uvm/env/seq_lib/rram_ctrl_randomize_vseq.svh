// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A virtual sequence that will pick a random configuration for the MP_REGION_*, MP_REGION_CFG,
// DEFAULT_REGION and INFO_PAGE_CFG_* registers.

class rram_ctrl_randomize_vseq extends uvm_sequence;
  `uvm_object_utils(rram_ctrl_randomize_vseq)

  // A status that accumulates the results of all the register transactions in the sequence. When
  // start finishes, it will either be UVM_IS_OK (if everything worked) or UVM_NOT_OK (if anything
  // failed).
  uvm_status_e m_status = UVM_IS_OK;

  // The RRAM register block. Set this by calling set_ral() before starting the sequence.
  local rram_ctrl_core_reg_block m_ral;

  // How many regions should be enabled by the virtual sequence? Constrained by
  // enabled_regions_c.
  local rand int unsigned m_num_enabled_regions;

  // The "en" and "rd_en" bits that will be used in m_region_cfgs (split out because it makes
  // reasoning about the fields in constraints much simpler)
  local rand bit [NumRegions-1:0] m_enabled_regions;
  local rand bit [NumRegions-1:0] m_read_enabled_regions;

  // The NumRegions configurations that will be written to the MP_REGION_CFG_* registers.
  local rand region_cfg_setting m_region_cfgs[];

  // An array of configurations for the NumRegions MP_REGION_* registers. These ones are constrained
  // to be in increasing order of base (which makes the constraints easier to write).
  local rand region_setting m_increasing_regions[];

  // The array of configurations that get written to the NumRegions MP_REGION_* registers, in the
  // order of those registers (with a mapping dictated by m_reg_order_idx_map). The values are
  // copied across in post_randomize.
  local region_setting m_regions[];

  // The index mapping array that relates m_increasing_regions and m_regions. This is a permutation
  // of (0, 1, ..., NumRegions-1). Element i gives the index of the element in m_increasing_regions
  // that will be used for m_regions[i].
  local rand int unsigned m_reg_order_idx_map[];

  // The configuration that should be written to the DEFAULT_REGION register.
  local rand region_cfg_setting_base m_default_region_cfg;

  // How many info pages should be enabled by the virtual sequence? Constrained by
  // num_enabled_info_pages_c.
  local rand int unsigned m_num_enabled_info_pages;

  // The "en" bits that will be used in m_info_page_cfgs (split out because it makes counting the
  // number that are set much simpler)
  local rand bit [NumInfoPages-1:0] m_enabled_info_pages;

  // The configs that should be used for the info pages (in INFO_PAGE_CFG_*).
  local rand region_cfg_setting m_info_page_cfgs[];

  extern function new(string name="");
  extern function void post_randomize();
  extern task pre_start();

  extern virtual function void do_print(uvm_printer printer);
  extern task body();

  // Set the register block that the virtual sequence will configure. Call this before starting the
  // sequence.
  extern function void set_ral(rram_ctrl_core_reg_block ral);

  extern local task write_region_cfgs(output uvm_status_e status);
  extern local task write_one_region_cfg(int unsigned idx, output uvm_status_e status);

  extern local task write_regions(output uvm_status_e status);
  extern local task write_one_region(int unsigned idx, output uvm_status_e status);

  extern local task write_default_region(output uvm_status_e status);

  extern local task write_info_page_cfgs(output uvm_status_e status);
  extern local task write_one_info_page_cfg(int unsigned idx, output uvm_status_e status);

  // There should be between 1 and NumRegions enabled regions (we want at least one to be enabled).
  // A bit in m_enabled_regions must be a boolean version of the en field in the respective element
  // of m_region_cfgs. Similarly, a bit in m_read_enabled_regions must be a boolean version of the
  // rd_en field in the respective element of m_region_cfgs.
  //
  // What's more, there are m_num_enabled_regions bits set in m_enabled_regions (which will cause
  // that many regions to be enabled).
  extern constraint enabled_regions_c;

  // The elements of m_increasing_regions should be ordered with the bases strictly increasing and
  // should be disjoint (so the difference in two base fields is more than the earlier region's
  // size). Finally, the last region should fit in the number of available pages.
  extern constraint increasing_regions_c;

  // The values of m_reg_order_idx_map should be a permutation of 0..NumRegions-1 and should give
  // the order of m_regions.
  extern constraint regions_idx_map_c;

  // There should be at least one way to read RRAM, either through an enabled region with rd_en
  // enabled, or because default_region has rd_en enabled.
  //
  // This constraint allows downstream sequences to assume there will be *some* way to read from
  // RRAM.
  extern constraint something_readable_c;

  // The number of enabled info pages (m_num_enabled_info_pages) should be between 1 and
  // NumInfoPages (we want at least one to be enabled)
  extern constraint num_enabled_info_pages_c;

  // A bit in m_enabled_info_pages must equal the en field in the respective element of
  // m_info_page_cfgs.
  //
  // What's more, there are m_num_enabled_info_pages bits set in m_enabled_info_pages (which will
  // cause that many info pages to be enabled).
  extern constraint enabled_info_pages_c;
endclass

function rram_ctrl_randomize_vseq::new(string name="");
  super.new(name);

  m_region_cfgs = new[NumRegions];
  foreach (m_region_cfgs[i]) m_region_cfgs[i] = new();

  m_default_region_cfg = new();

  m_info_page_cfgs = new[NumInfoPages];
  foreach (m_info_page_cfgs[i]) m_info_page_cfgs[i] = new();

  m_increasing_regions = new[NumRegions];
  foreach (m_increasing_regions[i]) m_increasing_regions[i] = new();
endfunction

function void rram_ctrl_randomize_vseq::post_randomize();
  // Link elements of m_regions to elements of m_increasing_regions, in the order dictated by
  // m_reg_order_idx_map.
  m_regions = new[NumRegions];
  foreach (m_regions[i]) begin
    m_regions[i] = m_increasing_regions[m_reg_order_idx_map[i]];
  end
endfunction

task rram_ctrl_randomize_vseq::pre_start();
  if (m_ral == null) begin
    `uvm_fatal("no_ral", "Register model not set.")
  end
endtask

function void rram_ctrl_randomize_vseq::do_print(uvm_printer printer);
  super.do_print(printer);
  printer.print_field_int("m_num_enabled_regions", m_num_enabled_regions, 32);
  printer.print_field("m_enabled_regions", m_enabled_regions, NumRegions, UVM_BIN);
  printer.print_field("m_read_enabled_regions", m_read_enabled_regions, NumRegions, UVM_BIN);
  foreach (m_region_cfgs[i]) begin
    // Only print out enabled regions unless printing at UVM_HIGH or greater.
    if (m_enabled_regions[i] || uvm_report_enabled(UVM_HIGH, UVM_INFO, "m_region_cfgs")) begin
      m_region_cfgs[i].named_print($sformatf("m_region_cfgs[%0d]", i), printer);
    end
  end
  // Only print the list of region values in memory order (rather than register order) if printing
  // at UVM_HIGH or higher,
  if (uvm_report_enabled(UVM_HIGH, UVM_INFO, "m_increasing_regions")) begin
    foreach (m_increasing_regions[i]) begin
      m_increasing_regions[i].named_print($sformatf("m_increasing_regions[%0d]", i), printer);
    end
  end
  foreach (m_regions[i]) begin
    // Only print out a region if it is enabled or we are printing at UVM_HIGH or greater.
    if (m_enabled_regions[i] || uvm_report_enabled(UVM_HIGH, UVM_INFO, "m_regions")) begin
      m_regions[i].named_print($sformatf("m_regions[%0d]", i), printer);
    end
  end
  // Only print the index mapping between the different lists of region configurations at UVM_HIGH
  // or greater.
  if (uvm_report_enabled(UVM_HIGH, UVM_INFO, "m_reg_order_idx_map")) begin
    foreach (m_reg_order_idx_map[i]) begin
      printer.print_field_int($sformatf("m_reg_order_idx_map[%0d]", i), m_reg_order_idx_map[i], 32);
    end
  end

  m_default_region_cfg.named_print("m_default_region_cfg", printer);

  printer.print_field_int("m_num_enabled_info_pages", m_num_enabled_info_pages, 32);
  printer.print_field("m_enabled_info_pages", m_enabled_info_pages, NumInfoPages, UVM_BIN);
  foreach (m_info_page_cfgs[i]) begin
    // Only print out enabled info pages unless printing at UVM_HIGH or greater.
    if (m_enabled_info_pages[i] || uvm_report_enabled(UVM_HIGH, UVM_INFO, "m_info_page_cfgs")) begin
      m_info_page_cfgs[i].named_print($sformatf("m_info_page_cfgs[%0d]", i), printer);
    end
  end
endfunction

task rram_ctrl_randomize_vseq::body();
  uvm_status_e cfg_status, region_status, default_status, info_status;

  // At UVM_MEDIUM, print the configuration we're about to write
  if (uvm_report_enabled(UVM_MEDIUM, UVM_INFO, "config")) begin
    `uvm_info("config", "Randomized configuration sequence:", UVM_MEDIUM)
    print();
  end

  fork
    write_region_cfgs(cfg_status);
    write_regions(region_status);
    write_default_region(default_status);
    write_info_page_cfgs(info_status);
  join

  m_status = UVM_IS_OK;
  if (cfg_status != UVM_IS_OK) m_status = UVM_NOT_OK;
  if (region_status != UVM_IS_OK) m_status = UVM_NOT_OK;
  if (default_status != UVM_IS_OK) m_status = UVM_NOT_OK;
  if (info_status != UVM_IS_OK) m_status = UVM_NOT_OK;
endtask

function void rram_ctrl_randomize_vseq::set_ral(rram_ctrl_core_reg_block ral);
  m_ral = ral;
endfunction

task rram_ctrl_randomize_vseq::write_region_cfgs(output uvm_status_e status);
  status = UVM_IS_OK;

  fork : isolation_fork begin
    for (int unsigned i = 0; i < NumRegions; i++) begin
      automatic int unsigned i_ = i;
      fork begin
        uvm_status_e one_status;
        write_one_region_cfg(i_, one_status);
        if (one_status != UVM_IS_OK) status = UVM_NOT_OK;
      end join_none
    end
    wait fork;
  end join
endtask

task rram_ctrl_randomize_vseq::write_one_region_cfg(int unsigned idx, output uvm_status_e status);
  uvm_reg_data_t wdata = 0;
  wdata |= m_region_cfgs[idx].en << m_ral.mp_region_cfg[idx].en.get_lsb_pos();
  wdata |= m_region_cfgs[idx].rd_en << m_ral.mp_region_cfg[idx].rd_en.get_lsb_pos();
  wdata |= m_region_cfgs[idx].wr_en << m_ral.mp_region_cfg[idx].wr_en.get_lsb_pos();
  wdata |= m_region_cfgs[idx].scramble_en << m_ral.mp_region_cfg[idx].scramble_en.get_lsb_pos();
  wdata |= m_region_cfgs[idx].ecc_en << m_ral.mp_region_cfg[idx].ecc_en.get_lsb_pos();

  m_ral.mp_region_cfg[idx].write(status, wdata);
endtask

task rram_ctrl_randomize_vseq::write_regions(output uvm_status_e status);
  status = UVM_IS_OK;

  fork : isolation_fork begin
    for (int unsigned i = 0; i < NumRegions; i++) begin
      automatic int unsigned i_ = i;
      fork begin
        uvm_status_e one_status;
        write_one_region(i_, one_status);
        if (one_status != UVM_IS_OK) status = UVM_NOT_OK;
      end join_none
    end
    wait fork;
  end join
endtask

task rram_ctrl_randomize_vseq::write_one_region(int unsigned idx, output uvm_status_e status);
  uvm_reg_data_t wdata = 0;
  wdata |= m_regions[idx].base << m_ral.mp_region[idx].base.get_lsb_pos();
  wdata |= m_regions[idx].size << m_ral.mp_region[idx].size.get_lsb_pos();

  m_ral.mp_region[idx].write(status, wdata);
endtask

task rram_ctrl_randomize_vseq::write_default_region(output uvm_status_e status);
  uvm_reg_data_t wdata = 0;
  wdata |= m_default_region_cfg.rd_en << m_ral.default_region.rd_en.get_lsb_pos();
  wdata |= m_default_region_cfg.wr_en << m_ral.default_region.wr_en.get_lsb_pos();
  wdata |= m_default_region_cfg.scramble_en << m_ral.default_region.scramble_en.get_lsb_pos();
  wdata |= m_default_region_cfg.ecc_en << m_ral.default_region.ecc_en.get_lsb_pos();

  m_ral.default_region.write(status, wdata);
endtask

task rram_ctrl_randomize_vseq::write_info_page_cfgs(output uvm_status_e status);
  status = UVM_IS_OK;

  fork : isolation_fork begin
    for (int unsigned i = 0; i < NumInfoPages; i++) begin
      automatic int unsigned i_ = i;
      fork begin
        uvm_status_e one_status;
        write_one_info_page_cfg(i_, one_status);
        if (one_status != UVM_IS_OK) status = UVM_NOT_OK;
      end join_none
    end
    wait fork;
  end join
endtask

task rram_ctrl_randomize_vseq::write_one_info_page_cfg(int unsigned idx,
                                                       output       uvm_status_e status);
  uvm_reg_data_t wdata = 0;
  wdata |= m_info_page_cfgs[idx].en << m_ral.info_page_cfg[idx].en.get_lsb_pos();
  wdata |= m_info_page_cfgs[idx].rd_en << m_ral.info_page_cfg[idx].rd_en.get_lsb_pos();
  wdata |= m_info_page_cfgs[idx].wr_en << m_ral.info_page_cfg[idx].wr_en.get_lsb_pos();
  wdata |= m_info_page_cfgs[idx].scramble_en << m_ral.info_page_cfg[idx].scramble_en.get_lsb_pos();
  wdata |= m_info_page_cfgs[idx].ecc_en << m_ral.info_page_cfg[idx].ecc_en.get_lsb_pos();

  m_ral.info_page_cfg[idx].write(status, wdata);
endtask

constraint rram_ctrl_randomize_vseq::enabled_regions_c {
  1 <= m_num_enabled_regions;
  m_num_enabled_regions <= NumRegions;

  $countones(m_enabled_regions) == m_num_enabled_regions;

  foreach (m_region_cfgs[i]) {
    (m_region_cfgs[i].en == MuBi4True) == m_enabled_regions[i];
    (m_region_cfgs[i].rd_en == MuBi4True) == m_read_enabled_regions[i];
  }
}

constraint rram_ctrl_randomize_vseq::increasing_regions_c {
  // Check that the regions are genuinely in order and disjoint. The type-cast widens the
  // calculation to ensure there is no overflow (so base + size overflowing the 12 bit counter
  // doesn't cause it to pass)
  foreach (m_increasing_regions[i]) {
    if (i > 0) {
      (m_increasing_regions[i - 1].base +
       m_increasing_regions[i - 1].size) < 13'(m_increasing_regions[i].base);
    }
  }

  // Check that the last region's top page (with index base + size) doesn't overflow the size of the
  // data partition.
  m_increasing_regions[NumRegions-1].base + m_increasing_regions[NumRegions-1].size < NumDataPages;
}

constraint rram_ctrl_randomize_vseq::regions_idx_map_c {
  m_reg_order_idx_map.size == NumRegions;

  // m_reg_order_idx_map should be a permutation of the indices. To check this, we require that they
  // are distinct and in the range 0..NumRegions-1.
  unique {m_reg_order_idx_map};
  foreach (m_reg_order_idx_map[i]) { m_reg_order_idx_map[i] < NumRegions; }
}

constraint rram_ctrl_randomize_vseq::something_readable_c {
  // There must either be some enabled region with rd_en set or there must be a gap in between the
  // regions and the default region must have rd_en set.
  //
  // For the latter case, we can reason about the fact that the regions are chosen to be disjoint
  // (whether or not they are enabled). As such, there will be a gap between the enabled regions if
  // some region is not enabled.
  //
  // There is still a gap in both cases: we have a region whose addresses have rd_en set (either
  // because the region is enabled with that flag set or because it is disabled and default_region
  // has the flag set). Unfortunately, it's possible for that "region of safety" to be completely
  // contained in the OTP region, where SW and host_tl accesses would be denied.
  //
  // To avoid that problem, we cheat slightly and mandate that the highest region must start
  // strictly before the first page of the OTP region. If we decide in future that a region
  // contained in the OTP region is one we need to reason about, we'll have to generalise this
  // slightly.
  m_increasing_regions[NumRegions-1].base < OtpStartPage;

  (|(m_enabled_regions & m_read_enabled_regions)) ||
   (~&m_enabled_regions && (m_default_region_cfg.rd_en == MuBi4True));
}

constraint rram_ctrl_randomize_vseq::num_enabled_info_pages_c {
  1 <= m_num_enabled_info_pages;
  m_num_enabled_info_pages <= NumInfoPages;
}

constraint rram_ctrl_randomize_vseq::enabled_info_pages_c {
  foreach (m_info_page_cfgs[i]) {
    (m_info_page_cfgs[i].en == MuBi4True) == m_enabled_info_pages[i];
  }

  $countones(m_enabled_info_pages) == m_num_enabled_info_pages;
}
