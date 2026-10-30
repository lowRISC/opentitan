// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Memory protection model of rram_ctrl.
//
// Holds the effective page configuration (access permissions, scrambling, ECC and address
// infection) of every page, as seen by software requests through the controller interface and by
// requests on the host interface.
// The configuration is derived from the core RAL model's mirrored values and the life cycle
// enables, mirroring rram_ctrl_region_cfg.sv and rram_ctrl_mp.sv.
//
// The data partition is modelled as one array per interface, so that each lookup is a plain array
// access.
// Recomputing these arrays is comparatively expensive, so the scoreboard only flags them as stale
// (see invalidate()) whenever it sees a write to a register that changes them.
// They are recomputed on the next lookup.
// The few info pages are cheap to compute and also depend on the life cycle enables, which can
// change at any time, so they are computed on every lookup.
//
// Not modelled: hardware interface rules (life cycle manager and OTP requests), and the global
// disable of all accesses on escalation or RMA.
class rram_ctrl_mp_model extends uvm_object;
  `uvm_object_utils(rram_ctrl_mp_model)

  // Core RAL model the configuration is read from. Set by rram_ctrl_env_cfg.
  rram_ctrl_core_reg_block ral;

  // Life cycle enables that restrict software access to the creator, owner and isolated info
  // pages. Set by rram_ctrl_env.
  misc_vif_t misc_vif;

  // Effective configuration of every data page for software and host requests.
  protected page_cfg_t sw_data_page_cfg[TotalDataPages];
  protected page_cfg_t host_data_page_cfg[TotalDataPages];

  // Set once an RMA was requested. The DUT then denies all accesses from a point in time that the
  // model cannot predict, so host errors are not checked any more. Cleared on reset.
  bit rma_requested;

  // Set when the data page arrays above no longer match the RAL model.
  protected bit stale = 1'b1;

  // Registers whose value changes the data page arrays above.
  protected bit data_cfg_regs[uvm_reg];

  // Standard SV/UVM methods
  extern function new(string name = "");

  // Class specific methods

  // Collects the registers that affect the data page configuration. Called once the RAL model is
  // built and locked.
  extern function void initialize(rram_ctrl_core_reg_block ral);

  // Returns 1 if a write to `csr` can change the data page configuration.
  extern function bit is_data_cfg_reg(uvm_reg csr);

  // Flags the data page configuration as stale, so it is recomputed on the next lookup.
  extern function void invalidate();

  // Returns the effective configuration of `page` in partition `part` for software requests
  // through the controller interface. Out-of-range pages return CfgDisable.
  extern function page_cfg_t get_sw_page_cfg(rram_part_e part, int unsigned page);

  // Returns the effective configuration of data page `page` for host requests.
  extern function page_cfg_t get_host_page_cfg(int unsigned page);

  // Convenience functions on top of the above, matching the mubi4 checks of rram_ctrl_mp.sv.
  extern function bit sw_rd_allowed(rram_part_e part, int unsigned page);
  extern function bit sw_wr_allowed(rram_part_e part, int unsigned page);
  extern function bit host_rd_allowed(int unsigned page);

  // Recomputes the data page arrays from the RAL model.
  extern protected function void update_data_pages();

  // Builds the prioritized region lists of rram_ctrl_region_cfg.sv for software and host
  // requests, lowest index first.
  extern protected function void get_regions(output mp_region_cfg_t sw_regions[$],
                                             output mp_region_cfg_t host_regions[$]);

  // Assigns the configuration of the highest-priority enabled region to every page it covers.
  extern protected function void apply_regions(const ref mp_region_cfg_t regions[$],
                                               ref page_cfg_t page_cfg[TotalDataPages]);
endclass : rram_ctrl_mp_model


function rram_ctrl_mp_model::new(string name = "");
  super.new(name);
endfunction : new

function void rram_ctrl_mp_model::initialize(rram_ctrl_core_reg_block ral);
  this.ral = ral;
  data_cfg_regs[ral.default_region] = 1'b1;
  foreach (ral.mp_region[i])                  data_cfg_regs[ral.mp_region[i]] = 1'b1;
  foreach (ral.mp_region_cfg[i])              data_cfg_regs[ral.mp_region_cfg[i]] = 1'b1;
  foreach (ral.emul_info_regwen[i])           data_cfg_regs[ral.emul_info_regwen[i]] = 1'b1;
  foreach (ral.emul_info_region[i])           data_cfg_regs[ral.emul_info_region[i]] = 1'b1;
  foreach (ral.emul_info_subregion_regwen[i]) begin
    data_cfg_regs[ral.emul_info_subregion_regwen[i]] = 1'b1;
  end
  foreach (ral.emul_info_subregion[i])        data_cfg_regs[ral.emul_info_subregion[i]] = 1'b1;
  foreach (ral.emul_info_subregion_cfg[i])    data_cfg_regs[ral.emul_info_subregion_cfg[i]] = 1'b1;
  invalidate();
endfunction : initialize

function bit rram_ctrl_mp_model::is_data_cfg_reg(uvm_reg csr);
  return data_cfg_regs.exists(csr);
endfunction : is_data_cfg_reg

function void rram_ctrl_mp_model::invalidate();
  stale = 1'b1;
endfunction : invalidate

function page_cfg_t rram_ctrl_mp_model::get_sw_page_cfg(rram_part_e part, int unsigned page);
  page_cfg_t   cfg;
  mubi4_t      lc_rd_en, lc_wr_en;
  uvm_reg_data_t val;

  if (part == RramPartData) begin
    if (page >= TotalDataPages) return CfgDisable;
    if (stale) update_data_pages();
    return sw_data_page_cfg[page];
  end

  if (page >= TotalInfoPages) return CfgDisable;
  val = ral.info_page_cfg[page].get_mirrored_value();
  cfg.en          = mubi4_t'(get_field_val(ral.info_page_cfg[page].en, val));
  cfg.rd_en       = mubi4_t'(get_field_val(ral.info_page_cfg[page].rd_en, val));
  cfg.wr_en       = mubi4_t'(get_field_val(ral.info_page_cfg[page].wr_en, val));
  cfg.scramble_en = mubi4_t'(get_field_val(ral.info_page_cfg[page].scramble_en, val));
  cfg.ecc_en      = mubi4_t'(get_field_val(ral.info_page_cfg[page].ecc_en, val));
  cfg.addr_xor_en = MuBi4True;

  // The life cycle controller can overrule access to the creator, owner and isolated pages.
  case (page)
    CreatorInfoPage: begin
      lc_rd_en = lc_ctrl_pkg::lc_to_mubi4(misc_vif.lc_creator_seed_sw_rw_en);
      lc_wr_en = lc_rd_en;
    end
    OwnerInfoPage: begin
      lc_rd_en = lc_ctrl_pkg::lc_to_mubi4(misc_vif.lc_owner_seed_sw_rw_en);
      lc_wr_en = lc_rd_en;
    end
    IsolatedInfoPage: begin
      lc_rd_en = lc_ctrl_pkg::lc_to_mubi4(misc_vif.lc_iso_part_sw_rd_en);
      lc_wr_en = lc_ctrl_pkg::lc_to_mubi4(misc_vif.lc_iso_part_sw_wr_en);
    end
    default: begin
      lc_rd_en = MuBi4True;
      lc_wr_en = MuBi4True;
    end
  endcase
  cfg.rd_en = prim_mubi_pkg::mubi4_and_hi(cfg.rd_en, lc_rd_en);
  cfg.wr_en = prim_mubi_pkg::mubi4_and_hi(cfg.wr_en, lc_wr_en);
  return cfg;
endfunction : get_sw_page_cfg

function page_cfg_t rram_ctrl_mp_model::get_host_page_cfg(int unsigned page);
  if (page >= TotalDataPages) return CfgDisable;
  if (stale) update_data_pages();
  return host_data_page_cfg[page];
endfunction : get_host_page_cfg

function bit rram_ctrl_mp_model::sw_rd_allowed(rram_part_e part, int unsigned page);
  page_cfg_t cfg = get_sw_page_cfg(part, page);
  return (cfg.en == MuBi4True) && (cfg.rd_en == MuBi4True);
endfunction : sw_rd_allowed

function bit rram_ctrl_mp_model::sw_wr_allowed(rram_part_e part, int unsigned page);
  page_cfg_t cfg = get_sw_page_cfg(part, page);
  return (cfg.en == MuBi4True) && (cfg.wr_en == MuBi4True);
endfunction : sw_wr_allowed

function bit rram_ctrl_mp_model::host_rd_allowed(int unsigned page);
  page_cfg_t cfg = get_host_page_cfg(page);
  return (cfg.en == MuBi4True) && (cfg.rd_en == MuBi4True);
endfunction : host_rd_allowed

function void rram_ctrl_mp_model::update_data_pages();
  mp_region_cfg_t sw_regions[$], host_regions[$];
  get_regions(sw_regions, host_regions);
  apply_regions(sw_regions, sw_data_page_cfg);
  apply_regions(host_regions, host_data_page_cfg);
  stale = 1'b0;
endfunction : update_data_pages

function void rram_ctrl_mp_model::get_regions(output mp_region_cfg_t sw_regions[$],
                                              output mp_region_cfg_t host_regions[$]);
  mp_region_cfg_t window_deny[EmulInfoRegions];
  mp_region_cfg_t subregion[EmulInfoSubregions];
  mp_region_cfg_t generic[MpRegions];
  mp_region_cfg_t default_region;
  bit             window_en[EmulInfoRegions];
  bit             window_locked[EmulInfoRegions];
  bit             window_overlap[EmulInfoRegions];
  int unsigned    window_end[EmulInfoRegions];
  bit             chain_locked;
  uvm_reg_data_t  val;

  // Emulated info windows. Each denies all accesses not covered by one of its enabled subregions.
  foreach (window_deny[w]) begin
    val = ral.emul_info_region[w].get_mirrored_value();
    window_deny[w].base   = get_field_val(ral.emul_info_region[w].base, val);
    window_deny[w].size   = get_field_val(ral.emul_info_region[w].size, val);
    window_deny[w].phase  = PhaseInvalid;
    window_deny[w].cfg    = CfgDisable;
    window_deny[w].cfg.en = mubi4_t'(get_field_val(ral.emul_info_region[w].en, val));
    window_en[w]          = window_deny[w].cfg.en == MuBi4True;
    window_locked[w]      = !ral.emul_info_regwen[w].region.get_mirrored_value();
    window_end[w]         = int'(window_deny[w].base) + int'(window_deny[w].size);
  end

  // If two enabled windows overlap, the subregions of both are disabled.
  foreach (window_overlap[a]) begin
    window_overlap[a] = 1'b0;
    foreach (window_overlap[b]) begin
      if (a != b && window_en[a] && window_en[b] &&
          window_deny[a].base <= window_end[b] && window_deny[b].base <= window_end[a]) begin
        window_overlap[a] = 1'b1;
      end
    end
  end

  // Emulated info subregions.
  // All subregions of a window share its base and lower indices have priority, so each one
  // effectively covers the pages from the end of the prior one up to its own TOP.
  // A subregion is enabled once its window is enabled and locked, the placement of the subregion
  // and of all lower-indexed subregions of the same window is locked, its TOP fits within the
  // window and the window does not overlap another enabled window.
  foreach (subregion[i]) begin
    int unsigned w = i / EmulInfoSubregionsPerRegion;
    bit          placement_locked = !ral.emul_info_subregion_regwen[i].region.get_mirrored_value();
    bit          overflow_ok;

    if (i % EmulInfoSubregionsPerRegion == 0) begin
      chain_locked = placement_locked && window_locked[w] && window_en[w];
    end else begin
      chain_locked = chain_locked && placement_locked;
    end

    subregion[i].base  = window_deny[w].base;
    subregion[i].size  = ral.emul_info_subregion[i].top.get_mirrored_value();
    subregion[i].phase = PhaseInvalid;
    overflow_ok        = subregion[i].size <= window_deny[w].size;

    val = ral.emul_info_subregion_cfg[i].get_mirrored_value();
    subregion[i].cfg.en = (chain_locked && overflow_ok && !window_overlap[w]) ?
                          MuBi4True : MuBi4False;
    subregion[i].cfg.rd_en       = mubi4_t'(get_field_val(ral.emul_info_subregion_cfg[i].rd_en,
                                                          val));
    subregion[i].cfg.wr_en       = mubi4_t'(get_field_val(ral.emul_info_subregion_cfg[i].wr_en,
                                                          val));
    subregion[i].cfg.scramble_en =
        mubi4_t'(get_field_val(ral.emul_info_subregion_cfg[i].scramble_en, val));
    subregion[i].cfg.ecc_en      = mubi4_t'(get_field_val(ral.emul_info_subregion_cfg[i].ecc_en,
                                                          val));
    subregion[i].cfg.addr_xor_en = MuBi4True;
  end

  // Configurable regions.
  foreach (generic[i]) begin
    val = ral.mp_region[i].get_mirrored_value();
    generic[i].base  = get_field_val(ral.mp_region[i].base, val);
    generic[i].size  = get_field_val(ral.mp_region[i].size, val);
    generic[i].phase = PhaseInvalid;
    val = ral.mp_region_cfg[i].get_mirrored_value();
    generic[i].cfg.en          = mubi4_t'(get_field_val(ral.mp_region_cfg[i].en, val));
    generic[i].cfg.rd_en       = mubi4_t'(get_field_val(ral.mp_region_cfg[i].rd_en, val));
    generic[i].cfg.wr_en       = mubi4_t'(get_field_val(ral.mp_region_cfg[i].wr_en, val));
    generic[i].cfg.scramble_en = mubi4_t'(get_field_val(ral.mp_region_cfg[i].scramble_en, val));
    generic[i].cfg.ecc_en      = mubi4_t'(get_field_val(ral.mp_region_cfg[i].ecc_en, val));
    generic[i].cfg.addr_xor_en = MuBi4True;
  end

  // The default region covers all pages and applies if no other region matched.
  val = ral.default_region.get_mirrored_value();
  default_region.base            = '0;
  default_region.size            = TotalDataPages - 1;
  default_region.phase           = PhaseInvalid;
  default_region.cfg.en          = MuBi4True;
  default_region.cfg.rd_en       = mubi4_t'(get_field_val(ral.default_region.rd_en, val));
  default_region.cfg.wr_en       = mubi4_t'(get_field_val(ral.default_region.wr_en, val));
  default_region.cfg.scramble_en = mubi4_t'(get_field_val(ral.default_region.scramble_en, val));
  default_region.cfg.ecc_en      = mubi4_t'(get_field_val(ral.default_region.ecc_en, val));
  default_region.cfg.addr_xor_en = MuBi4True;

  // Software requests: OTP exclusion, subregions, window-deny entries, configurable regions and
  // the default region.
  sw_regions.delete();
  sw_regions.push_back(SwInitDataCfg);
  foreach (subregion[i])   sw_regions.push_back(subregion[i]);
  foreach (window_deny[w]) sw_regions.push_back(window_deny[w]);
  foreach (generic[i])     sw_regions.push_back(generic[i]);
  sw_regions.push_back(default_region);

  // Host requests always deny the OTP region and all enabled windows entirely.
  host_regions.delete();
  host_regions.push_back(SwInitDataCfg);
  foreach (window_deny[w]) host_regions.push_back(window_deny[w]);
  foreach (generic[i])     host_regions.push_back(generic[i]);
  host_regions.push_back(default_region);
endfunction : get_regions

function void rram_ctrl_mp_model::apply_regions(const ref mp_region_cfg_t regions[$],
                                                ref page_cfg_t page_cfg[TotalDataPages]);
  foreach (page_cfg[p]) page_cfg[p] = CfgDisable;

  // Apply the regions from lowest to highest priority, so that higher-priority regions overwrite
  // the pages they share with lower-priority ones.
  for (int i = regions.size() - 1; i >= 0; i--) begin
    int unsigned last;
    if (regions[i].cfg.en != MuBi4True) continue;
    last = int'(regions[i].base) + int'(regions[i].size);
    if (last >= TotalDataPages) last = TotalDataPages - 1;
    for (int unsigned p = regions[i].base; p <= last; p++) page_cfg[p] = regions[i].cfg;
  end
endfunction : apply_regions
