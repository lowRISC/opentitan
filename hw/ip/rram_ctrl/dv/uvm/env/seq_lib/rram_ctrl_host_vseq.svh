// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A virtual sequence that performs a single "host" operation (using the host_tl ports)
//
// Note that this currently assumes that there are no enabled emulated info windows (which would
// block host_tl access). If we wish to use this sequence when there are some emulated info windows,
// we'll have to constrain things to ensure there are still readable addresses and will have to
// teach this sequence to avoid the emulated info windows.
//
// Also note that this currently assumes that the enabled regions are disjoint. When two enabled
// regions overlap, the region with the lower index will take precedence. The addr_c constraint
// doesn't currently reason about this. To support overlapping regions, we'd probably have to
// resolve regions into a (possibly larger) set of effective regions in pre_randomize. To check that
// we don't miss this by accident, pre_randomize contains a check that the regions are disjoint.

class rram_ctrl_host_vseq extends uvm_sequence;
  `uvm_object_utils(rram_ctrl_host_vseq)

  // True if this should be a fetch (rather than a data read).
  //
  // Note: This might need to be constrained to be false when randomising the sequence unless we
  // know that the EXEC register holds the special value that allows fetches.
  rand bit m_fetch;

  // The byte address of the read, relative to the start of the data partition
  rand uvm_reg_addr_t m_addr;

  // The size used for the transaction (this translates to the SIZE value on the A and D TileLink
  // channels, which is the base-2 logarithm of the size in bytes).
  rand int unsigned m_size;

  // The RRAM register block. Set this by calling set_ral() before randomising the sequence.
  local rram_ctrl_core_reg_block m_ral;

  // The base address of the host_tl interface on the bus. Set this by calling set_host_base_addr()
  // before randomising the sequence.
  local uvm_reg_addr_t m_host_base_addr;

  // The sequencer for the host interface's tl_agent. Set this by calling set_host_sequencer()
  // before starting the sequence.
  local tl_sequencer m_host_sequencer;

  // Information about the various configured regions. These give the byte address and length, then
  // whether the region is enabled and whether it allows reads.
  //
  // They are computed from the predicted register contents in pre_randomize().
  local uvm_reg_addr_t [NumRegions-1:0] m_region_start_addrs;
  local uvm_reg_addr_t [NumRegions-1:0] m_region_byte_sizes;
  local bit [NumRegions-1:0]            m_region_en;
  local bit [NumRegions-1:0]            m_region_rd_en;
  local bit                             m_default_region_rd_en;

  // The index of the region being addressed. If the stimulus will use the default region instead,
  // this index is constrained to zero.
  rand int unsigned m_region_idx;

  // If this is set, the host_tl access should target an address that is not in any defined region,
  // so permissions are based on DEFAULT_REGION.
  rand bit m_use_default_region;

  extern function new(string name="");
  extern function void pre_randomize();

  extern virtual function void do_print(uvm_printer printer);
  extern task pre_start();
  extern task body();

  // Set the register block (from which the sequence will get configuration information). Call this
  // before randomising the sequence.
  extern function void set_ral(rram_ctrl_core_reg_block ral);

  // Set the base address for the host_tl interface on the bus. Call this before randomising the
  // sequence.
  extern function void set_host_base_addr(uvm_reg_addr_t base_addr);

  // Set the sequencer for the host_tl interface's tl_agent. Call this before starting the sequence.
  extern function void set_host_sequencer(tl_sequencer sequencer);

  extern constraint addr_c;
  extern constraint size_c;
endclass

function rram_ctrl_host_vseq::new(string name="");
  super.new(name);
endfunction

function void rram_ctrl_host_vseq::pre_randomize();
  import rram_ctrl_reg_pkg::BytesPerPage;

  if (m_ral == null) begin
    `uvm_fatal("no_ral", "Register model not set.")
  end

  for (int unsigned i = 0; i < NumRegions; i++) begin
    m_region_start_addrs[i] = m_ral.mp_region[i].base.get_mirrored_value() * BytesPerPage;
    m_region_byte_sizes[i] = (m_ral.mp_region[i].size.get_mirrored_value() + 1) * BytesPerPage;
    m_region_en[i] = (m_ral.mp_region_cfg[i].en.get_mirrored_value() == MuBi4True);
    m_region_rd_en[i] = (m_ral.mp_region_cfg[i].rd_en.get_mirrored_value() == MuBi4True);
  end
  m_default_region_rd_en = (m_ral.default_region.rd_en.get_mirrored_value() == MuBi4True);

  // Check that the enabled regions are genuinely disjoint. See the note at the top of the file for
  // detail about why this is needed.
  for (int unsigned i = 0; i < NumRegions; i++) begin
    if (!m_region_en[i]) continue;
    for (int unsigned j = i + 1; j < NumRegions; j++) begin
      if (!m_region_en[j]) continue;
      if (m_region_start_addrs[i] + m_region_byte_sizes[i] <= m_region_start_addrs[j]) continue;
      if (m_region_start_addrs[j] + m_region_byte_sizes[j] <= m_region_start_addrs[i]) continue;
      `uvm_fatal("overlapping_regions",
                 $sformatf({"Sequence expects to run with disjoint regions but region %0d has ",
                            "range [0x%0h, 0x%0h] and region %0d has range [0x%0h, 0x%0h]."},
                           i,
                           m_region_start_addrs[i],
                           m_region_start_addrs[i] + m_region_byte_sizes[i] - 1,
                           j,
                           m_region_start_addrs[j],
                           m_region_start_addrs[j] + m_region_byte_sizes[j] - 1))
    end
  end
endfunction

function void rram_ctrl_host_vseq::do_print(uvm_printer printer);
  super.do_print(printer);

  printer.print_field_int("m_fetch", m_fetch, 1);
  printer.print_field_int("m_addr", m_addr, $bits(m_addr));
  printer.print_field_int("m_size", m_size, $bits(m_size));
  printer.print_field_int("m_host_base_addr", m_host_base_addr, $bits(m_host_base_addr));

  // Only print out the configuration inferred from registers under UVM_FULL
  if (uvm_report_enabled(UVM_FULL, UVM_INFO, "config")) begin
    for (int unsigned i = 0; i < NumRegions; i++) begin
      printer.print_field_int($sformatf("m_region_start_addrs[%0d]", i),
                              m_region_start_addrs[i],
                              $bits(uvm_reg_addr_t),
                              UVM_HEX);
    end
    for (int unsigned i = 0; i < NumRegions; i++) begin
      printer.print_field_int($sformatf("m_region_byte_sizes[%0d]", i),
                              m_region_byte_sizes[i],
                              $bits(uvm_reg_addr_t),
                              UVM_HEX);
    end
    printer.print_field("m_region_en", m_region_en, NumRegions, UVM_BIN);
    printer.print_field("m_region_rd_en", m_region_rd_en, NumRegions, UVM_BIN);
    printer.print_field("m_default_region_rd_en", m_default_region_rd_en, 1, UVM_BIN);
  end

  printer.print_field_int("m_region_idx", m_region_idx, 32);
  printer.print_field_int("m_use_default_region", m_use_default_region, 1);
endfunction

task rram_ctrl_host_vseq::pre_start();
  if (m_host_sequencer == null) `uvm_fatal("no_sqr", "No sequencer for host_tl interface.")

  super.pre_start();
endtask

task rram_ctrl_host_vseq::body();
  cip_tl_host_single_seq seq = cip_tl_host_single_seq::type_id::create("seq");

  if (!seq.randomize() with {
        write == 0;
        mask == ((1 << (1 << local::m_size)) - 1) << local::m_addr[1:0];
        addr == local::m_addr + local::m_host_base_addr;
        size == local::m_size;
        instr_type == (local::m_fetch ? MuBi4True : MuBi4False);
      }) begin
    `uvm_fatal("rand_failed", "Failed to randomize TL sequence item.")
  end

  // Make sure the item from the sequence obeys the address alignment and size that we have chosen
  seq.control_addr_alignment = 1;
  seq.control_rand_size      = 1;

  seq.start(m_host_sequencer);
endtask

function void rram_ctrl_host_vseq::set_ral(rram_ctrl_core_reg_block ral);
  m_ral = ral;
endfunction

function void rram_ctrl_host_vseq::set_host_base_addr(uvm_reg_addr_t base_addr);
  m_host_base_addr = base_addr;
endfunction

function void rram_ctrl_host_vseq::set_host_sequencer(tl_sequencer sequencer);
  m_host_sequencer = sequencer;
endfunction

constraint rram_ctrl_host_vseq::addr_c {
  // The top of the access must be below the start of the OTP pages (also visible in the address
  // space, but not accessible to host_tl). Splitting the constraint into two pieces like this
  // ensures that we don't get spurious examples that wrap over the top of uvm_reg_addr_t.
  m_addr <= OtpStartPage * rram_ctrl_reg_pkg::BytesPerPage;
  1 << m_size <= OtpStartPage * rram_ctrl_reg_pkg::BytesPerPage - m_addr;

  // Only use the default region if m_default_region_rd_en is set
  !m_default_region_rd_en -> !m_use_default_region;

  if (m_use_default_region) {
    foreach (m_region_start_addrs[i]) {
      // Either the region must be disabled, or the access must start after the top of the region,
      // or the top byte of the access must be before the start of the region.
      (!m_region_en[i] ||
       (m_region_start_addrs[i] + m_region_byte_sizes[i] <= m_addr) ||
       (m_addr + (1 << m_size) <= (m_region_start_addrs[i])));
    }
    m_region_idx == 0;
  } else {
    // Choose a valid region index.
    m_region_idx < NumRegions;

    // The region must be enabled and support reads.
    m_region_en[m_region_idx];
    m_region_rd_en[m_region_idx];

    // The address must be above the start of the region
    m_region_start_addrs[m_region_idx] <= m_addr;

    // The highest byte in the access must be before the end of the region. This byte has address
    // m_addr + (1 << m_size) - 1 and the highest byte in the region has address
    // m_region_start_addrs[m_region_idx] + m_region_byte_sizes[m_region_idx] - 1.
    m_addr + (1 << m_size) <= (m_region_start_addrs[m_region_idx] +
                               m_region_byte_sizes[m_region_idx]);
  }
}

constraint rram_ctrl_host_vseq::size_c {
  // The size must be at most 2 (a 32-bit access)
  m_size <= 2;

  // The address must be naturally aligned for m_size, so its bottom m_size bits must all be zero.
  ~|(m_addr & ((1 << m_size) - 1));
}
