// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// JTAG DTM registers based on RISCV JTAG debug spec (see section 6.1.2):
// https://github.com/riscv/riscv-debug-spec/raw/4e0bb0fc2d843473db2356623792c6b7603b94d4/riscv-debug-release.pdf

class jtag_dtm_base_reg extends dv_base_reg;
  `uvm_object_utils(jtag_dtm_base_reg)

  function new(string       name = "jtag_dtm_base_reg",
               int unsigned n_bits = 32,
               int          has_coverage = UVM_NO_COVERAGE);
    super.new(name, n_bits, has_coverage);
  endfunction : new

  // When reading DTM CSR, we write the previous value that we through we wrote before, to maintain
  // consistency, since the JTAG protocol parallely writes and reads the DR at all times. This
  // function is used to return the data we want to write to the DTM DR on reads. For the most part,
  // it is the mirrored value. But in some cases, we may not want to rewrite some fields.
  virtual function uvm_reg_data_t get_wdata_for_read();
    return get_mirrored_value();
  endfunction

endclass

class jtag_dtm_reg_bypass extends jtag_dtm_base_reg;
  // fields
  rand dv_base_reg_field bypass;

  `uvm_object_utils(jtag_dtm_reg_bypass)

  function new(string       name = "jtag_dtm_reg_bypass",
               int unsigned n_bits = 32,
               int          has_coverage = UVM_NO_COVERAGE);
    super.new(name, n_bits, has_coverage);
  endfunction : new

  virtual function void build(csr_excl_item csr_excl = null);
    // create fields
    bypass = (dv_base_reg_field::type_id::create("bypass"));
    bypass.configure(
      .parent(this),
      .size(1),
      .lsb_pos(0),
      .access("RO"),
      .mubi_access("NONE"),
      .volatile(0),
      .reset(32'h0),
      .has_reset(1),
      .is_rand(1),
      .individually_accessible(0));

    bypass.set_original_access("RO");

  endfunction : build
endclass : jtag_dtm_reg_bypass

class jtag_dtm_reg_idcode extends jtag_dtm_base_reg;
  // fields
  rand dv_base_reg_field rsvd;
  rand dv_base_reg_field manufld;
  rand dv_base_reg_field partnumber;
  rand dv_base_reg_field version;

  `uvm_object_utils(jtag_dtm_reg_idcode)

  function new(string       name = "jtag_dtm_reg_idcode",
               int unsigned n_bits = 32,
               int          has_coverage = UVM_NO_COVERAGE);
    super.new(name, n_bits, has_coverage);
  endfunction : new

  virtual function void build(csr_excl_item csr_excl = null);
    // create fields
    rsvd = (dv_base_reg_field::type_id::create("rsvd"));
    rsvd.configure(
      .parent(this),
      .size(1),
      .lsb_pos(0),
      .access("RO"),
      .mubi_access("NONE"),
      .volatile(0),
      .reset(32'h1),
      .has_reset(1),
      .is_rand(1),
      .individually_accessible(0));

    rsvd.set_original_access("RO");

    // Note: The reset value of manufld must be set based on the design.
    manufld = (dv_base_reg_field::type_id::create("manufld"));
    manufld.configure(
      .parent(this),
      .size(11),
      .lsb_pos(1),
      .access("RO"),
      .mubi_access("NONE"),
      .volatile(0),
      .reset(32'h0),
      .has_reset(1),
      .is_rand(1),
      .individually_accessible(0));

    manufld.set_original_access("RO");

    // Note: The reset value of partnumber must be set based on the design.
    partnumber = (dv_base_reg_field::type_id::create("partnumber"));
    partnumber.configure(
      .parent(this),
      .size(16),
      .lsb_pos(12),
      .access("RO"),
      .mubi_access("NONE"),
      .volatile(0),
      .reset(32'h0),
      .has_reset(1),
      .is_rand(1),
      .individually_accessible(0));

    partnumber.set_original_access("RO");

    // Note: The reset value of version must be set based on the design.
    version = (dv_base_reg_field::type_id::create("version"));
    version.configure(
      .parent(this),
      .size(4),
      .lsb_pos(28),
      .access("RO"),
      .mubi_access("NONE"),
      .volatile(0),
      .reset(32'h0),
      .has_reset(1),
      .is_rand(1),
      .individually_accessible(0));

    version.set_original_access("RO");

  endfunction : build
endclass : jtag_dtm_reg_idcode

class jtag_dtm_reg_dtmcs extends jtag_dtm_base_reg;
  // fields
  rand dv_base_reg_field version;
  rand dv_base_reg_field abits;
  rand dv_base_reg_field dmistat;
  rand dv_base_reg_field idle;
  rand dv_base_reg_field zero0;
  rand dv_base_reg_field dmireset;
  rand dv_base_reg_field dmihardreset;
  rand dv_base_reg_field zero1;

  `uvm_object_utils(jtag_dtm_reg_dtmcs)

  function new(string       name = "jtag_dtm_reg_dtmcs",
               int unsigned n_bits = 32,
               int          has_coverage = UVM_NO_COVERAGE);
    super.new(name, n_bits, has_coverage);
  endfunction : new

  virtual function void build(csr_excl_item csr_excl = null);
    // create fields
    version = (dv_base_reg_field::type_id::create("version"));
    version.configure(
      .parent(this),
      .size(4),
      .lsb_pos(0),
      .access("RO"),
      .mubi_access("NONE"),
      .volatile(0),
      .reset(32'h1),
      .has_reset(1),
      .is_rand(1),
      .individually_accessible(0));

    version.set_original_access("RO");

    // Note: The reset value of abits must be set based on the design.
    abits = (dv_base_reg_field::type_id::create("abits"));
    abits.configure(
      .parent(this),
      .size(6),
      .lsb_pos(4),
      .access("RO"),
      .mubi_access("NONE"),
      .volatile(0),
`ifdef USE_DMI_INTERFACE
      .reset(32'h10),
`else
      .reset(32'h07),
`endif
      .has_reset(1),
      .is_rand(1),
      .individually_accessible(0));

    abits.set_original_access("RO");

    dmistat = (dv_base_reg_field::type_id::create("dmistat"));
    dmistat.configure(
      .parent(this),
      .size(2),
      .lsb_pos(10),
      .access("RO"),
      .mubi_access("NONE"),
      .volatile(0),
      .reset(32'h0),
      .has_reset(1),
      .is_rand(1),
      .individually_accessible(0));

    dmistat.set_original_access("RO");

    idle = (dv_base_reg_field::type_id::create("idle"));
    idle.configure(
      .parent(this),
      .size(3),
      .lsb_pos(12),
      .access("RO"),
      .mubi_access("NONE"),
      .volatile(0),
      .reset(32'h1),
      .has_reset(1),
      .is_rand(1),
      .individually_accessible(0));

    idle.set_original_access("RO");

    zero0 = (dv_base_reg_field::type_id::create("zero0"));
    zero0.configure(
      .parent(this),
      .size(1),
      .lsb_pos(15),
      .access("RO"),
      .mubi_access("NONE"),
      .volatile(0),
      .reset(32'h0),
      .has_reset(1),
      .is_rand(1),
      .individually_accessible(0));

    zero0.set_original_access("RO");

    dmireset = (dv_base_reg_field::type_id::create("dmireset"));
    dmireset.configure(
      .parent(this),
      .size(1),
      .lsb_pos(16),
      .access("W1C"),
      .mubi_access("NONE"),
      .volatile(0),
      .reset(32'h0),
      .has_reset(1),
      .is_rand(1),
      .individually_accessible(0));

    dmireset.set_original_access("W1C");

    dmihardreset = (dv_base_reg_field::type_id::create("dmihardreset"));
    dmihardreset.configure(
      .parent(this),
      .size(1),
      .lsb_pos(17),
      .access("W1C"),
      .mubi_access("NONE"),
      .volatile(0),
      .reset(32'h0),
      .has_reset(1),
      .is_rand(1),
      .individually_accessible(0));

    dmihardreset.set_original_access("W1C");
    // Writing 1 to this field will clear the dmi register, causing read-check mismatches.
    csr_excl.add_excl(dmihardreset.get_full_name(), CsrExclWrite, CsrNonInitTests);

    zero1 = (dv_base_reg_field::type_id::create("zero1"));
    zero1.configure(
      .parent(this),
      .size(14),
      .lsb_pos(18),
      .access("RO"),
      .mubi_access("NONE"),
      .volatile(0),
      .reset(32'h0),
      .has_reset(1),
      .is_rand(0),
      .individually_accessible(0));

    zero1.set_original_access("RO");

  endfunction : build
endclass : jtag_dtm_reg_dtmcs

class jtag_dtm_reg_dmi extends jtag_dtm_base_reg;
  // fields
  rand dv_base_reg_field op;
  rand dv_base_reg_field data;
  rand dv_base_reg_field address;

  `uvm_object_utils(jtag_dtm_reg_dmi)

  function new(string       name = "jtag_dtm_reg_dmi",
`ifdef USE_DMI_INTERFACE
               int unsigned n_bits = 50,
`else
               int unsigned n_bits = 41,
`endif
               int          has_coverage = UVM_NO_COVERAGE);
    super.new(name, n_bits, has_coverage);
  endfunction : new

  virtual function void build(csr_excl_item csr_excl = null);
    // create fields
    op = (dv_base_reg_field::type_id::create("op"));
    op.configure(
      .parent(this),
      .size(2),
      .lsb_pos(0),
      .access("RW"),
      .mubi_access("NONE"),
      .volatile(1),
      .reset(32'h0),
      .has_reset(1),
      .is_rand(1),
      .individually_accessible(0));

    op.set_original_access("RW");

    data = (dv_base_reg_field::type_id::create("data"));
    data.configure(
      .parent(this),
      .size(32),
      .lsb_pos(2),
      .access("RW"),
      .mubi_access("NONE"),
      .volatile(0),
      .reset(32'h0),
      .has_reset(1),
      .is_rand(1),
      .individually_accessible(0));

    data.set_original_access("RW");

    address = (dv_base_reg_field::type_id::create("address"));
    address.configure(
      .parent(this),
`ifdef USE_DMI_INTERFACE
      .size(16 /* Same as abits. */),
`else
      .size(7 /* Same as abits. */),
`endif
      .lsb_pos(34),
      .access("RW"),
      .mubi_access("NONE"),
      .volatile(0),
      .reset(32'h0),
      .has_reset(1),
      .is_rand(1),
      .individually_accessible(0));

    address.set_original_access("RW");

  endfunction : build

  // On reads, we do not want to write the op field.
  virtual function uvm_reg_data_t get_wdata_for_read();
    return get_csr_val_with_updated_field(op, get_mirrored_value(), 0);
  endfunction
endclass : jtag_dtm_reg_dmi

class jtag_dtm_reg_block extends dv_base_reg_block;
  // registers
  rand jtag_dtm_reg_bypass    bypass0;
  rand jtag_dtm_reg_idcode    idcode;
  rand jtag_dtm_reg_dtmcs     dtmcs;
  rand jtag_dtm_reg_dmi       dmi;
  rand jtag_dtm_reg_bypass    bypass1;

  `uvm_object_utils(jtag_dtm_reg_block)

  function new(string name = "jtag_dtm_reg_block",
               int    has_coverage = UVM_NO_COVERAGE);
    super.new(name, has_coverage);
  endfunction : new

  virtual function void build(uvm_reg_addr_t base_addr,
                              csr_excl_item csr_excl = null);
    // create default map
    this.default_map = create_map(.name("default_map"),
                                  .base_addr(base_addr),
                                  .n_bytes(JTAG_DRW / 8),
                                  .endian(UVM_LITTLE_ENDIAN),
                                  .byte_addressing(0));
    if (csr_excl == null) begin
      csr_excl = csr_excl_item::type_id::create("csr_excl");
      this.csr_excl = csr_excl;
    end
    // create registers
    bypass0 = (jtag_dtm_reg_bypass::
                  type_id::create("bypass0"));
    bypass0.configure(.blk_parent(this));
    bypass0.build(csr_excl);
    default_map.add_reg(.rg(bypass0),
                        .offset(32'h0));

    idcode = (jtag_dtm_reg_idcode::
                  type_id::create("idcode"));
    idcode.configure(.blk_parent(this));
    idcode.build(csr_excl);
    default_map.add_reg(.rg(idcode),
                        .offset(32'h1));

    dtmcs = (jtag_dtm_reg_dtmcs::
                  type_id::create("dtmcs"));
    dtmcs.configure(.blk_parent(this));
    dtmcs.build(csr_excl);
    default_map.add_reg(.rg(dtmcs),
                        .offset(32'h10));

    dmi = (jtag_dtm_reg_dmi::
                  type_id::create("dmi"));
    dmi.configure(.blk_parent(this));
    dmi.build(csr_excl);
    default_map.add_reg(.rg(dmi),
                        .offset(32'h11));

    // Disable automated CSR tests based on the dmi register. This acts as a window into a different
    // bus and we don't guarantee "standard register behaviour" for any of its fields.
    csr_excl.add_excl(dmi.get_full_name(), CsrExclAll, CsrAllTests);

    bypass1 = (jtag_dtm_reg_bypass::
                  type_id::create("bypass1"));
    bypass1.configure(.blk_parent(this));
    bypass1.build(csr_excl);
    default_map.add_reg(.rg(bypass1),
                        .offset(32'h1f));

  endfunction : build
endclass : jtag_dtm_reg_block
