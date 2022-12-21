// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0


// Define a short riscv-dv directed instruction stream to setup hardware breakpoints
// (TSELECT/TDATA), and then trigger on an instruction at the end of this stream.
class ibex_breakpoint_stream extends riscv_directed_instr_stream;

  riscv_pseudo_instr   la_instr;
  riscv_instr          ebreak_insn;
  rand int unsigned    num_of_instr;

  constraint instr_c {
    num_of_instr inside {[5:10]};
  }

  `uvm_object_utils(ibex_breakpoint_stream)

  function new(string name = "");
    super.new(name);
  endfunction

  function void post_randomize();
    riscv_instr      instr;
    string           trigger_label, gn;

    // Setup a randomized main body of instructions.
    initialize_instr_list(num_of_instr);
    setup_allowed_instr(1, 1); // no_branch=1/no_load_store=1
    foreach(instr_list[i]) begin
      instr = riscv_instr::type_id::create("instr");
      randomize_instr(instr);
      instr_list[i] = instr;
      // Copy this from the base-class behaviour
      instr_list[i].atomic = 1'b1;
      instr_list[i].has_label = 1'b0;
    end

    // Give the last insn of the main body a label, then set the breakpoint address to that label.
    gn = get_name();
    trigger_label = {gn};
    instr_list[$].label = trigger_label;
    instr_list[$].has_label = 1'b1;

    // Load the address of the trigger point as the (last insn of the stream + 4)
    // Store in gpr[1] ()
    la_instr = riscv_pseudo_instr::type_id::create("la_instr");
    la_instr.pseudo_instr_name = LA;
    la_instr.imm_str           = $sformatf("%0s+4", trigger_label);
    la_instr.rd                = cfg.gpr[1];

    // Create the ebreak insn which will cause us to enter debug mode, and run the
    // special code in the debugrom.
    ebreak_insn = riscv_instr::get_instr(EBREAK);

    // Add the instructions into the stream.
    instr_list = {la_instr,
                  ebreak_insn,
                  instr_list};
  endfunction

endclass

// Define a short riscv-dv directed instruction stream to write random values to MSECCFG CSR
class ibex_rand_mseccfg_stream extends riscv_directed_instr_stream;

  `uvm_object_utils(ibex_rand_mseccfg_stream)

  function new(string name = "");
    super.new(name);
  endfunction

  function void post_randomize();
    riscv_instr          csrrw_instr;
    // This stream consists of a single instruction
    initialize_instr_list(1);

    csrrw_instr = riscv_instr::get_instr(CSRRWI);
    csrrw_instr.atomic = 1'b0;
    csrrw_instr.csr = MSECCFG;
    csrrw_instr.rd = '0;
    // Randomize between 3'b000 and 3'b111 to hit every combination of RLB/MMWP/MML bits.
    csrrw_instr.imm_str = $sformatf("0x%0x", $urandom_range(7,0));
    instr_list = {csrrw_instr};
  endfunction

endclass

// Stream to randomly toggle different Ibex specific feature enables in cpuctrlsts
class ibex_rand_cpuctrlsts_stream extends riscv_directed_instr_stream;

  `uvm_object_utils(ibex_rand_cpuctrlsts_stream)

  function new(string name = "");
    super.new(name);
  endfunction

  function void post_randomize();
    riscv_instr instrs[4];
    bit toggle_dit;
    bit toggle_dummy_instr;
    bit toggle_icache;
    bit icache_en;
    bit dit_en;
    bit dummy_instr_en;
    bit [2:0] dummy_instr_mask;
    bit [8:0] cpuctrlsts_mask;
    bit [5:0] cpuctrlsts_val;

    if (cfg.init_privileged_mode != MACHINE_MODE) begin
      // Cannot write to cpuctrlsts when we're doing a U mode test
      return;
    end

    // DIT is Data Independent Timing
    if (!$value$plusargs("toggle_dit", toggle_dit)) begin
      toggle_dit = 1'b0;
    end

    if (!$value$plusargs("toggle_dummy_instr", toggle_dummy_instr)) begin
      toggle_dummy_instr = 1'b0;
    end

    if (!$value$plusargs("toggle_icache", toggle_icache)) begin
      toggle_icache = 1'b0;
    end

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(icache_en, if (!toggle_icache) icache_en == 0;);
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(dit_en, if (!toggle_dit) dit_en == 0;);
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(dummy_instr_en,
      if (!toggle_dummy_instr) dummy_instr_en == 0;);
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(dummy_instr_mask,
      if (!toggle_dummy_instr) dummy_instr_mask == 0;);

    cpuctrlsts_mask = {3'b111, {4{!dummy_instr_en}}, !dit_en, !icache_en};
    cpuctrlsts_val = {dummy_instr_mask, dummy_instr_en, dit_en, icache_en};

    initialize_instr_list(4);

    instrs[0] = riscv_instr::get_instr(CSRRSI);
    instrs[0].atomic = 1'b0;
    instrs[0].csr = 12'h7c0;
    instrs[0].rd = cfg.gpr[0];
    instrs[0].imm_str = "0";

    instrs[1] = riscv_instr::get_instr(ANDI);
    instrs[1].atomic = 1'b0;
    instrs[1].rs1 = cfg.gpr[0];
    instrs[1].rd = cfg.gpr[0];
    instrs[1].imm_str = $sformatf("0x%0x", cpuctrlsts_mask);

    instrs[2] = riscv_instr::get_instr(ORI);
    instrs[2].atomic = 1'b0;
    instrs[2].rs1 = cfg.gpr[0];
    instrs[2].rd = cfg.gpr[0];
    instrs[2].imm_str = $sformatf("0x%0x", cpuctrlsts_val);

    instrs[3] = riscv_instr::get_instr(CSRRW);
    instrs[3].atomic = 1'b0;
    instrs[3].csr = 12'h7c0;
    instrs[3].rd = '0;
    instrs[3].rs1 = cfg.gpr[0];

    instr_list = instrs;
  endfunction

endclass

// Define a short riscv-dv directed instruction stream to set a valid NA4 address/config
class ibex_valid_na4_stream extends riscv_directed_instr_stream;

  `uvm_object_utils(ibex_valid_na4_stream)

  function new(string name = "");
    super.new(name);
  endfunction

  function void post_randomize();
    string               instr_label, gn;
    riscv_pseudo_instr   la_instr;
    riscv_instr          addr_csrrw_instr;
    riscv_instr          srli_instr;
    riscv_instr          nop_instr;
    riscv_instr          cfg_csrrw_instr;

    // Inserted stream will consist of five instructions
    initialize_instr_list(5);

    cfg_csrrw_instr = riscv_instr::get_instr(CSRRSI);
    cfg_csrrw_instr.atomic = 1'b1;
    cfg_csrrw_instr.has_label = 1'b0;
    cfg_csrrw_instr.csr = PMPCFG0;
    cfg_csrrw_instr.rd = '0;
    cfg_csrrw_instr.imm_str = $sformatf("%0d", $urandom_range(16,23));

    // Use a label to use it for setting pmpaddr CSR.
    instr_label = $sformatf("na4_addr_stream_%0x", $urandom());

    nop_instr = riscv_instr::get_instr(NOP);
    nop_instr.label = instr_label;
    nop_instr.has_label = 1'b1;
    nop_instr.atomic = 1'b1;

    // Load the address of the instruction after this whole stream
    la_instr = riscv_pseudo_instr::type_id::create("la_instr");
    la_instr.pseudo_instr_name = LA;
    la_instr.has_label = 1'b0;
    la_instr.atomic = 1'b1;
    la_instr.imm_str           = $sformatf("%0s+16", instr_label);
    la_instr.rd                = cfg.gpr[1];

    srli_instr = riscv_instr::get_instr(SRLI);
    srli_instr.has_label = 1'b0;
    srli_instr.atomic = 1'b1;
    srli_instr.rs1 = cfg.gpr[1];
    srli_instr.rd = cfg.gpr[1];
    srli_instr.imm_str = $sformatf("2");

    addr_csrrw_instr = riscv_instr::get_instr(CSRRW);
    addr_csrrw_instr.has_label = 1'b0;
    addr_csrrw_instr.atomic = 1'b1;
    addr_csrrw_instr.csr = PMPADDR0;
    addr_csrrw_instr.rs1 = cfg.gpr[1];
    addr_csrrw_instr.rd = '0;
    instr_list = {cfg_csrrw_instr, nop_instr, la_instr, srli_instr, addr_csrrw_instr};
  endfunction

endclass

class ibex_cross_pmp_region_mem_access_stream extends riscv_directed_instr_stream;
  `uvm_object_utils(ibex_cross_pmp_region_mem_access_stream)

  int unsigned pmp_region;
  int unsigned region_mask;
  int unsigned region_size;

  function new (string name = "");
    super.new(name);
  endfunction

  function void calc_region_params();
    int unsigned cur_addr = cfg.pmp_cfg.pmp_cfg[pmp_region].addr;

    region_size = 8;
    region_mask = 32'hfffffffe;

    for (int i = 0; i < 29; ++i) begin
      if ((cur_addr & 1) == 0) break;
      region_size *= 2;
      cur_addr >>= 1;
      region_mask <<= 1;
    end
  endfunction

  function int unsigned pmp_region_top_addr();
    return ((cfg.pmp_cfg.pmp_cfg[pmp_region].addr & region_mask) << 2) + region_size;
  endfunction

  function int unsigned pmp_region_bottom_addr();
    return ((cfg.pmp_cfg.pmp_cfg[pmp_region].addr & region_mask) << 2);
  endfunction

  function void post_randomize();
    int unsigned target_addr;
    int unsigned offset;
    riscv_pseudo_instr la_instr;
    riscv_instr mem_instr;
    bit access_at_top;

    if (!std::randomize(pmp_region) with {
          pmp_region > 1;
          pmp_region < cfg.pmp_cfg.pmp_num_regions;
          cfg.pmp_cfg.pmp_cfg[pmp_region].a == NAPOT;
        })
    begin
      `uvm_info(`gfn,
        {"WARNING: Cannot choose random NAPOT PMP region, skipping cross PMP region access ",
         "generation"}, UVM_LOW)
      return;
    end

    initialize_instr_list(2);

    calc_region_params();

    mem_instr = riscv_instr::get_load_store_instr({LH, LHU, LW, SH, SW});

    std::randomize(access_at_top);

    if (mem_instr.instr_name inside {LW, SW}) begin
      std::randomize(offset) with {offset < 3;offset > 0;};
    end else begin
      offset = 1;
    end

    if (access_at_top) begin
      target_addr = pmp_region_top_addr() - offset;
    end else begin
      target_addr = pmp_region_bottom_addr() - offset;
    end

    la_instr = riscv_pseudo_instr::type_id::create("la_instr");
    la_instr.pseudo_instr_name = LA;
    la_instr.has_label = 1'b0;
    la_instr.atomic = 1'b1;
    la_instr.imm_str = $sformatf("0x%x", target_addr);
    la_instr.rd = cfg.gpr[1];

    randomize_gpr(mem_instr);
    mem_instr.has_imm = 0;
    mem_instr.imm_str = "0";
    mem_instr.rs1 = cfg.gpr[1];

    instr_list = {la_instr, mem_instr};

    super.post_randomize();
  endfunction
endclass

class ibex_make_pmp_region_exec_stream extends riscv_directed_instr_stream;
  `uvm_object_utils(ibex_make_pmp_region_exec_stream)

  int unsigned pmp_region;

  function new (string name = "");
    super.new(name);
  endfunction

  function void post_randomize();
    riscv_pseudo_instr li_bit_instr;
    riscv_pseudo_instr li_cfg_instr;
    riscv_instr instrs[7];
    bit [31:0] pmpcfg_bits;
    bit [31:0] pmpcfg_mask;
    bit [3:0] new_cfg;
    int pmpcfg_num;

    if (cfg.init_privileged_mode != MACHINE_MODE) begin
      // Cannot write to pmpcfgX CSRs in U Mode so skip inserting this sequence
      return;
    end

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(pmp_region,
      pmp_region > 1; pmp_region < cfg.pmp_cfg.pmp_num_regions;)

    // Choose a new config which is executable when MML is set
    // 4 config bits are {L, X, W, R}
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(new_cfg, new_cfg inside {4'b0100, 4'b0101, 4'b0111,
      4'b1100, 4'b1010, 4'b1110, 4'b1101};)

    pmpcfg_num = pmp_region / 4;
    pmpcfg_bits = {new_cfg[3], 4'b0, new_cfg[2:0]} << ((pmp_region % 4) * 8);
    pmpcfg_mask = 32'b10000111 << ((pmp_region % 4) * 8);
    pmpcfg_mask = ~pmpcfg_mask;

    initialize_instr_list(7);

    // Read the current PMP config masking out the bits we want to change an AND, adding the bits we
    // want with an OR then write back to the CSR.
    li_bit_instr = riscv_pseudo_instr::type_id::create("li_bit_instr");
    li_bit_instr.pseudo_instr_name = LI;
    li_bit_instr.has_label = 1'b0;
    li_bit_instr.atomic = 1'b1;
    li_bit_instr.imm_str = $sformatf("0x%x", pmpcfg_bits);
    li_bit_instr.rd = cfg.gpr[0];
    instrs[0] = li_bit_instr;

    li_cfg_instr = riscv_pseudo_instr::type_id::create("li_cfg_instr");
    li_cfg_instr.pseudo_instr_name = LI;
    li_cfg_instr.has_label = 1'b0;
    li_cfg_instr.atomic = 1'b1;
    li_cfg_instr.imm_str = $sformatf("0x%x", pmpcfg_mask);
    li_cfg_instr.rd = cfg.gpr[1];
    instrs[1] = li_cfg_instr;

    instrs[2] = riscv_instr::get_instr(CSRRSI);
    instrs[2].atomic = 1'b0;
    instrs[2].csr = PMPCFG0 + pmpcfg_num;
    instrs[2].rd = cfg.gpr[2];
    instrs[2].imm_str = "0";

    instrs[3] = riscv_instr::get_instr(AND);
    instrs[3].atomic = 1'b0;
    instrs[3].rs1 = cfg.gpr[2];
    instrs[3].rs2 = cfg.gpr[1];
    instrs[3].rd = cfg.gpr[2];

    instrs[4] = riscv_instr::get_instr(OR);
    instrs[4].atomic = 1'b0;
    instrs[4].rs1 = cfg.gpr[2];
    instrs[4].rs2 = cfg.gpr[0];
    instrs[4].rd = cfg.gpr[2];

    instrs[5] = riscv_instr::get_instr(CSRRW);
    instrs[5].atomic = 1'b0;
    instrs[5].csr = PMPCFG0 + pmpcfg_num;
    instrs[5].rd = '0;
    instrs[5].rs1 = cfg.gpr[2];

    // Immediately read back what we wrote, to check it has been dealt with correctly (i.e. write
    // suppressed where it should be suppressed), as co-sim currently doesn't check CSR writes.
    instrs[6] = riscv_instr::get_instr(CSRRS);
    instrs[6].atomic = 1'b0;
    instrs[6].csr = PMPCFG0 + pmpcfg_num;
    instrs[6].rd = cfg.gpr[0];
    instrs[6].rs1 = 0;

    instr_list = instrs;

    super.post_randomize();
  endfunction
endclass
