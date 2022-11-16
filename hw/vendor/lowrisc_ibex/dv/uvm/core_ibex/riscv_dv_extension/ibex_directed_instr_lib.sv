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
