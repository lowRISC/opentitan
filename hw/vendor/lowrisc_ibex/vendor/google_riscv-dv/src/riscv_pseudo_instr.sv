// Psuedo instructions are used to simplify assembly program writing
class riscv_pseudo_instr extends riscv_instr;

  rand riscv_pseudo_instr_name_t  pseudo_instr_name;

  `add_pseudo_instr(LI, I_FORMAT, LOAD, RV32I)
  `add_pseudo_instr(LA, I_FORMAT, LOAD, RV32I)

  `uvm_object_utils(riscv_pseudo_instr)

  function new(string name = "");
    super.new(name);
    process_load_store = 0;
    this.format = I_FORMAT;
  endfunction

  // Convert the instruction to assembly code
  virtual function string convert2asm(string prefix = "");
    string asm_str;
    asm_str = format_string(get_instr_name(), MAX_INSTR_STR_LEN);
    // instr rd,imm
    asm_str = $sformatf("%0s%0s, %0s", asm_str, rd.name(), get_imm());
    if(comment != "")
      asm_str = {asm_str, " #",comment};
    return asm_str.tolower();
  endfunction

  virtual function string get_instr_name();
    return pseudo_instr_name.name();
  endfunction

endclass
