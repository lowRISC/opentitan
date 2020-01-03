class riscv_vector_instr extends riscv_instr;

  // TODO : Add vector instruction operands here

  `uvm_object_utils(riscv_vector_instr)

  function new(string name = "");
    super.new(name);
  endfunction

  virtual function string get_instr_name();
    // TODO : Implement this function for vector instructions
  endfunction

  // Convert the instruction to assembly code
  virtual function string convert2asm(string prefix = "");
    string asm_str;
    asm_str = format_string(get_instr_name(), MAX_INSTR_STR_LEN);
    // TODO : Implement this function for vector instructions
    if(comment != "")
      asm_str = {asm_str, " #",comment};
    return asm_str.tolower();
  endfunction

endclass
