// This test is only used to debug covergroup implementation

class riscv_instr_cov_debug_test extends uvm_test;

  riscv_instr_gen_config    cfg;
  riscv_instr_cover_group   instr_cg;
  riscv_instr_cov_item      instr;
  int unsigned              num_of_iterations = 10000;

  `uvm_component_utils(riscv_instr_cov_debug_test)
  `uvm_component_new

  task run_phase(uvm_phase phase);
    bit [XLEN-1:0] rand_val;
    void'($value$plusargs("num_of_iterations=%0d", num_of_iterations));
    cfg = riscv_instr_gen_config::type_id::create("cfg");
    instr = riscv_instr_cov_item::type_id::create("instr");
    instr_cg = new(cfg);
    repeat(20000) begin
      void'(instr.randomize() with {group == RV32I;
                                    csr inside {implemented_csr};});
      `uvm_info(`gfn, instr.convert2asm(), UVM_LOW)
      instr.pre_sample();
      instr_cg.sample(instr);
    end
    `uvm_info("", "TEST PASSED", UVM_NONE);
  endtask

endclass
