// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_sensor_ctrl_status_intr_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_sensor_ctrl_status_intr_vseq)

  `uvm_object_new

  localparam int TOTAL_IO = 2;
  `ifdef GATE_LEVEL
    localparam string VIOA_POK_PATH = "`AST_TOP.ast_pwst_o_io_pok_0_";
    localparam string VIOB_POK_PATH = "`AST_TOP.ast_pwst_o_io_pok_1_";
  `else
    localparam string VIOA_POK_PATH = "tb.dut.u_ast.ast_pwst_o.io_pok[0]";
    localparam string VIOB_POK_PATH = "tb.dut.u_ast.ast_pwst_o.io_pok[1]";
  `endif

  localparam string SLEEPING_PATH = "tb.dut.top_earlgrey.u_rv_core_ibex.u_core_sleeping_buf.out_o";
  string io_paths[2] = '{VIOA_POK_PATH, VIOB_POK_PATH};
  int iterations = 10;

  task check_hdl_paths();
    int retval;

    foreach (io_paths[i]) begin
      `DV_CHECK_FATAL(uvm_hdl_check_path(io_paths[i]),
                      $sformatf("Hierarchical path %0s appears to be invalid.", io_paths[i]))
    end
  endtask // check_hdl_paths

  task change_io_val();
    bit [TOTAL_IO-1:0] cur_val;
    bit test_idx;

    foreach (cur_val[i]) begin
      `DV_CHECK_FATAL(uvm_hdl_read(io_paths[i], cur_val[i]));
    end

    test_idx = $urandom_range(0, TOTAL_IO-1);
    `uvm_info(`gfn, $sformatf("Forcing IO %d to a different value", test_idx), UVM_HIGH)
    `DV_CHECK_FATAL(uvm_hdl_force(io_paths[test_idx], ~cur_val[test_idx]));

  endtask

   virtual task wait_for_sleeping();
     bit sleeping = 0;
     `DV_SPINWAIT(
      while (sleeping == 0) begin
        `DV_CHECK_FATAL(uvm_hdl_read(SLEEPING_PATH, sleeping));
        cfg.clk_rst_vif.wait_clks(10);
        `uvm_info(`gfn, $sformatf("Cpu sleeping status: 0x%h", sleeping), UVM_HIGH)
      end
     )
   endtask


  // Force AST change to observe behavior
  virtual task body();
    bit cpu_sleeping;

    super.body();

    // Randomize the number of iterations once SV has a way of passing random
    // seeds over to C side without using backdoor load
    //`DV_CHECK_RANDOMIZE_WITH_FATAL(iterations, iterations <= 10)
    check_hdl_paths();
    for (int i = 0; i < iterations; i++) begin
      `uvm_info(`gfn, $sformatf("Iteration %d start", i), UVM_MEDIUM)
      `DV_WAIT(cfg.sw_logger_vif.printed_log == "Waiting for IO change")
      wait_for_sleeping();
      change_io_val();
      `uvm_info(`gfn, $sformatf("Iteration %d end", i), UVM_MEDIUM)
      `DV_WAIT(cfg.sw_logger_vif.printed_log == "IO change complete")
    end
  endtask

endclass : chip_sw_sensor_ctrl_status_intr_vseq
