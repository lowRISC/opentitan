// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This injects arbitration faults in any of 4 arbiters with either copy grounded.
// The scrambler arbiters use prim_arbiter_tree, but the host arbiters in flash_phy_core
// use prim_arbiter_fixed, which has different assertions. For the scrambler arbiters we
// also need to disable some assertions that are violated by fault injection.
//
// Notice the $asserton/off directives need to get a string literal, which explains
// why they are done in a case statement.

class flash_ctrl_phy_arb_redun_vseq extends flash_ctrl_err_base_vseq;
  `uvm_object_utils(flash_ctrl_phy_arb_redun_vseq)
  `uvm_object_new

  localparam int NumArbiters = 4;

  rand int unsigned which_arbiter;
  constraint which_arbiter_c { which_arbiter < NumArbiters; }

  rand bit which_copy;

  constraint ctrl_num_c {
    ctrl_num dist { CtrlTransMin := 2, [2:16] :/ 1};
  }

  typedef struct {
    string name;
    string copy_0_req;
    string copy_1_req;
  } arb_t;

`define HOST_ARB_0_PREFIX tb.dut.u_eflash.gen_flash_cores[0].u_core.u_host_arb
`define HOST_ARB_1_PREFIX tb.dut.u_eflash.gen_flash_cores[1].u_core.u_host_arb
`define CALC_ARB_PREFIX tb.dut.u_eflash.u_scramble.u_prim_arbiter_tree_calc
`define OP_ARB_PREFIX tb.dut.u_eflash.u_scramble.u_prim_arbiter_tree_op

`define COPY_0 gen_input_bufs[0]
`define COPY_1 gen_input_bufs[1]
`define REQ_SUFFIX u_req_buf.out_o[1:0]
`define FIXED_SVA_STAY_HIGH_SUFFIX gen_fixed_arbiter.u_arb.ReqStaysHighUntilGranted0_M
`define RR_SVA_STAY_HIGH_SUFFIX gen_rr_arbiter.u_arb.ReqStaysHighUntilGranted0_M
`define RR_SVA_LOCK_ARB_DEC_SUFFIX gen_rr_arbiter.u_arb.LockArbDecision_A

`define HIER_PATH(prefix, copy, suffix) `"prefix.copy.suffix`"

  arb_t arbs[NumArbiters] = {
    '{
      name: "host_arb[0]",
      copy_0_req: `HIER_PATH(`HOST_ARB_0_PREFIX, `COPY_0, `REQ_SUFFIX),
      copy_1_req: `HIER_PATH(`HOST_ARB_0_PREFIX, `COPY_1, `REQ_SUFFIX)
    },
    '{
      name: "host_arb[1]",
      copy_0_req: `HIER_PATH(`HOST_ARB_1_PREFIX, `COPY_0, `REQ_SUFFIX),
      copy_1_req: `HIER_PATH(`HOST_ARB_1_PREFIX, `COPY_1, `REQ_SUFFIX)
    },
    '{
      name: "scrambler_calc",
      copy_0_req: `HIER_PATH(`CALC_ARB_PREFIX, `COPY_0, `REQ_SUFFIX),
      copy_1_req: `HIER_PATH(`CALC_ARB_PREFIX, `COPY_1, `REQ_SUFFIX)
    },
    '{
      name: "scrambler_op",
      copy_0_req: `HIER_PATH(`OP_ARB_PREFIX, `COPY_0, `REQ_SUFFIX),
      copy_1_req: `HIER_PATH(`OP_ARB_PREFIX, `COPY_1, `REQ_SUFFIX)
    }
  };

  task run_error_event();
    int delay;
    arb_t arb;
    logic [1:0] req_0 = which_copy == 1'b0 ? 2'h0 : 2'h3;
    logic [1:0] req_1 = which_copy == 1'b0 ? 2'h3 : 2'h0;
    // unit 100 ns;
    delay = $urandom_range(1, 10);
    #(delay * 100ns);
    cfg.otf_scb_h.comp_off = 1;
    cfg.otf_scb_h.mem_mon_off = 1;
    cfg.scb_h.expected_alert["fatal_err"].expected = 1;
    cfg.scb_h.expected_alert["fatal_err"].max_delay = cfg.seq_cfg.long_fatal_err_delay;
    cfg.scb_h.exp_alert_contd["fatal_err"] = 10000;

    arb = arbs[which_arbiter];
    `uvm_info(`gfn, $sformatf(
              "Faulting arbiter %0d %s: %s=%x and %s=%x",
              which_arbiter, arb.name, arb.copy_0_req, req_0, arb.copy_1_req, req_1),
              UVM_MEDIUM)
    case (which_arbiter)
      // The host arbiters assertions (arbiters 0 and 1) are not impacted.
      0: begin
      end
      1: begin
      end
      2: begin
        $assertoff(0, `HIER_PATH(`CALC_ARB_PREFIX, `COPY_0, `RR_SVA_STAY_HIGH_SUFFIX));
        $assertoff(0, `HIER_PATH(`CALC_ARB_PREFIX, `COPY_0, `RR_SVA_LOCK_ARB_DEC_SUFFIX));
        $assertoff(0, `HIER_PATH(`CALC_ARB_PREFIX, `COPY_1, `RR_SVA_STAY_HIGH_SUFFIX));
        $assertoff(0, `HIER_PATH(`CALC_ARB_PREFIX, `COPY_1, `RR_SVA_LOCK_ARB_DEC_SUFFIX));
      end
      3: begin
        $assertoff(0, `HIER_PATH(`OP_ARB_PREFIX, `COPY_0, `RR_SVA_STAY_HIGH_SUFFIX));
        $assertoff(0, `HIER_PATH(`OP_ARB_PREFIX, `COPY_0, `RR_SVA_LOCK_ARB_DEC_SUFFIX));
        $assertoff(0, `HIER_PATH(`OP_ARB_PREFIX, `COPY_1, `RR_SVA_STAY_HIGH_SUFFIX));
        $assertoff(0, `HIER_PATH(`OP_ARB_PREFIX, `COPY_1, `RR_SVA_LOCK_ARB_DEC_SUFFIX));
      end
      default:
        `uvm_error(`gfn, $sformatf("Illegal arbiter index %0d, expected 0..3", which_arbiter))
    endcase
    // Wait a couple cycles to have any prior SVA attempts complete, and they all last at
    // most two cycles.
    cfg.clk_rst_vif.wait_clks(2);

    `DV_CHECK(uvm_hdl_force(arb.copy_0_req, req_0))
    `DV_CHECK(uvm_hdl_force(arb.copy_1_req, req_1))
    cfg.clk_rst_vif.wait_clks($urandom_range(60, 90));
    `DV_CHECK(uvm_hdl_release(arb.copy_0_req))
    `DV_CHECK(uvm_hdl_release(arb.copy_1_req))
    // Wait a cycle to start attempts once the state should straighten up.
    cfg.clk_rst_vif.wait_clks(1);
    case (which_arbiter)
      // The host arbiters assertions (arbiters 0 and 1) are not impacted.
      0: begin
      end
      1: begin
      end
      2: begin
        $asserton(0, `HIER_PATH(`CALC_ARB_PREFIX, `COPY_0, `FIXED_SVA_STAY_HIGH_SUFFIX));
        $asserton(0, `HIER_PATH(`CALC_ARB_PREFIX, `COPY_0, `RR_SVA_LOCK_ARB_DEC_SUFFIX));
        $asserton(0, `HIER_PATH(`CALC_ARB_PREFIX, `COPY_1, `FIXED_SVA_STAY_HIGH_SUFFIX));
        $asserton(0, `HIER_PATH(`CALC_ARB_PREFIX, `COPY_1, `RR_SVA_LOCK_ARB_DEC_SUFFIX));
      end
      3: begin
        $asserton(0, `HIER_PATH(`OP_ARB_PREFIX, `COPY_0, `FIXED_SVA_STAY_HIGH_SUFFIX));
        $asserton(0, `HIER_PATH(`OP_ARB_PREFIX, `COPY_0, `RR_SVA_LOCK_ARB_DEC_SUFFIX));
        $asserton(0, `HIER_PATH(`OP_ARB_PREFIX, `COPY_1, `FIXED_SVA_STAY_HIGH_SUFFIX));
        $asserton(0, `HIER_PATH(`OP_ARB_PREFIX, `COPY_1, `RR_SVA_LOCK_ARB_DEC_SUFFIX));
      end
      default:
        `uvm_error(`gfn, $sformatf("Illegal arbiter index %0d, expected 0..3", which_arbiter))
    endcase

    `uvm_info(`gfn, "Calling check_fault", UVM_MEDIUM)
    check_fault(ral.fault_status.arb_err);
    `uvm_info(`gfn, "Calling collect_err_cov_status", UVM_MEDIUM)
    collect_err_cov_status(ral.fault_status);
    // host transaction unpredictably triggers err_code.mp_err.
    // Instead of checking err_code == 0, make sure hw_fault.mp_err doesn't happen.
    delay = $urandom_range(60, 90);
    #(delay * 10us);
    csr_rd_check(.ptr(ral.fault_status.mp_err), .compare_value(0));
    drain_n_finish_err_event();
  endtask
  task clean_up();
    init_controller();
  endtask // clean_up

`undef HOST_ARB_0_PREFIX
`undef HOST_ARB_1_PREFIX
`undef CALC_ARB_PREFIX
`undef OP_ARB_PREFIX

`undef COPY_0
`undef COPY_1
`undef REQ_SUFFIX
`undef FIXED_SVA_STAY_HIGH_SUFFIX
`undef RR_SVA_STAY_HIGH_SUFFIX
`undef RR_SVA_LOCK_ARB_DEC_SUFFIX

`undef HIER_PATH
endclass
