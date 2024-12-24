// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence assert errors duing seed-reading process targeting
// some hw oriented fault status errors.
// See 'check_status' tasks for what status errors are covered.
class flash_ctrl_hw_read_seed_err_vseq extends flash_ctrl_err_base_vseq;
  `uvm_object_utils(flash_ctrl_hw_read_seed_err_vseq)
  `uvm_object_new

  task run_main_event();
    cfg.seq_cfg.disable_flash_init = 1;
    cfg.seq_cfg.en_init_keys_seeds = 0;
    apply_reset();
     // Enable ecc for all regions
    init_controller(.non_blocking(1));
  endtask // run_main_event

  // fatal_std_err
  task run_error_event();
    int wait_timeout_ns = 50_000;
    int event_idx = $urandom_range(0, 4);

    `uvm_info(`gfn, $sformatf("event_idx :%0d", event_idx), UVM_MEDIUM)
    `DV_SPINWAIT(wait(cfg.flash_ctrl_vif.hw_rvalid == 1);,
                 , wait_timeout_ns)
    cfg.scb_h.expected_alert["fatal_err"].expected = 1;
    cfg.scb_h.expected_alert["fatal_err"].max_delay = 2000;
    cfg.scb_h.exp_alert_contd["fatal_err"] = 10000;

    add_glitch(event_idx);
    collect_err_cov_status(ral.fault_status);
    check_status(event_idx);
  endtask

  task add_glitch(int idx);
    string path = LIST_OF_READ_SEED_FORCE_PATHS[idx];
    case (idx)
      0, 1: begin
        `DV_CHECK(uvm_hdl_force(path, FlashOpInvalid));
      end
      2: begin
        `DV_CHECK(uvm_hdl_force(path, 0));
      end
      3, 4: begin
         flip_2bits(path);
      end
      default: `uvm_error(`gfn, $sformatf("unsupported index %0d", idx))
    endcase // case (idx)
    cfg.clk_rst_vif.wait_clks(10);
    `DV_CHECK(uvm_hdl_release(path));
  endtask

  task check_status(int idx);
    uvm_object fld;

    case (idx)
      0: begin
        fld = ral.fault_status.op_err;
      end
      1: begin
        fld = ral.fault_status.seed_err;
      end
      2: begin
        fld = ral.fault_status.mp_err;
      end
      3: begin
        fld = ral.fault_status.rd_err;
      end
      4: begin
        fld = ral.fault_status.phy_relbl_err;
      end
      default: `uvm_error(`gfn, $sformatf("unsupported index %0d", idx))
    endcase // case (idx)
    csr_rd_check(.ptr(ral.err_code), .compare_value(0));
    csr_rd_check(.ptr(fld), .compare_value(1));
  endtask // check_status

endclass // flash_ctrl_hw_read_seed_err_vseq
