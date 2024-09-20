// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence force the alert accumulation count to large value, then check if the accum count
// will saturate and won't overflow.

`define CLASS_CNT_PATH(class_i, i) \
    string class_``class_i``_path_0 = \
           "tb.dut.gen_classes[``i``].u_accu.u_prim_count.cnt_q[0]"; \
    string class_``class_i``_path_1 = \
           "tb.dut.gen_classes[``i``].u_accu.u_prim_count.cnt_q[1]";

`define CHECK_ALERT_ACCUM_CNT(class_i, i) \
    csr_rd_check(.ptr(ral.class``class_i``_accum_cnt), \
                 .compare_value(saturated_class == ``i`` ? \
                  MAX_ACCUM_CNT : MAX_ACCUM_CNT - num_alerts_to_saturate));

class alert_handler_alert_accum_saturation_vseq extends alert_handler_smoke_vseq;
  `uvm_object_utils(alert_handler_alert_accum_saturation_vseq)

  `uvm_object_new

  parameter uint MAX_ACCUM_CNT = 'hffff;
  rand int num_alerts_to_saturate;
  rand bit [1:0] saturated_class; // only 4 classes: a, b, c, d

  `CLASS_CNT_PATH(a, 0)
  `CLASS_CNT_PATH(b, 1)
  `CLASS_CNT_PATH(c, 2)
  `CLASS_CNT_PATH(d, 3)

  constraint num_alerts_to_saturate_c {
    num_alerts_to_saturate inside {[1 : 10]};
    $countones(alert_trigger) == 1;
  }

  function void pre_randomize();
    this.enable_one_alert_c.constraint_mode(0);
    this.enable_classa_only_c.constraint_mode(0);
  endfunction

  virtual task pre_start();
    // Force accum counts to a large value.
    `DV_CHECK(uvm_hdl_force(class_a_path_0, (MAX_ACCUM_CNT - num_alerts_to_saturate)));
    `DV_CHECK(uvm_hdl_force(class_a_path_1, (num_alerts_to_saturate)));

    `DV_CHECK(uvm_hdl_force(class_b_path_0, (MAX_ACCUM_CNT - num_alerts_to_saturate)));
    `DV_CHECK(uvm_hdl_force(class_b_path_1, (num_alerts_to_saturate)));

    `DV_CHECK(uvm_hdl_force(class_c_path_0, (MAX_ACCUM_CNT - num_alerts_to_saturate)));
    `DV_CHECK(uvm_hdl_force(class_c_path_1, (num_alerts_to_saturate)));

    `DV_CHECK(uvm_hdl_force(class_d_path_0, (MAX_ACCUM_CNT - num_alerts_to_saturate)));
    `DV_CHECK(uvm_hdl_force(class_d_path_1, (num_alerts_to_saturate)));

    super.pre_start();
  endtask

  virtual task body();
    // Assign all alerts to one class.
    foreach (alert_class_map[i]) alert_class_map[i] = saturated_class;
    alert_handler_init(.intr_en('1),
                       .alert_en('1),
                       .alert_class(alert_class_map),
                       .loc_alert_en(0),
                       .loc_alert_class(0));
    csr_wr(ral.classa_accum_thresh_shadowed, '1);
    csr_wr(ral.classb_accum_thresh_shadowed, '1);
    csr_wr(ral.classc_accum_thresh_shadowed, '1);
    csr_wr(ral.classd_accum_thresh_shadowed, '1);

    // Enable and lock all alert classes.
    csr_wr(ral.classa_ctrl_shadowed.en, 1);
    csr_wr(ral.classb_ctrl_shadowed.en, 1);
    csr_wr(ral.classc_ctrl_shadowed.en, 1);
    csr_wr(ral.classd_ctrl_shadowed.en, 1);

    `DV_CHECK(uvm_hdl_release(class_a_path_0));
    `DV_CHECK(uvm_hdl_release(class_a_path_1));
    `DV_CHECK(uvm_hdl_release(class_b_path_0));
    `DV_CHECK(uvm_hdl_release(class_b_path_1));
    `DV_CHECK(uvm_hdl_release(class_c_path_0));
    `DV_CHECK(uvm_hdl_release(class_c_path_1));
    `DV_CHECK(uvm_hdl_release(class_d_path_0));
    `DV_CHECK(uvm_hdl_release(class_d_path_1));

    `uvm_info(`gfn, $sformatf("Saturate class %0d, alerts to saturate %0d", saturated_class,
                              num_alerts_to_saturate), UVM_LOW)

    // First round will reach the max count value, afterwards check if the max value saturates and
    // won't overflow.
    repeat ($urandom_range(2, 5)) begin
      repeat (num_alerts_to_saturate) begin
        `DV_CHECK_MEMBER_RANDOMIZE_FATAL(alert_trigger)
        drive_alert(alert_trigger, alert_int_err);
        csr_rd_check(.ptr(ral.intr_state), .compare_value(1 << saturated_class));
        csr_wr(.ptr(ral.intr_state), .value(1 << saturated_class));
      end

      `CHECK_ALERT_ACCUM_CNT(a, 0)
      `CHECK_ALERT_ACCUM_CNT(b, 1)
      `CHECK_ALERT_ACCUM_CNT(c, 2)
      `CHECK_ALERT_ACCUM_CNT(d, 3)
    end
 endtask

endclass : alert_handler_alert_accum_saturation_vseq
