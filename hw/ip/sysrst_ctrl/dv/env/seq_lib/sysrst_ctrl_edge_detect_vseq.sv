// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence will detect the edge transition on input keys
// and raise an interrupt if the detected edge of signal remains
// stable during the entire debounce period
class sysrst_ctrl_edge_detect_vseq extends sysrst_ctrl_base_vseq;
  `uvm_object_utils(sysrst_ctrl_edge_detect_vseq)

  `uvm_object_new

   rand uvm_reg_data_t set_input;
   rand uint16_t set_timer;
   uvm_reg_data_t rdata;
   rand bit is_core_clk_stop;

   constraint set_timer_c {
    set_timer dist {
      [10:100] :/ 95,
      [101:$]   :/ 5
    };
   }

   constraint num_trans_c {
     num_trans inside {[1:3]};
   }

   edge_detect_h2l_t edge_detect_h2l[NumInputs], edge_detect_h2l_array[NumInputs];
   edge_detect_l2h_t edge_detect_l2h[NumInputs], edge_detect_l2h_array[NumInputs];

   task monitor_input_edge(sysrst_input_idx_e index, ref edge_detect_h2l_t edge_detect_h2l,
                           ref edge_detect_l2h_t edge_detect_l2h);
     bit h2l_timer_reached;
     bit h2l_detected;
     bit l2h_detected;

     fork
       if (edge_detect_l2h.en_l2h)
         forever begin
           @(posedge cfg.vif.sysrst_ctrl_inputs[index]);
             if (!edge_detect_l2h.l2h_triggered) begin
               `DV_CHECK_EQ(l2h_detected, 0)
               l2h_detected = 1;
             end
         end
       if (edge_detect_h2l.en_h2l)
         forever begin
           @(negedge cfg.vif.sysrst_ctrl_inputs[index]);
             if (!edge_detect_h2l.h2l_triggered) begin
               `DV_CHECK_EQ(h2l_detected, 0)
               h2l_detected = 1;
             end
         end

       // after h2l_detected is set, check the input stay low for enought time
       forever begin
         bit h2l_timer_reached;
         wait (h2l_detected && !edge_detect_h2l.h2l_triggered);
         fork
           begin
             cfg.clk_aon_rst_vif.wait_clks(set_timer);
             `uvm_info(`gfn, "H2L timer reached", UVM_NONE)
             h2l_timer_reached = 1;
           end
           begin
             // if edge change occurs again before the timer reaches the defined value, the interrupt
             // won't happen
             @(cfg.vif.sysrst_ctrl_inputs[index]);
           end
         join_any
         disable fork;
         if (h2l_timer_reached) edge_detect_h2l.h2l_triggered = 1;
         h2l_detected = 0;
       end

       forever begin
         bit l2h_timer_reached;
         wait (l2h_detected && !edge_detect_l2h.l2h_triggered);
         fork
           begin
             cfg.clk_aon_rst_vif.wait_clks(set_timer);
             l2h_timer_reached = 1;
           end
           begin
             // if edge change occurs again before the timer reaches the defined value, the interrupt
             // won't happen
             @(cfg.vif.sysrst_ctrl_inputs[index]);
           end
         join_any
         disable fork;
         if (l2h_timer_reached) edge_detect_l2h.l2h_triggered = 1;
         l2h_detected = 0;
       end
     join
   endtask

   function void check_h2l_edge_intr(sysrst_input_idx_e index,
             ref edge_detect_h2l_t edge_detect_h2l, bit[TL_DW-1:0] key_intr_status);
     `DV_CHECK_EQ(key_intr_status[index], edge_detect_h2l.h2l_triggered,
                  $sformatf("Compare mismatch at %s", index.name))
     edge_detect_h2l.h2l_triggered = 0;
   endfunction


   function void check_l2h_edge_intr(sysrst_input_idx_e index,
             ref edge_detect_l2h_t edge_detect_l2h, bit[TL_DW-1:0] key_intr_status);
     `DV_CHECK_EQ(key_intr_status[NumInputs+index], edge_detect_l2h.l2h_triggered,
                  $sformatf("Compare mismatch at %s", index.name))
     edge_detect_l2h.l2h_triggered = 0;
   endfunction

   task body();
     bit exp_intr_state;
     uint16_t get_timer_val;
     uvm_reg_data_t get_input;

     `uvm_info(`gfn, "Starting the body from edge_detect_vseq", UVM_LOW)

     // Select the inputs and their transition
     csr_wr(ral.key_intr_ctl, set_input);

     // Set the key interrupt debounce timer value
     csr_wr(ral.key_intr_debounce_ctl, set_timer);

     // It takes 2-3 clock cycles to sync register values
     cfg.clk_aon_rst_vif.wait_clks(3);

     csr_rd(ral.key_intr_ctl, get_input);

     // start monitor edge
     fork begin  // isolation fork
       for (int i = 0; i < NumInputs; i++) begin
         automatic int local_i = i;
         edge_detect_h2l[i].en_h2l = get_input[i];
         edge_detect_l2h[i].en_l2h = get_input[NumInputs + i + 1];
         fork
           monitor_input_edge(sysrst_input_idx_e'(local_i), edge_detect_h2l[local_i],
                  edge_detect_l2h[local_i]);
         join_none
       end

       csr_rd(ral.key_intr_debounce_ctl, get_timer_val);

       for (int j = 0; j < num_trans; j++) begin
         int wait_cycles;
         `DV_CHECK_MEMBER_RANDOMIZE_FATAL(is_core_clk_stop)
         if (is_core_clk_stop) cfg.clk_rst_vif.stop_clk();
         cfg.clk_aon_rst_vif.wait_clks(1);
         cfg.vif.randomize_input();
         cfg.clk_aon_rst_vif.wait_clks(1);
         `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(wait_cycles,
                                          wait_cycles inside {[1:get_timer_val-2],
                                          [get_timer_val+5:get_timer_val*2]};)
         cfg.clk_aon_rst_vif.wait_clks(wait_cycles);
         cfg.vif.randomize_input();

         // make sure the previous transition lasts long enough, so that everything is settled and we can check them
         cfg.clk_aon_rst_vif.wait_clks(get_timer_val+10);

         // Enable the bus clock to read the status register
         if (is_core_clk_stop) cfg.clk_rst_vif.start_clk();

         cfg.clk_aon_rst_vif.wait_clks(5);

         csr_rd(ral.key_intr_status, rdata);
         foreach (edge_detect_h2l_array[i]) begin
           check_h2l_edge_intr(sysrst_input_idx_e'(i), edge_detect_h2l[i], rdata);
         end

         foreach (edge_detect_l2h_array[i]) begin
           check_l2h_edge_intr(sysrst_input_idx_e'(i), edge_detect_l2h[i], rdata);
         end

         // check intr_status
         if (rdata >= 1) exp_intr_state = 1;
         else            exp_intr_state = 0;
         check_interrupts(.interrupts(1), .check_set(exp_intr_state));

         // clear interrupt
         // Write to clear the register
         csr_wr(ral.key_intr_status, rdata);

         cfg.clk_aon_rst_vif.wait_clks(5);
         // Check if the register is cleared
         csr_rd_check(ral.key_intr_status, .compare_value(0));

         cfg.clk_aon_rst_vif.wait_clks(20);
       end
       disable fork;
      end join
   endtask : body

endclass : sysrst_ctrl_edge_detect_vseq
