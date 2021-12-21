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

   constraint set_timer_c {
    set_timer dist {
      [10:100] :/ 95,
      [101:$]   :/ 5
    };
   }

   constraint num_trans_c {
     num_trans == 2;
   }

   edge_detect_t edge_detect[NumInputs];

   task monitor_input_edge(sysrst_input_idx_e index, ref edge_detect_t edge_detect, bit[TL_DW-1:0] key_intr_status);
     bit timer_reached;
     bit h2l_detected;
     bit l2h_detected;

     fork
       begin
         fork begin // isolation fork
         forever begin
           cfg.clk_aon_rst_vif.wait_clks(1);
           fork
             if (edge_detect.en_l2h && !edge_detect.l2h_triggered) begin
               @(posedge cfg.vif.sysrst_ctrl_inputs[index]);
               `DV_CHECK_EQ(l2h_detected, 0)
               l2h_detected = 1;
             end
             if (edge_detect.en_h2l && !edge_detect.h2l_triggered) begin
               @(negedge cfg.vif.sysrst_ctrl_inputs[index]);
               `DV_CHECK_EQ(h2l_detected, 0)
               h2l_detected = 1;
             end
           join_any
         disable fork;
         end
         end join
       end

       // after h2l_detected is set, check the input stay low for enought time
       begin
         bit h2l_timer_reached;
         fork begin // isolation fork
         forever begin
          cfg.clk_aon_rst_vif.wait_clks(1);
          if (edge_detect.en_h2l && !edge_detect.h2l_triggered) begin
            wait (h2l_detected);
             fork
               begin
                 cfg.clk_aon_rst_vif.wait_clks(set_timer);
                 h2l_timer_reached = 1;
               end
               begin
                 // if edge change occurs again before the timer reaches the defined value, the interrupt
                 // won't happen
                 @(posedge cfg.vif.sysrst_ctrl_inputs[index]);
               end
             join_any
            disable fork;
          end
         end
         end join
         if (h2l_timer_reached) edge_detect.h2l_triggered = 1;
         h2l_detected = 0;
       end

       begin
         bit l2h_timer_reached;
         fork begin // isolation fork
         forever begin
          cfg.clk_aon_rst_vif.wait_clks(1);
          if (edge_detect.en_l2h && !edge_detect.l2h_triggered) begin
            wait (l2h_detected);
            fork
              begin
               cfg.clk_aon_rst_vif.wait_clks(set_timer);
               l2h_timer_reached = 1;
              end
              begin
                // if edge change occurs again before the timer reaches the defined value, the interrupt
                // won't happen
                @(negedge cfg.vif.sysrst_ctrl_inputs[index]);
              end
           join_any
           disable fork;
          end
         end
         end join
         if (l2h_timer_reached) edge_detect.l2h_triggered = 1;
         l2h_detected = 0;
       end
     join
   endtask

   function void check_edge_intr(sysrst_input_idx_e index, ref edge_detect_t edge_detect,
                              bit[TL_DW-1:0] key_intr_status);
     `DV_CHECK_EQ(key_intr_status[index], edge_detect.h2l_triggered,
                  $sformatf("Compare mismatch at %s", index.name))
     `DV_CHECK_EQ(key_intr_status[NumInputs+index], edge_detect.l2h_triggered,
                  $sformatf("Compare mismatch at %s", index.name))
     edge_detect.h2l_triggered = 0;
     edge_detect.l2h_triggered = 0;
   endfunction

   task body();
     bit exp_intr_state;
     `uvm_info(`gfn, "Starting the body from edge_detect_vseq", UVM_LOW)

     // Select the inputs and their transition
     csr_wr(ral.key_intr_ctl, set_input);

     // Set the key interrupt debounce timer value
     csr_wr(ral.key_intr_debounce_ctl, set_timer);

     // It takes 2-3 clock cycles to sync register values
     cfg.clk_aon_rst_vif.wait_clks(3);

     // start monitor edge
     fork
      for (int i = 0; i < NumInputs; i++) begin
       automatic int local_i = i;
       edge_detect[i].en_h2l = set_input[i];
       edge_detect[i].en_l2h = set_input[NumInputs + i];
       monitor_input_edge(sysrst_input_idx_e'(local_i), edge_detect[local_i], rdata);
      end
     join_none

     for (int j = 0; j < num_trans; j++) begin
       repeat ($urandom_range(1, 2)) begin
         cfg.clk_aon_rst_vif.wait_clks(1);
         cfg.vif.randomize_input();
         cfg.clk_aon_rst_vif.wait_clks($urandom_range(1, set_timer * 2));
         cfg.vif.randomize_input();
       end

       // make sure the previous transition lasts long enough, so that everything is settled and we can check them
       cfg.clk_aon_rst_vif.wait_clks(set_timer);

       csr_rd(ral.key_intr_status, rdata);
       foreach (edge_detect[i]) begin
         check_edge_intr(sysrst_input_idx_e'(i), edge_detect[i], rdata);
       end

       // check intr_status
       if (rdata > 1) exp_intr_state = 1;
       else           exp_intr_state = 0;
       check_interrupts(.interrupts(1), .check_set(exp_intr_state));

       // clear interrupt
       // Write to clear the register
       csr_wr(ral.key_intr_status, rdata);

       cfg.clk_aon_rst_vif.wait_clks(20);
       // Check if the register is cleared
       csr_rd_check(ral.key_intr_status, .compare_value(0));

       cfg.clk_aon_rst_vif.wait_clks(20);
     end
   endtask : body

endclass : sysrst_ctrl_edge_detect_vseq
