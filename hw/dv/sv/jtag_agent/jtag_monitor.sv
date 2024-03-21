// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`define MON_CB cfg.vif.mon_mp.mon_cb
class jtag_monitor extends dv_base_monitor #(
  .ITEM_T(jtag_item),
  .CFG_T (jtag_agent_cfg),
  .COV_T (jtag_agent_cov)
);
  `uvm_component_utils(jtag_monitor)

  // the base class provides the following handles for use:
  // jtag_agent_cfg: cfg
  // jtag_agent_cov: cov
  // uvm_analysis_port #(jtag_item): analysis_port

  `uvm_component_new

  task run_phase(uvm_phase phase);
    fork
      super.run_phase(phase);
      monitor_reset();
    join
  endtask

  // collect transactions forever - already forked in dv_base_monitor::run_phase
  virtual protected task collect_trans(uvm_phase phase);
    jtag_fsm_state_e   jtag_state;
    jtag_item          item;
    int                counter;
    bit [JTAG_IRW-1:0] ir;
    bit [JTAG_DRW-1:0] dr, dout;

    forever begin
      @(`MON_CB);
      if(!cfg.vif.tck_en) continue;
      if (!cfg.vif.trst_n) begin
        jtag_state = JtagResetState;
        wait(cfg.vif.trst_n == 1);
        continue;
      end

      `uvm_info(`gfn, $sformatf("state = %0s, ir = 0x%0h, dr = 0x%0h dout = 0x%0h counter = %0d",
                                jtag_state.name, ir, dr, dout, counter), UVM_DEBUG)
      case (jtag_state)
        JtagResetState: begin
          if (!`MON_CB.tms) jtag_state = JtagIdleState;
        end
        JtagIdleState: begin
          if (`MON_CB.tms) jtag_state = JtagSelectDrState;
        end
        JtagSelectDrState: begin
          jtag_state = `MON_CB.tms ? JtagSelectIrState : JtagCaptureDrState;
        end

        // Select DR
        JtagCaptureDrState: begin
          jtag_state = `MON_CB.tms ? JtagExit1DrState : JtagShiftDrState;
          if (jtag_state == JtagShiftDrState) begin
            dr      = 0;
            dout    = 0;
            counter = 0;
          end
        end
        JtagShiftDrState: begin
          jtag_state = `MON_CB.tms ? JtagExit1DrState : JtagShiftDrState;
          dr[counter] = `MON_CB.tdi;
          dout[counter] = `MON_CB.tdo;
          counter++;
        end
        JtagExit1DrState: begin
          jtag_state = `MON_CB.tms ? JtagUpdateDrState : JtagPauseDrState;
        end
        JtagPauseDrState: begin
          jtag_state = `MON_CB.tms ? JtagExit2DrState : JtagPauseDrState;
        end
        JtagExit2DrState: begin
          jtag_state = `MON_CB.tms ? JtagUpdateDrState : JtagShiftDrState;
        end
        JtagUpdateDrState: begin
          jtag_state = `MON_CB.tms ? JtagSelectDrState : JtagIdleState;

          // Send DR packet to analysis port
          if (cfg.vif.trst_n) begin
            item        = jtag_item::type_id::create("item");
            item.ir_len = 0;
            item.dr_len = counter;
            item.dr     = dr;
            item.dout   = dout;
            analysis_port.write(item);
            `uvm_info(`gfn, item.sprint(uvm_default_line_printer), UVM_MEDIUM)
          end
        end

        // Select IR
        JtagSelectIrState: begin
          jtag_state = `MON_CB.tms ? JtagResetState : JtagCaptureIrState;
        end
        JtagCaptureIrState: begin
          jtag_state = `MON_CB.tms ? JtagExit1IrState : JtagShiftIrState;
          if (jtag_state == JtagShiftIrState) begin
            ir      = 0;
            counter = 0;
          end
        end
        JtagShiftIrState: begin
          jtag_state  = `MON_CB.tms ? JtagExit1IrState : JtagShiftIrState;
          ir[counter] = `MON_CB.tdi;
          counter++;
        end
        JtagExit1IrState: begin
          jtag_state = `MON_CB.tms ? JtagUpdateIrState : JtagPauseIrState;
        end
        JtagPauseIrState: begin
          jtag_state = `MON_CB.tms ? JtagExit2IrState : JtagPauseIrState;
        end
        JtagExit2IrState: begin
          jtag_state = `MON_CB.tms ? JtagUpdateIrState : JtagShiftIrState;
        end
        JtagUpdateIrState: begin
          jtag_state = `MON_CB.tms ? JtagSelectDrState : JtagIdleState;

          // Send IR packet to analysis port
          if (cfg.vif.trst_n) begin
            item        = jtag_item::type_id::create("item");
            item.ir_len = counter;
            item.dr_len = 0;
            item.ir     = ir;
            analysis_port.write(item);
            `uvm_info(`gfn, item.sprint(uvm_default_line_printer), UVM_MEDIUM)
          end
        end
        default: `uvm_fatal(`gfn, $sformatf("Does not support jtag state: %0s", jtag_state.name))
      endcase

      // TODO: sample the covergroups
    end
  endtask

  virtual protected task monitor_reset();
    forever begin
      @(cfg.vif.trst_n);
      cfg.in_reset = !cfg.vif.trst_n;
    end
  endtask

endclass
