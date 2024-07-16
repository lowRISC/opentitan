// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

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

  // Wait for the next posedge of TCK if tck_en is true. If tck_en is false, wait until it becomes
  // true (which gives a sort of "virtual posedge", representing something that happened at some
  // point before).
  //
  // Note that this is slightly different from calling cfg.vif.wait_tck(1) because the behaviour is
  // different when tck_en is false.
  task wait_tck();
    if (cfg.mon_vif != null) begin
      @(cfg.mon_vif.mp.cb);
    end else begin
      if (cfg.vif.tck_en) @(cfg.vif.mon_mp.mon_cb);
      else @(posedge cfg.vif.tck_en);
    end
  endtask

  // Get the TMS signal from the jtag_if that we're monitoring
  function logic read_tms();
    return (cfg.mon_vif == null) ? cfg.vif.mon_mp.mon_cb.tms : cfg.mon_vif.mp.cb.tms;
  endfunction

  // Get the TDI signal from the jtag_if that we're monitoring
  function logic read_tdi();
    return (cfg.mon_vif == null) ? cfg.vif.mon_mp.mon_cb.tdi : cfg.mon_vif.mp.cb.tdi;
  endfunction

  // Get the TDO signal from the jtag_if that we're monitoring
  function logic read_tdo();
    return (cfg.mon_vif == null) ? cfg.vif.mon_mp.mon_cb.tdo : cfg.mon_vif.mp.cb.tdo;
  endfunction

  // collect transactions forever - already forked in dv_base_monitor::run_phase
  virtual protected task collect_trans();
    jtag_fsm_state_e   jtag_state;
    jtag_item          item;
    int                counter;
    bit [JTAG_IRW-1:0] ir;
    bit [JTAG_DRW-1:0] dr, dout;

    forever begin
      // Wait until the next TCK edge, or reset if that happens first.
      fork begin : isolation_fork
        fork
          wait_tck();
          wait(!cfg.vif.trst_n);
        join_any
        disable fork;
      end join

      // If we are in reset then put the FSM state back to the reset state and then wait until we
      // exit reset (and can start looking at TCK again).
      if (!cfg.vif.trst_n) begin
        jtag_state = JtagResetState;
        wait(cfg.vif.trst_n == 1);
        continue;
      end

      `uvm_info(`gfn, $sformatf("state = %0s, ir = 0x%0h, dr = 0x%0h dout = 0x%0h counter = %0d",
                                jtag_state.name, ir, dr, dout, counter), UVM_DEBUG)
      case (jtag_state)
        JtagResetState: begin
          if (!read_tms()) jtag_state = JtagIdleState;
        end
        JtagIdleState: begin
          if (read_tms()) jtag_state = JtagSelectDrState;
        end
        JtagSelectDrState: begin
          jtag_state = read_tms() ? JtagSelectIrState : JtagCaptureDrState;
        end

        // Select DR
        JtagCaptureDrState: begin
          jtag_state = read_tms() ? JtagExit1DrState : JtagShiftDrState;
          if (jtag_state == JtagShiftDrState) begin
            dr      = 0;
            dout    = 0;
            counter = 0;
          end
        end
        JtagShiftDrState: begin
          jtag_state = read_tms() ? JtagExit1DrState : JtagShiftDrState;
          dr[counter] = read_tdi();
          dout[counter] = read_tdo();
          counter++;
        end
        JtagExit1DrState: begin
          jtag_state = read_tms() ? JtagUpdateDrState : JtagPauseDrState;
        end
        JtagPauseDrState: begin
          jtag_state = read_tms() ? JtagExit2DrState : JtagPauseDrState;
        end
        JtagExit2DrState: begin
          jtag_state = read_tms() ? JtagUpdateDrState : JtagShiftDrState;
        end
        JtagUpdateDrState: begin
          jtag_state = read_tms() ? JtagSelectDrState : JtagIdleState;

          // Send DR packet to analysis port, so long as the DR length is positive
          if (cfg.vif.trst_n && counter > 0) begin
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
          jtag_state = read_tms() ? JtagResetState : JtagCaptureIrState;
        end
        JtagCaptureIrState: begin
          jtag_state = read_tms() ? JtagExit1IrState : JtagShiftIrState;
          if (jtag_state == JtagShiftIrState) begin
            ir      = 0;
            counter = 0;
          end
        end
        JtagShiftIrState: begin
          jtag_state  = read_tms() ? JtagExit1IrState : JtagShiftIrState;
          ir[counter] = read_tdi();
          counter++;
        end
        JtagExit1IrState: begin
          jtag_state = read_tms() ? JtagUpdateIrState : JtagPauseIrState;
        end
        JtagPauseIrState: begin
          jtag_state = read_tms() ? JtagExit2IrState : JtagPauseIrState;
        end
        JtagExit2IrState: begin
          jtag_state = read_tms() ? JtagUpdateIrState : JtagShiftIrState;
        end
        JtagUpdateIrState: begin
          jtag_state = read_tms() ? JtagSelectDrState : JtagIdleState;

          // Send IR packet to analysis port, so long as the IR length is positive.
          if (cfg.vif.trst_n && counter > 0) begin
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
