// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Core Implemenation module for Serial Peripheral Interface (SPI) Host IP.
//

module spi_host_fsm
  import spi_host_cmd_pkg::*;
#(
  parameter  int NumCS = 1
) (
  input                              clk_i,
  input                              rst_ni,
  input                              en_i,
  input  command_t                   command_i,
  input                              command_valid_i,
  output logic                       command_ready_o,
  output logic                       sck_o,
  output logic [NumCS-1:0]           csb_o,
  output logic [3:0]                 sd_en_o,
  output logic                       cmd_end_o,
  output logic                       wr_en_o,
  input                              sr_wr_ready_i,
  output logic                       rd_en_o,
  input                              sr_rd_ready_i,
  output logic                       sample_en_o,
  output logic                       shift_en_o,
  output logic [1:0]                 speed_o,
  output logic                       full_cyc_o,
  output logic                       rx_stall_o,
  output logic                       tx_stall_o,
  output logic                       active_o,

  input                              sw_rst_i
);

  logic             isIdle;
  logic [15:0]      clkdiv, clkdiv_q;
  logic [15:0]      clk_cntr_q, clk_cntr_d;
  logic             clk_cntr_en;

  logic [CSW-1:0]   csid;
  logic [CSW-1:0]   csid_q;

  logic [3:0]       csnidle, csntrail, csnlead;
  logic [3:0]       csnidle_q, csntrail_q, csnlead_q;
  logic             full_cyc, cpha, cpol;
  logic             full_cyc_q, cpha_q, cpol_q;

  logic [1:0]       cmd_speed;
  logic [1:0]       cmd_speed_q;
  logic             cmd_wr_en, cmd_wr_en_q;
  logic             cmd_rd_en, cmd_rd_en_q;
  // cmd_len needs no data latching as it is only used at the very start of a command.
  // The corresponding register, cmd_len_q, would create a warning at synthesis
  logic [8:0]       cmd_len;
  logic             csaat;
  logic             csaat_q;

  logic [2:0]       bit_cntr_d, bit_cntr_q;
  logic [8:0]       byte_cntr_d, byte_cntr_q;
  // TODO: merge lead, trail * idle counters to match documentation
  logic [3:0]       lead_cntr_d, idle_cntr_d, trail_cntr_d;
  logic [3:0]       lead_cntr_q, idle_cntr_q, trail_cntr_q;
  logic             last_bit, last_byte;

  logic             state_changing;
  logic             byte_starting, byte_starting_cpha0, byte_starting_cpha1;
  logic             bit_shifting, bit_shifting_cpha0, bit_shifting_cpha1;
  logic             byte_ending, byte_ending_cpha0, byte_ending_cpha1;
  logic             lead_starting;
  logic             trail_starting;
  logic             idle_starting;

  logic             sample_en_d, sample_en_q, sample_en_q2;

  // TODO: Update switch_required to handle ANY change in parameters
  logic             switch_required;
  logic             fsm_en;
  logic             new_command;

  logic             csb_single_d;
  logic [NumCS-1:0] csb_q;
  logic             sck_d, sck_q;

  logic wr_en_internal, rd_en_internal, sample_en_internal, shift_en_internal;

  logic stall, stall_q;

  assign stall = rx_stall_o | tx_stall_o;

  // suppress output pulses if stalled.
  assign wr_en_o     = wr_en_internal & ~stall;
  assign rd_en_o     = rd_en_internal & ~stall;
  assign sample_en_o = sample_en_internal & ~stall;
  assign shift_en_o  = shift_en_internal & ~stall;

  typedef enum logic [2:0] {
    Idle,
    WaitLead,
    InternalClkLow,
    InternalClkHigh,
    WaitTrail,
    WaitIdle,
    CSBSwitch,
    IdleCSBActive
  } spi_host_st_e;

  // The FSM stall mechanism halts the FSM by preventing the update of any internal registers.
  // Since most register data values in this do not actually depend on the stall signal, this
  // means that the stall signal is routed to the enable line of the corresponding flop but does
  // not influence the and flip-flop data (_d) signals.
  //
  // This is not the case for the main FSM state variable, where there there is actually a logical
  // cyclical dependency to worry about.  The stall variable depends on the FSM state, because an
  // empty/full data FIFO only stalls the FSM when during states where data is needed from the
  // FIFO.  Meanwhile, the FSM state depends on the stall variable through the `command_ready_o`
  // signal. We only want to start processing an incoming command when it has been acknowledged,
  // and we don't want to acknowledge the next command during a stall condition.
  //
  // Linting reports this cyclical dependency as unoptimizable and simulations can hang
  // if this is not resolved.
  //
  // In principle, this cyclical dependency could possibly be broken through careful analysis of
  // the logical dependencies between these three signals.  However, this may become a
  // developmental challenge as we revise and debug this block.  So instead we take a simpler
  // approach of breaking this combinational logic loop with a second FSM state register.
  //
  // That said there are then two copies of the FSM state variable
  // Actual:   The true state of the FSM, which controls the peripheral IOs and the interactions
  //           with the other blocks.
  // Prestall: The "tentative" state of the FSM, which can be overridden by stall events. Normally
  //           this matches the actual state. However when a stall event is recieved, the actual
  //           state remains unchanged.  Once the stall event is resolved, the actual state is
  //           updated to match the prestall state.
  //
  // The prestall state variable has no combinational logic dependency on the stall signal.

  spi_host_st_e prestall_st_q, prestall_st_d, actual_st_d, actual_st_q;

  assign new_command     = command_valid_i && command_ready_o;
  assign switch_required = command_valid_i && (command_i.csid != csid_q);

  // TODO: use functions/combinational logic to simplify "bypassable"
  // state logic (see documentation)

  always_comb begin
    csid      = new_command ? command_i.csid : csid_q;
    cpol      = new_command ? command_i.configopts.cpol : cpol_q;
    cpha      = new_command ? command_i.configopts.cpha : cpha_q;
    full_cyc  = new_command ? command_i.configopts.full_cyc : full_cyc_q;
    csnidle   = new_command ? command_i.configopts.csnidle : csnidle_q;
    csnlead   = new_command ? command_i.configopts.csnlead : csnlead_q;
    csntrail  = new_command ? command_i.configopts.csntrail : csntrail_q;
    clkdiv    = new_command ? command_i.configopts.clkdiv : clkdiv_q;
    csaat     = new_command ? command_i.segment.csaat : csaat_q;
    // cmd_len needs no data latching as it is only used at the very start of a command.
    cmd_len   = command_i.segment.len;
    cmd_rd_en = new_command ? command_i.segment.cmd_rd_en : cmd_rd_en_q;
    cmd_wr_en = new_command ? command_i.segment.cmd_wr_en : cmd_wr_en_q;
    cmd_speed = new_command ? command_i.segment.speed : cmd_speed_q;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      csid_q      <= {CSW{1'b0}};
      cpol_q      <= 1'b0;
      cpha_q      <= 1'b0;
      full_cyc_q  <= 1'b0;
      csnidle_q   <= 4'h0;
      csnlead_q   <= 4'h0;
      csntrail_q  <= 4'h0;
      clkdiv_q    <= 16'h0;
      csaat_q     <= 1'b0;
      cmd_rd_en_q <= 1'b0;
      cmd_wr_en_q <= 1'b0;
      cmd_speed_q <= 2'b00;
    end else begin
      csid_q      <= new_command ? csid : csid_q;
      cpol_q      <= new_command ? cpol : cpol_q;
      cpha_q      <= new_command ? cpha : cpha_q;
      full_cyc_q  <= new_command ? full_cyc : full_cyc_q;
      csnidle_q   <= new_command ? csnidle : csnidle_q;
      csnlead_q   <= new_command ? csnlead : csnlead_q;
      csntrail_q  <= new_command ? csntrail : csntrail_q;
      clkdiv_q    <= new_command ? clkdiv : clkdiv_q;
      csaat_q     <= new_command ? csaat : csaat_q;
      cmd_rd_en_q <= new_command ? cmd_rd_en : cmd_rd_en_q;
      cmd_wr_en_q <= new_command ? cmd_wr_en : cmd_wr_en_q;
      cmd_speed_q <= new_command ? cmd_speed : cmd_speed_q;
    end
  end

  assign isIdle     = (actual_st_q == Idle) || (actual_st_q == IdleCSBActive);

  assign active_o   = ~isIdle;

  assign clk_cntr_d = sw_rst_i              ? 16'h0 :
                      !clk_cntr_en          ? clk_cntr_q :
                      isIdle                ? 16'h0 :
                      new_command           ? clkdiv :
                      (clk_cntr_q == 16'h0) ? clkdiv :
                      clk_cntr_q - 1;

  assign tx_stall_o = wr_en_internal & ~sr_wr_ready_i;
  assign rx_stall_o = rd_en_internal & ~sr_rd_ready_i;
  assign clk_cntr_en = en_i;
  assign fsm_en = (clk_cntr_en && clk_cntr_q == 0);

  // FSM main body: Controls state transitions and command_ready_o signaling
  //
  // command_ready_o Note: New commands should may be acknowled as we enter into the idle condition
  // with two subtle exceptions:
  //   1. During stall conditions the FSM does not actually perform transitions and so
  //      command_ready_o should be held low during stalls regardless of the current state
  //   2. In cases where the next segment is for a different CSID, command_ready_o is held
  //      explicitly low to enforce CSNTRAIL, CSIDLE requirements for the previous segment.
  //      Holding command_ready_o low in this case defers updates of the internal state variables
  always_comb begin
    prestall_st_d = actual_st_q;
    command_ready_o = 1'b0;
    if (sw_rst_i) begin
      prestall_st_d = Idle;
    end else if (stall_q) begin
      prestall_st_d = prestall_st_q;
    end else if (fsm_en) begin
      unique case (actual_st_q)
        Idle: begin
          // Initial state, wait for commands.
          command_ready_o = 1'b1;
          if (command_valid_i) begin
            if (command_i.csid != csid_q) begin
              prestall_st_d = CSBSwitch;
            end else begin
              prestall_st_d = WaitLead;
            end
          end
        end
        WaitLead: begin
          // Transaction lead: CSB is low, waiting to start sck pulses.
          if (lead_cntr_q == 4'h0) begin
            prestall_st_d = InternalClkHigh;
          end
        end
        InternalClkLow: begin
          // One of two active clock states. sck is low when CPOL=0.
          prestall_st_d = InternalClkHigh;
        end
        InternalClkHigh: begin
          // One of two active clock states. sck is low when CPOL=0.
          // Typically often the last state in a command, and so the next state depends on CSAAT,
          // and of CSAAT is asserted, the details of the subsequent command.
          if (!last_bit || !last_byte) begin
            prestall_st_d = InternalClkLow;
          end else if (!command_i.segment.csaat) begin
            prestall_st_d = WaitTrail;
          end else if (!command_valid_i) begin
            prestall_st_d = IdleCSBActive;
          end else if (command_i.csid != csid_q) begin
            prestall_st_d = WaitTrail;
          end else begin
            command_ready_o  = 1'b1;
            prestall_st_d = InternalClkLow;
          end
        end
        WaitTrail: begin
          // Prepare to enter CSB high idle state by waiting csntrail cycles.
          if (trail_cntr_q == 4'h0) begin
            prestall_st_d = WaitIdle;
          end
        end
        WaitIdle: begin
          // Once CSB is high, wait for the designated number of cyclse before accepting commands.
          if (idle_cntr_q == 4'h0) begin
            // ready to accept new command
            command_ready_o = 1'b1;
            if (command_valid_i) begin
              if (switch_required) begin
                 prestall_st_d = CSBSwitch;
              end else begin
                 prestall_st_d = WaitLead;
              end
            end else begin
              prestall_st_d = Idle;
            end
          end
        end
        CSBSwitch: begin
          // Insert extra idle cycles when swtiching between CSID, this allows time to switch CPHA,
          // CPOL and clkdiv settings, as well as guarantee that the idle delay requirements have
          // been observed for the new device.
          if (idle_cntr_q == 4'h0) begin
            prestall_st_d = WaitLead;
          end else begin
            prestall_st_d = WaitIdle;
          end
        end
        IdleCSBActive: begin
          // Wait for new commands, but with CSB held active low.
          if (command_valid_i) begin
            if (command_i.csid != csid_q) begin
              // New command received, but for a different CSID than the last.  Deactivate CSB,
              // while still adhering to trail and idle time requirements
              prestall_st_d = WaitTrail;
              // Explicitly delay command_ready until the end of WaitIdle.  We need to observe
              // the trail time requirements for the current CSID, so we can't update our
              // configopts until CSB is high.
              command_ready_o = 1'b0;
            end else begin
              command_ready_o = 1'b1;
              prestall_st_d = InternalClkLow;
            end
          end else begin
            command_ready_o = 1'b1;
          end
        end
        default: begin
          command_ready_o  = 1'b0;
          prestall_st_d = Idle;
        end
      endcase
    end
  end

  // All register updates freeze when a stall is detected.
  // The definition of the stall signal looks ahead to determine whether a conflict is looming.
  // Thus stall depends on actual_st_d.  Making the actual state depend on stall
  // would create a circular logic loop, and lint errors.  Therefore stall is applied here, not
  // in the previous always_comb block;

  logic stall_resolve;

  assign stall_resolve = !stall && stall_q;
  assign actual_st_d   = stall         ? actual_st_q :
                         stall_resolve ? prestall_st_q :
                         prestall_st_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      actual_st_q         <= Idle;
      prestall_st_q       <= Idle;
      clk_cntr_q          <= 16'h0;
      stall_q             <= 1'b0;
    end else begin
      stall_q             <= stall;
      prestall_st_q       <= prestall_st_d;
      actual_st_q         <= actual_st_d;
      clk_cntr_q          <= stall ? clk_cntr_q : clk_cntr_d;
    end
  end

  assign state_changing = (actual_st_q != prestall_st_d);

  // The stall signal depends on byte_starting, and since acutal_st_d depends on stall,
  // byte_starting_cpha0 is based off prestall_st_d.   In the event of a stall
  // byte_starting may be high for multiple cycles until the stall is resolved.
  // The rd_en_o and wr_en_o signals held low during a stall, thus the control signals
  // sent to the byte_merge and byte_sleect blocks are active for only one cycle.
  assign byte_starting_cpha0 = ~sw_rst_i & state_changing &
                               ((prestall_st_d == WaitLead) |
                                (prestall_st_d == InternalClkLow & bit_cntr_q==0));
  assign bit_shifting_cpha0  = ~sw_rst_i & state_changing &
                               (actual_st_d == InternalClkLow & bit_cntr_q != 0);
  assign byte_ending_cpha0   = ~sw_rst_i & state_changing &
                               (actual_st_q == InternalClkHigh & bit_cntr_q == 0);

  // We can calculate byte transitions for CHPA=1 by noting
  // that in this implmentation, the sck edges have a 1-1
  // correspondence with FSM transitions.
  // New bytes are loaded exactly one state transition behind the time
  // when they would be loaded if CPHA=0
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      byte_starting_cpha1 <= 1'b0;
      byte_ending_cpha1 <= 1'b0;
      bit_shifting_cpha1 <= 1'b0;
    end else begin
      byte_ending_cpha1   <= (state_changing && !stall) ? byte_ending_cpha0 : 1'b0;
      byte_starting_cpha1 <= (state_changing && !stall) ? byte_starting_cpha0 : 1'b0;
      bit_shifting_cpha1  <= (state_changing && !stall) ? bit_shifting_cpha0 : 1'b0;
    end
  end

  assign byte_starting = (cpha == 1'b0) ? byte_starting_cpha0 :
                                          byte_starting_cpha1;

  assign byte_ending   = (cpha == 1'b0) ? byte_ending_cpha0 :
                                          byte_ending_cpha1;

  assign bit_shifting  = (cpha == 1'b0) ? bit_shifting_cpha0 :
                                          bit_shifting_cpha1;

  logic [2:0] shift_size;
  logic [2:0] start_bit;

  always_comb begin
    if (!cmd_rd_en && !cmd_wr_en) begin
      // direction == 0, means to send out
      // a fixed number of pulses, NOT bytes.
      // thus "last_bit" is always asserted,
      // and the number of pulses is counted
      // by byte_cntr_d.
      shift_size = 0;
      start_bit = 3'h0;
    end else begin
      unique case (cmd_speed)
        Standard: begin
          shift_size = 3'h1;
          start_bit  = 3'h7;
        end
        Dual:     begin
          shift_size = 3'h2;
          start_bit  = 3'h6;
        end
        Quad:     begin
          shift_size = 3'h4;
          start_bit  = 3'h4;
        end
        default: begin
          // Invalid_speed;
          shift_size = 3'h1;
          start_bit  = 3'h1;
        end
      endcase
    end
  end

  assign bit_cntr_d = sw_rst_i         ? 3'h0 :
                      !fsm_en          ? bit_cntr_q :
                      byte_starting    ? start_bit :
                      bit_shifting     ? bit_cntr_q - shift_size :
                      bit_cntr_q;

  assign last_bit  = (bit_cntr_q == 3'h0);
  assign last_byte = (byte_cntr_q == 9'h0);

  assign byte_cntr_d = sw_rst_i    ? 9'h0 :
                       !fsm_en     ? byte_cntr_q :
                       new_command ? cmd_len :
                       byte_ending ? byte_cntr_q - 1 :
                       byte_cntr_q;

  assign lead_starting = state_changing && actual_st_d == WaitLead;

  assign lead_cntr_d = sw_rst_i         ? 4'h0 :
                       !fsm_en          ? lead_cntr_q :
                       lead_starting    ? csnlead :
                       lead_cntr_q == 0 ? 4'h0 :
                       lead_cntr_q - 1;

  assign trail_starting = state_changing && actual_st_d == WaitTrail;

  assign trail_cntr_d = sw_rst_i          ? 4'h0 :
                        !fsm_en           ? trail_cntr_q :
                        trail_starting    ? csntrail :
                        trail_cntr_q == 0 ? 4'h0 :
                        trail_cntr_q - 1;

  assign idle_starting = state_changing &&
                        (actual_st_d == WaitIdle ||
                         actual_st_d == CSBSwitch);

  assign idle_cntr_d = sw_rst_i         ? 4'h0 :
                       !fsm_en          ? idle_cntr_q :
                       idle_starting    ? csnidle :
                       idle_cntr_q == 0 ? 4'h0 :
                       idle_cntr_q - 1;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      bit_cntr_q   <= 3'h0;
      byte_cntr_q  <= 9'h0;
      idle_cntr_q  <= 4'h0;
      lead_cntr_q  <= 4'h0;
      trail_cntr_q <= 4'h0;
    end else begin
      bit_cntr_q   <= stall ? bit_cntr_q   : bit_cntr_d;
      byte_cntr_q  <= stall ? byte_cntr_q  : byte_cntr_d;
      idle_cntr_q  <= stall ? idle_cntr_q  : idle_cntr_d;
      lead_cntr_q  <= stall ? lead_cntr_q  : lead_cntr_d;
      trail_cntr_q <= stall ? trail_cntr_q : trail_cntr_d;
    end
  end

  assign wr_en_internal    = byte_starting & cmd_wr_en;
  assign shift_en_internal = bit_shifting;
  assign rd_en_internal    = byte_ending & cmd_rd_en;
  assign speed_o           = cmd_speed;
  assign sample_en_d       = byte_starting | shift_en_o;
  assign full_cyc_o        = full_cyc;
  assign cmd_end_o         = (byte_cntr_q == 'h1) & wr_en_o & sr_wr_ready_i;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sample_en_q <= 1'b0;
      sample_en_q2 <= 1'b00;
    end else begin
      sample_en_q  <= (fsm_en && !stall) ? sample_en_d : sample_en_q;
      sample_en_q2 <= (fsm_en && !stall) ? sample_en_q : sample_en_q2;
    end
  end

  assign sample_en_internal = full_cyc_o ? sample_en_q2 : sample_en_q;

  always_comb begin
    unique case (actual_st_d)
      WaitLead, InternalClkLow, InternalClkHigh, IdleCSBActive, WaitTrail:
        csb_single_d = 1'b0;
      default:
        csb_single_d = 1'b1;
    endcase
  end

  assign sck_d = cpol ? (actual_st_d != InternalClkHigh) :
                        (actual_st_d == InternalClkHigh);

  assign sck_o = sck_q;

  for (genvar ii = 0; ii < NumCS; ii = ii + 1) begin : gen_csb_gen
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        csb_q[ii] <= 1'b1;
        sck_q     <= 1'b0;
      end else begin
        csb_q[ii] <= (csid != ii) ? 1'b1 :
                     !stall       ? csb_single_d :
                     csb_q[ii];
        sck_q     <= !stall ? sck_d : sck_q;
      end
    end
  end : gen_csb_gen

  assign csb_o = csb_q;

  always_comb begin
    if (&csb_o) begin
      sd_en_o[3:0] = 4'h0;
    end else begin
      unique case (cmd_speed)
        Standard: begin
          sd_en_o[0]   = 1'b1;
          sd_en_o[1]   = 1'b0;
          sd_en_o[3:2] = 2'b00;
        end
        Dual:     begin
          sd_en_o[1:0] = {2{cmd_wr_en}};
          sd_en_o[3:2] = 2'b00;
        end
        Quad:     begin
          sd_en_o[3:0] = {4{cmd_wr_en}};
        end
        default: begin
          // invalid speed
          sd_en_o[3:0] = 4'h0;
        end
      endcase
    end
  end

  //
  // Assertions confirming valid user input.
  //

  `ASSERT(BidirOnlyInStdMode_A, cmd_speed == Standard || !(cmd_rd_en && cmd_wr_en), clk_i, rst_ni)
  `ASSERT(ValidSpeed_A, cmd_speed != RsvdSpd, clk_i, rst_ni)
  `ASSERT(ValidCSID_A, csid < NumCS, clk_i, rst_ni)

endmodule
