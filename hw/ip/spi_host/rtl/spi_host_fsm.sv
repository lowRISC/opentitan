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
  output logic                       last_read_o,
  output logic                       last_write_o,
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

  logic             is_idle;
  logic [15:0]      clkdiv, clkdiv_q;
  logic [15:0]      clk_cntr_q, clk_cntr_d;
  logic             clk_cntr_en;

  logic [1:0]       speed_cpha0, speed_cpha1;

  logic [CSW-1:0]   csid;
  logic [CSW-1:0]   csid_q;

  logic [3:0]       csnidle, csntrail, csnlead;
  logic [3:0]       csnidle_q, csntrail_q, csnlead_q;
  logic             full_cyc, cpha, cpol;
  logic             full_cyc_q, cpha_q, cpol_q;

  // Unlike the configopts fields, the segment fields can change in back-to-backsegment operation.
  // (If a change in only the configopts fields is detected, the FSM transitions to idle instead).
  // For that reason, when using the segment fields in back-to-back operations,  we have to bear
  // in mind context and determine whether it is appropriate to use the value for the previous
  // segment or the following segment.
  // For instance, the cmd_rd_en signal is sometimes used to push segment byte into the shift
  // register, and so in that case it is important to use cmd_rd_en_q in that sense.  The same
  // signal is consulted to load the bit counter at the /beginning/ of each byte or dummy cycle,
  // and so in this context it is appropriate to use cmd_rd_en_d (which refers to the value from
  // the immediately following segment).
  logic [1:0]       cmd_speed_d, cmd_speed_q;
  logic             cmd_wr_en_d, cmd_wr_en_q;
  logic             cmd_rd_en_d, cmd_rd_en_q;
  logic [8:0]       cmd_len_d, cmd_len_q;
  logic             csaat;
  logic             csaat_q;

  logic [2:0]       bit_cntr_d, bit_cntr_q;
  logic [8:0]       byte_cntr_cpha0_d, byte_cntr_cpha1_d, byte_cntr_cpha0_q, byte_cntr_cpha1_q;
  logic [8:0]       byte_cntr_early, byte_cntr_late;
  logic [3:0]       wait_cntr_d, wait_cntr_q;
  logic             last_bit, last_byte;

  logic             state_changing;
  logic             byte_starting, byte_starting_cpha0, byte_starting_cpha0_q, byte_starting_cpha1;
  logic             bit_shifting, bit_shifting_cpha0, bit_shifting_cpha0_q, bit_shifting_cpha1;
  logic             byte_ending, byte_ending_cpha0, byte_ending_cpha0_q, byte_ending_cpha1;

  logic             sample_en_d, sample_en_q, sample_en_q2;

  logic             config_changed;
  logic             fsm_en;

  // new_command: signals a new segment input
  // new_command_cpha1: delayed copy for updating the byte_cntr (do not use the delayed copy for
  //                    updating the FSM state)
  logic             new_command, new_command_cpha1;

  logic             csb_single_d;
  logic [NumCS-1:0] csb_q;
  logic             sck_d, sck_q;

  logic wr_en_internal, rd_en_internal, sample_en_internal, shift_en_internal;

  logic stall;

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

  spi_host_st_e state_q, state_d;

  logic command_ready_int;
  assign command_ready_o = command_ready_int & ~stall;


  assign new_command    = command_valid_i && command_ready_int;
  assign config_changed = (command_i.configopts.cpol     != cpol_q) ||
                          (command_i.configopts.cpha     != cpha_q) ||
                          (command_i.configopts.full_cyc != full_cyc_q) ||
                          (command_i.configopts.csnidle  != csnidle_q) ||
                          (command_i.configopts.csntrail != csntrail_q) ||
                          (command_i.configopts.csnlead  != csnlead_q) ||
                          (command_i.configopts.clkdiv   != clkdiv_q);

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
    cmd_len_d   = new_command ? command_i.segment.len : cmd_len_q;
    cmd_wr_en_d = new_command ? command_i.segment.cmd_wr_en : cmd_wr_en_q;
    cmd_rd_en_d = new_command ? command_i.segment.cmd_rd_en : cmd_rd_en_q;
    cmd_speed_d = new_command ? command_i.segment.speed : cmd_speed_q;
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
      cmd_len_q   <= 9'h0;
    end else begin
      csid_q      <= (new_command && !stall) ? csid : csid_q;
      cpol_q      <= (new_command && !stall) ? cpol : cpol_q;
      cpha_q      <= (new_command && !stall) ? cpha : cpha_q;
      full_cyc_q  <= (new_command && !stall) ? full_cyc : full_cyc_q;
      csnidle_q   <= (new_command && !stall) ? csnidle : csnidle_q;
      csnlead_q   <= (new_command && !stall) ? csnlead : csnlead_q;
      csntrail_q  <= (new_command && !stall) ? csntrail : csntrail_q;
      clkdiv_q    <= (new_command && !stall) ? clkdiv : clkdiv_q;
      csaat_q     <= (new_command && !stall) ? csaat : csaat_q;
      cmd_wr_en_q <= (new_command && !stall) ? cmd_wr_en_d : cmd_wr_en_q;
      cmd_rd_en_q <= (new_command && !stall) ? cmd_rd_en_d : cmd_rd_en_q;
      cmd_speed_q <= (new_command && !stall) ? cmd_speed_d : cmd_speed_q;
      cmd_len_q   <= (new_command && !stall) ? cmd_len_d : cmd_len_q;
    end
  end

  assign is_idle     = (state_q == Idle) || (state_q == IdleCSBActive);

  assign active_o   = ~is_idle;

  assign clk_cntr_d = sw_rst_i              ? 16'h0 :
                      !clk_cntr_en          ? clk_cntr_q :
                      is_idle               ? 16'h0 :
                      new_command           ? clkdiv :
                      (clk_cntr_q == 16'h0) ? clkdiv :
                      clk_cntr_q - 1;

  assign tx_stall_o = wr_en_internal & ~sr_wr_ready_i;
  assign rx_stall_o = rd_en_internal & ~sr_rd_ready_i;
  assign clk_cntr_en = en_i;
  assign fsm_en = (clk_cntr_en && clk_cntr_q == 0);

  spi_host_st_e next_state_after_idle;
  always_comb begin
    if (command_valid_i) begin
      if (config_changed) begin
         next_state_after_idle = CSBSwitch;
      end else begin
         next_state_after_idle = WaitLead;
      end
    end else begin
      next_state_after_idle = Idle;
    end
  end

  spi_host_st_e next_state_after_idle_csb_active;
  logic         command_ready_idle_csb_active;
  always_comb begin
    if (command_valid_i) begin
      if (command_i.csid != csid_q) begin
        //
        // Do not acknowledge the command now, as it will trigger
        // an update of the internal command and configuration registers.
        // *Silently* transition to WaitTrail.  The command
        // will be acknowledged later, at the end of the WaitIdle state.
        //
        next_state_after_idle_csb_active = WaitTrail;
        // Explicitly *suppress* command_ready
        command_ready_idle_csb_active = 1'b0;
      end else begin
        next_state_after_idle_csb_active = InternalClkLow;
        command_ready_idle_csb_active = 1'b1;
      end
    end else begin
      next_state_after_idle_csb_active = IdleCSBActive;
      command_ready_idle_csb_active = 1'b1;
    end
  end

  //
  // FSM main body: Controls state transitions and command_ready_o signaling
  //
  always_comb begin
    state_d = state_q;
    command_ready_int = 1'b0;
    if (sw_rst_i) begin
      state_d = Idle;
    end else if (fsm_en) begin
      unique case (state_q)
        Idle: begin
          // Initial state, wait for commands.
          command_ready_int = 1'b1;
          state_d = next_state_after_idle;
        end
        WaitLead: begin
          // Transaction lead: CSB is low, waiting to start sck pulses.
          if (wait_cntr_q == 4'h0) begin
            state_d = InternalClkHigh;
          end
        end
        InternalClkLow: begin
          // One of two active clock states. sck is low when CPOL=0.
          state_d = InternalClkHigh;
        end
        InternalClkHigh: begin
          // One of two active clock states. sck is low when CPOL=0.
          // Typically often the last state in a command, and so the next state depends on CSAAT,
          // and of CSAAT is asserted, the details of the subsequent command.
          if (!last_bit || !last_byte) begin
            state_d = InternalClkLow;
          // Check value of csaat for the previously submitted segment
          end else if (!csaat_q) begin
            state_d = WaitTrail;
          end else begin
            state_d = next_state_after_idle_csb_active;
            command_ready_int = command_ready_idle_csb_active;
          end
        end
        WaitTrail: begin
          // Prepare to enter CSB high idle state by waiting csntrail cycles.
          if (wait_cntr_q == 4'h0) begin
            state_d = WaitIdle;
          end
        end
        WaitIdle: begin
          // Once CSB is high, wait for the designated number of cycles before accepting commands.
          if (wait_cntr_q == 4'h0) begin
            // ready to accept new command
            command_ready_int = 1'b1;
            state_d = next_state_after_idle;
          end
        end
        CSBSwitch: begin
          // Insert extra idle cycles when swtiching between CSID, this allows time to switch CPHA,
          // CPOL and clkdiv settings, as well as guarantee that the idle delay requirements have
          // been observed for the new device.
          if (wait_cntr_q == 4'h0) begin
            state_d = WaitLead;
          end else begin
            state_d = CSBSwitch;
          end
        end
        IdleCSBActive: begin
          // Wait for new commands, but with CSB held active low.
          state_d = next_state_after_idle_csb_active;
          command_ready_int = command_ready_idle_csb_active;
        end
        default: begin
          command_ready_int  = 1'b0;
          state_d = Idle;
        end
      endcase
    end
  end

  // All register updates freeze when a stall is detected.
  // The definition of the stall signal looks ahead to determine whether a conflict is looming.
  // Thus stall depends on state_d.  Making state_d depend on stall
  // would create a circular logic loop, and lint errors.  Therefore stall is applied here, not
  // in the previous always_comb block;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q    <= Idle;
      clk_cntr_q <= 16'h0;
    end else begin
      state_q    <= stall ? state_q : state_d;
      clk_cntr_q <= stall ? clk_cntr_q : clk_cntr_d;
    end
  end

  logic segment_rd_en, segment_rd_en_cpha0, segment_rd_en_cpha1;

  assign state_changing = (state_q != state_d);
  assign byte_starting_cpha0 = ~sw_rst_i & state_changing &
                               ((state_d == WaitLead) |
                                (state_d == InternalClkLow & bit_cntr_q==0));
  assign bit_shifting_cpha0  = ~sw_rst_i & state_changing &
                               (state_d == InternalClkLow & bit_cntr_q != 0);
  assign byte_ending_cpha0   = ~sw_rst_i & state_changing &
                               (state_q == InternalClkHigh & bit_cntr_q == 0);

  assign speed_cpha0         = cmd_speed_q;
  assign segment_rd_en_cpha0 = cmd_rd_en_q;

  // We can calculate byte transitions for CHPA=1 by noting
  // that in this implmentation, the sck edges have a 1-1
  // correspondence with FSM transitions.
  // New bytes are loaded exactly one state transition behind the time
  // when they would be loaded if CPHA=0
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      byte_starting_cpha0_q <= 1'b0;
      byte_ending_cpha0_q   <= 1'b0;
      bit_shifting_cpha0_q  <= 1'b0;
      speed_cpha1           <= Standard;
      segment_rd_en_cpha1   <= 1'b0;
      new_command_cpha1     <= 1'b0;
    end else if (state_changing && !stall) begin
      byte_ending_cpha0_q   <= byte_ending_cpha0;
      byte_starting_cpha0_q <= byte_starting_cpha0;
      bit_shifting_cpha0_q  <= bit_shifting_cpha0;
      speed_cpha1           <= speed_cpha0;
      segment_rd_en_cpha1   <= segment_rd_en_cpha0;
      new_command_cpha1     <= new_command;
    end
  end

  // The <XYZ>_cpha0_q pulse registers queue up a delayed <XYZ> pulse for use
  // in CPHA=1 mode. Here we also have to ensure that the resulting
  // pulse is only one cycle long.
  assign byte_starting_cpha1 = byte_starting_cpha0_q & state_changing;
  assign byte_ending_cpha1   = byte_ending_cpha0_q   & state_changing;
  assign bit_shifting_cpha1  = bit_shifting_cpha0_q  & state_changing;

  assign byte_starting = (cpha == 1'b0) ? byte_starting_cpha0 :
                                          byte_starting_cpha1;

  assign byte_ending   = (cpha == 1'b0) ? byte_ending_cpha0 :
                                          byte_ending_cpha1;

  assign bit_shifting  = (cpha == 1'b0) ? bit_shifting_cpha0 :
                                          bit_shifting_cpha1;

  assign speed_o       = (cpha == 1'b0) ? speed_cpha0:
                                          speed_cpha1;

  assign segment_rd_en = (cpha == 1'b0) ? segment_rd_en_cpha0:
                                          segment_rd_en_cpha1;

  assign byte_cntr_early = (cpha == 1'b0) ? byte_cntr_cpha0_d :
                                            byte_cntr_cpha1_d;
  assign byte_cntr_late  = (cpha == 1'b0) ? byte_cntr_cpha0_q :
                                            byte_cntr_cpha1_q;

  logic [2:0] shift_size;
  logic [2:0] start_bit;

  always_comb begin
    if (!cmd_rd_en_d && !cmd_wr_en_d) begin
      // direction == 0, means to send out
      // a fixed number of pulses, NOT bytes.
      // thus "last_bit" is always asserted,
      // and the number of pulses is counted
      // by byte_cntr_d.
      shift_size = 0;
      start_bit = 3'h0;
    end else begin
      unique case (cmd_speed_d)
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
  //
  // The variable last_byte is only used for updating the FSM state.
  // For CPHA=1 operation, either byte_cntr_cpha0_q or byte_cntr_cpha1_q
  // can drive the FSM properly.  However, we explicitly choose
  // byte_cntr_cpha0_q to avoid a combinational logic loop.
  //
  assign last_byte = (byte_cntr_cpha0_q == 9'h0);

  // Note: when updating the byte_cntr in CPHA=0 mode with a new command value, the length must
  // be pulled in directly from the command bus, cmd_len_d;
  assign byte_cntr_cpha0_d = sw_rst_i    ? 9'h0 :
                             !fsm_en     ? byte_cntr_cpha0_q :
                             new_command ? cmd_len_d :
                             byte_ending_cpha0 ? byte_cntr_cpha0_q - 1 :
                             byte_cntr_cpha0_q;

  // Note: when updating the byte_cntr in CPHA=1 mode with a new command value, the length must
  // be pulled in with a single state delay (using new_command_cpha1) and must use the
  // registered value, cmd_len_q;
  assign byte_cntr_cpha1_d = sw_rst_i          ? 9'h0 :
                             !fsm_en           ? byte_cntr_cpha1_q :
                             new_command_cpha1 ? cmd_len_q :
                             byte_ending_cpha1 ? byte_cntr_cpha1_q - 1 :
                             byte_cntr_cpha1_q;

  always_comb begin
    if(sw_rst_i) begin
      wait_cntr_d = 4'b0;
    end else if (!fsm_en) begin
      wait_cntr_d = wait_cntr_q;
    end else if (state_changing) begin
      unique case (state_d)
         WaitLead: begin
           wait_cntr_d = csnlead;
         end
         WaitTrail: begin
           wait_cntr_d = csntrail;
         end
         WaitIdle: begin
           wait_cntr_d = csnidle;
         end
         CSBSwitch: begin
           wait_cntr_d = csnidle;
         end
         default: begin
           // Hold wait cntr to zero
           // for states that don't use it
           wait_cntr_d = 4'b0;
         end
      endcase
    end else if (wait_cntr_q == 0) begin
      wait_cntr_d = 4'h0;
    end else begin
      wait_cntr_d = wait_cntr_q - 1;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      bit_cntr_q        <= 3'h0;
      byte_cntr_cpha0_q <= 9'h0;
      byte_cntr_cpha1_q <= 9'h0;
      wait_cntr_q       <= 4'h0;
    end else begin
      bit_cntr_q        <= stall ? bit_cntr_q        : bit_cntr_d;
      byte_cntr_cpha0_q <= stall ? byte_cntr_cpha0_q : byte_cntr_cpha0_d;
      byte_cntr_cpha1_q <= stall ? byte_cntr_cpha1_q : byte_cntr_cpha1_d;
      wait_cntr_q       <= stall ? wait_cntr_q       : wait_cntr_d;
    end
  end

  assign wr_en_internal    = byte_starting & cmd_wr_en_d;
  assign shift_en_internal = bit_shifting;

  assign rd_en_internal    = byte_ending & segment_rd_en;
  assign sample_en_d       = byte_starting | shift_en_o;
  assign full_cyc_o        = full_cyc;
  assign last_read_o       = (byte_cntr_late == 'h0) & rd_en_o & sr_rd_ready_i;

  assign last_write_o      = (byte_cntr_early == 'h0) & wr_en_o & sr_wr_ready_i;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sample_en_q <= 1'b0;
      sample_en_q2 <= 1'b0;
    end else begin
      sample_en_q  <= (fsm_en && !stall) ? sample_en_d : sample_en_q;
      sample_en_q2 <= (fsm_en && !stall) ? sample_en_q : sample_en_q2;
    end
  end

  assign sample_en_internal = full_cyc_o ? sample_en_q2 : sample_en_q;

  always_comb begin
    unique case (state_d)
      WaitLead, InternalClkLow, InternalClkHigh, IdleCSBActive, WaitTrail:
        csb_single_d = 1'b0;
      default:
        csb_single_d = 1'b1;
    endcase
  end

  assign sck_d = cpol ? (state_d != InternalClkHigh) :
                        (state_d == InternalClkHigh);

  assign sck_o = sck_q;

  prim_flop_en u_sck_flop (
    .clk_i,
    .rst_ni,
    .en_i(~stall),
    .d_i(sck_d),
    .q_o(sck_q)
  );

  for (genvar ii = 0; ii < NumCS; ii = ii + 1) begin : gen_csb_gen
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        csb_q[ii] <= 1'b1;
      end else begin
        csb_q[ii] <= (csid != ii) ? 1'b1 :
                     !stall       ? csb_single_d :
                     csb_q[ii];
      end
    end
  end : gen_csb_gen

  assign csb_o = csb_q;

  always_comb begin
    if (&csb_o) begin
      sd_en_o[3:0] = 4'h0;
    end else begin
      unique case (speed_o)
        Standard: begin
          sd_en_o[0]   = 1'b1;
          sd_en_o[1]   = 1'b0;
          sd_en_o[3:2] = 2'b00;
        end
        Dual:     begin
          sd_en_o[1:0] = {2{cmd_wr_en_q}};
          sd_en_o[3:2] = 2'b00;
        end
        Quad:     begin
          sd_en_o[3:0] = {4{cmd_wr_en_q}};
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

  `ASSERT(BidirOnlyInStdMode_A,
      cmd_speed_d == Standard || !(cmd_rd_en_d && cmd_wr_en_d),
      clk_i, rst_ni)
  `ASSERT(ValidSpeed_A, cmd_speed_d != RsvdSpd, clk_i, rst_ni)
  `ASSERT(ValidCSID_A, csid < NumCS, clk_i, rst_ni)

endmodule
