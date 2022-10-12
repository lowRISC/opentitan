/* Copyright 2018 ETH Zurich and University of Bologna.
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the “License”); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * File:   dmi_jtag_tap.sv
 * Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
 * Date:   19.7.2018
 *
 * Description: JTAG TAP for DMI (according to debug spec 0.13)
 *
 */

module dmi_jtag_tap #(
  parameter int unsigned IrLength = 5,
  // JTAG IDCODE Value
  parameter logic [31:0] IdcodeValue = 32'h00000001
  // xxxx             version
  // xxxxxxxxxxxxxxxx part number
  // xxxxxxxxxxx      manufacturer id
  // 1                required by standard
) (
  input  logic        tck_i,    // JTAG test clock pad
  input  logic        tms_i,    // JTAG test mode select pad
  input  logic        trst_ni,  // JTAG test reset pad
  input  logic        td_i,     // JTAG test data input pad
  output logic        td_o,     // JTAG test data output pad
  output logic        tdo_oe_o, // Data out output enable
  input  logic        testmode_i,
  // JTAG is interested in writing the DTM CSR register
  output logic        tck_o,
  // Synchronous reset of the dmi module triggered by JTAG TAP
  output logic        dmi_clear_o,
  output logic        update_o,
  output logic        capture_o,
  output logic        shift_o,
  output logic        tdi_o,
  output logic        dtmcs_select_o,
  input  logic        dtmcs_tdo_i,
  // we want to access DMI register
  output logic        dmi_select_o,
  input  logic        dmi_tdo_i
);

  typedef enum logic [3:0] {
    TestLogicReset, RunTestIdle, SelectDrScan,
    CaptureDr, ShiftDr, Exit1Dr, PauseDr, Exit2Dr,
    UpdateDr, SelectIrScan, CaptureIr, ShiftIr,
    Exit1Ir, PauseIr, Exit2Ir, UpdateIr
  } tap_state_e;

  tap_state_e tap_state_q, tap_state_d;
  logic update_dr, shift_dr, capture_dr;

  typedef enum logic [IrLength-1:0] {
    BYPASS0   = 'h0,
    IDCODE    = 'h1,
    DTMCSR    = 'h10,
    DMIACCESS = 'h11,
    BYPASS1   = 'h1f
  } ir_reg_e;

  // ----------------
  // IR logic
  // ----------------

  // shift register
  logic [IrLength-1:0]  jtag_ir_shift_d, jtag_ir_shift_q;
  // IR register -> this gets captured from shift register upon update_ir
  ir_reg_e              jtag_ir_d, jtag_ir_q;
  logic capture_ir, shift_ir, update_ir, test_logic_reset; // pause_ir

  always_comb begin : p_jtag
    jtag_ir_shift_d = jtag_ir_shift_q;
    jtag_ir_d       = jtag_ir_q;

    // IR shift register
    if (shift_ir) begin
      jtag_ir_shift_d = {td_i, jtag_ir_shift_q[IrLength-1:1]};
    end

    // capture IR register
    if (capture_ir) begin
      jtag_ir_shift_d =  IrLength'(4'b0101);
    end

    // update IR register
    if (update_ir) begin
      jtag_ir_d = ir_reg_e'(jtag_ir_shift_q);
    end

    if (test_logic_reset) begin
      // Bring all TAP state to the initial value.
      jtag_ir_shift_d = '0;
      jtag_ir_d = IDCODE;
    end
  end

  always_ff @(posedge tck_i, negedge trst_ni) begin : p_jtag_ir_reg
    if (!trst_ni) begin
      jtag_ir_shift_q <= '0;
      jtag_ir_q       <= IDCODE;
    end else begin
      jtag_ir_shift_q <= jtag_ir_shift_d;
      jtag_ir_q       <= jtag_ir_d;
    end
  end

  // ----------------
  // TAP DR Regs
  // ----------------
  // - Bypass
  // - IDCODE
  // - DTM CS
  logic [31:0] idcode_d, idcode_q;
  logic        idcode_select;
  logic        bypass_select;

  logic        bypass_d, bypass_q;  // this is a 1-bit register

  always_comb begin
    idcode_d = idcode_q;
    bypass_d = bypass_q;

    if (capture_dr) begin
      if (idcode_select) idcode_d = IdcodeValue;
      if (bypass_select) bypass_d = 1'b0;
    end

    if (shift_dr) begin
      if (idcode_select)  idcode_d = {td_i, 31'(idcode_q >> 1)};
      if (bypass_select)  bypass_d = td_i;
    end

    if (test_logic_reset) begin
      // Bring all TAP state to the initial value.
      idcode_d = IdcodeValue;
      bypass_d = 1'b0;
    end
  end

  // ----------------
  // Data reg select
  // ----------------
  always_comb begin : p_data_reg_sel
    dmi_select_o   = 1'b0;
    dtmcs_select_o = 1'b0;
    idcode_select  = 1'b0;
    bypass_select  = 1'b0;
    unique case (jtag_ir_q)
      BYPASS0:   bypass_select  = 1'b1;
      IDCODE:    idcode_select  = 1'b1;
      DTMCSR:    dtmcs_select_o = 1'b1;
      DMIACCESS: dmi_select_o   = 1'b1;
      BYPASS1:   bypass_select  = 1'b1;
      default:   bypass_select  = 1'b1;
    endcase
  end

  // ----------------
  // Output select
  // ----------------
  logic tdo_mux;

  always_comb begin : p_out_sel
    // we are shifting out the IR register
    if (shift_ir) begin
      tdo_mux = jtag_ir_shift_q[0];
    // here we are shifting the DR register
    end else begin
      unique case (jtag_ir_q)
        IDCODE:         tdo_mux = idcode_q[0];   // Reading ID code
        DTMCSR:         tdo_mux = dtmcs_tdo_i;   // Read from DTMCS TDO
        DMIACCESS:      tdo_mux = dmi_tdo_i;     // Read from DMI TDO
        default:        tdo_mux = bypass_q;      // BYPASS instruction
      endcase
    end
  end

  // ----------------
  // DFT
  // ----------------
  logic tck_n;

  prim_clock_inv #(
    .HasScanMode(1'b1),
    .NoFpgaBufG(1'b1)
  ) i_tck_inv (
    .clk_i      ( tck_i      ),
    .clk_no     ( tck_n      ),
    .scanmode_i ( testmode_i )
  );

  // TDO changes state at negative edge of TCK
  always_ff @(posedge tck_n, negedge trst_ni) begin : p_tdo_regs
    if (!trst_ni) begin
      td_o     <= 1'b0;
      tdo_oe_o <= 1'b0;
    end else begin
      td_o     <= tdo_mux;
      tdo_oe_o <= (shift_ir | shift_dr);
    end
  end
  // ----------------
  // TAP FSM
  // ----------------
  // Determination of next state; purely combinatorial
  always_comb begin : p_tap_fsm

    test_logic_reset   = 1'b0;

    capture_dr         = 1'b0;
    shift_dr           = 1'b0;
    update_dr          = 1'b0;

    capture_ir         = 1'b0;
    shift_ir           = 1'b0;
    // pause_ir           = 1'b0; unused
    update_ir          = 1'b0;

    unique case (tap_state_q)
      TestLogicReset: begin
        tap_state_d = (tms_i) ? TestLogicReset : RunTestIdle;
        test_logic_reset = 1'b1;
      end
      RunTestIdle: begin
        tap_state_d = (tms_i) ? SelectDrScan : RunTestIdle;
      end
      // DR Path
      SelectDrScan: begin
        tap_state_d = (tms_i) ? SelectIrScan : CaptureDr;
      end
      CaptureDr: begin
        capture_dr = 1'b1;
        tap_state_d = (tms_i) ? Exit1Dr : ShiftDr;
      end
      ShiftDr: begin
        shift_dr = 1'b1;
        tap_state_d = (tms_i) ? Exit1Dr : ShiftDr;
      end
      Exit1Dr: begin
        tap_state_d = (tms_i) ? UpdateDr : PauseDr;
      end
      PauseDr: begin
        tap_state_d = (tms_i) ? Exit2Dr : PauseDr;
      end
      Exit2Dr: begin
        tap_state_d = (tms_i) ? UpdateDr : ShiftDr;
      end
      UpdateDr: begin
        update_dr = 1'b1;
        tap_state_d = (tms_i) ? SelectDrScan : RunTestIdle;
      end
      // IR Path
      SelectIrScan: begin
        tap_state_d = (tms_i) ? TestLogicReset : CaptureIr;
      end
      // In this controller state, the shift register bank in the
      // Instruction Register parallel loads a pattern of fixed values on
      // the rising edge of TCK. The last two significant bits must always
      // be "01".
      CaptureIr: begin
        capture_ir = 1'b1;
        tap_state_d = (tms_i) ? Exit1Ir : ShiftIr;
      end
      // In this controller state, the instruction register gets connected
      // between TDI and TDO, and the captured pattern gets shifted on
      // each rising edge of TCK. The instruction available on the TDI
      // pin is also shifted in to the instruction register.
      ShiftIr: begin
        shift_ir = 1'b1;
        tap_state_d = (tms_i) ? Exit1Ir : ShiftIr;
      end
      Exit1Ir: begin
        tap_state_d = (tms_i) ? UpdateIr : PauseIr;
      end
      PauseIr: begin
        // pause_ir = 1'b1; // unused
        tap_state_d = (tms_i) ? Exit2Ir : PauseIr;
      end
      Exit2Ir: begin
        tap_state_d = (tms_i) ? UpdateIr : ShiftIr;
      end
      // In this controller state, the instruction in the instruction
      // shift register is latched to the latch bank of the Instruction
      // Register on every falling edge of TCK. This instruction becomes
      // the current instruction once it is latched.
      UpdateIr: begin
        update_ir = 1'b1;
        tap_state_d = (tms_i) ? SelectDrScan : RunTestIdle;
      end
      default: ; // can't actually happen since case is full
    endcase
  end

  always_ff @(posedge tck_i or negedge trst_ni) begin : p_regs
    if (!trst_ni) begin
      tap_state_q <= RunTestIdle;
      idcode_q    <= IdcodeValue;
      bypass_q    <= 1'b0;
    end else begin
      tap_state_q <= tap_state_d;
      idcode_q    <= idcode_d;
      bypass_q    <= bypass_d;
    end
  end

  // Pass through JTAG signals to debug custom DR logic.
  // In case of a single TAP those are just feed-through.
  assign tck_o = tck_i;
  assign tdi_o = td_i;
  assign update_o = update_dr;
  assign shift_o = shift_dr;
  assign capture_o = capture_dr;
  assign dmi_clear_o = test_logic_reset;


endmodule : dmi_jtag_tap
