// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This package contains classes, parameters and functions related to the design
// and testing of oversampling-based I2C implementations.
//
package i2c_timing_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import i2c_pkg::*; // RTL pkg

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // Min/Max I2C timing parameters for different speed modes.
  // All constants below are lifted directly from Table 10 of the I2C spec.
  localparam time       TLOW_MINSTANDARD =  4.7us;
  localparam time     THDSTA_MINSTANDARD =    4us;
  localparam time     TSUSTA_MINSTANDARD =  4.7us;
  localparam time     THDDAT_MINSTANDARD =    0us;
  // localparam time     THDDAT_MINSTANDARD =    5us; // CBUS compatible controllers
  localparam time     TSUDAT_MINSTANDARD =  250ns;
  localparam time       TBUF_MINSTANDARD =  4.7us;
  localparam time     TSUSTO_MINSTANDARD =  4.0us;
  localparam time         TR_MINSTANDARD =   10ns; //
  localparam time         TF_MINSTANDARD =   10ns; //
  localparam time      THIGH_MINSTANDARD =    4us;

  localparam time       TLOW_MINFAST     =  1.3us;
  localparam time     THDSTA_MINFAST     =  0.6us;
  localparam time     TSUSTA_MINFAST     =  0.6us;
  localparam time     THDDAT_MINFAST     =    0ns;
  localparam time     TSUDAT_MINFAST     =  100ns;
  localparam time       TBUF_MINFAST     =  1.3us;
  localparam time     TSUSTO_MINFAST     =  0.6us;
  localparam time         TR_MINFAST     =   20ns; //
  localparam time         TF_MINFAST     =   10ns; // 20ns x (VDD / 5.5 V)
  localparam time      THIGH_MINFAST     =  0.6us;

  localparam time       TLOW_MINFASTPLUS =  0.5us;
  localparam time     THDSTA_MINFASTPLUS = 0.26us;
  localparam time     TSUSTA_MINFASTPLUS = 0.26us;
  localparam time     THDDAT_MINFASTPLUS =    0ns;
  localparam time     TSUDAT_MINFASTPLUS =   50ns;
  localparam time       TBUF_MINFASTPLUS =  0.5us;
  localparam time     TSUSTO_MINFASTPLUS = 0.26us;
  localparam time         TR_MINFASTPLUS =   10ns; //
  localparam time         TF_MINFASTPLUS =   10ns; // 20ns x (VDD / 5.5 V)
  localparam time      THIGH_MINFASTPLUS = 0.26us;

  localparam time         TR_MAXSTANDARD = 1000ns;
  localparam time         TF_MAXSTANDARD =  300ns;
  localparam time         TR_MAXFAST     =  300ns;
  localparam time         TF_MAXFAST     =  300ns;
  localparam time         TR_MAXFASTPLUS =  120ns;
  localparam time         TF_MAXFASTPLUS =  120ns;

  // The following macroized functions are used to create lookups for the above data.
  // @args
  // speed_mode: The I2C speed mode we wish to comply with, which defines the upper
  //             limit for SCL frequency.

  `ifndef I2C_GET_MIN_PARAM
  `define I2C_GET_MIN_PARAM(NAME_, PARAM_NAME_) \
    function time get_``NAME_``_min(speed_mode_e speed_mode); \
      case (speed_mode) inside \
        Standard : return (PARAM_NAME_``_MINSTANDARD); \
        Fast     : return (PARAM_NAME_``_MINFAST    ); \
        FastPlus : return (PARAM_NAME_``_MINFASTPLUS); \
      endcase \
    endfunction
  `endif

  `ifndef I2C_GET_MAX_PARAM
  `define I2C_GET_MAX_PARAM(NAME_, PARAM_NAME_) \
    function time get_``NAME_``_max(speed_mode_e speed_mode); \
      case (speed_mode) inside \
        Standard : return (PARAM_NAME_``_MAXSTANDARD); \
        Fast     : return (PARAM_NAME_``_MAXFAST    ); \
        FastPlus : return (PARAM_NAME_``_MAXFASTPLUS); \
      endcase \
    endfunction
  `endif

  `I2C_GET_MIN_PARAM(tlow, TLOW)
  `I2C_GET_MIN_PARAM(thdsta, THDSTA)
  `I2C_GET_MIN_PARAM(tsusta, TSUSTA)
  `I2C_GET_MIN_PARAM(thddat, THDDAT)
  `I2C_GET_MIN_PARAM(tsudat, TSUDAT)
  `I2C_GET_MIN_PARAM(tbuf, TBUF)
  `I2C_GET_MIN_PARAM(tsusto, TSUSTO)
  `I2C_GET_MIN_PARAM(tr, TR)
  `I2C_GET_MIN_PARAM(tf, TF)
  `I2C_GET_MIN_PARAM(thigh, THIGH)
  `I2C_GET_MAX_PARAM(tr, TR)
  `I2C_GET_MAX_PARAM(tf, TF)

  //////////////////////////
  // Absolute Time Delays //
  //////////////////////////
  typedef struct {
    time thigh;   // SCL high
    time tlow;    // SCL low
    time t_r;     // rise time
    time t_f;     // fall time
    time tsu_sta; // setup start
    time thd_sta; // hold start
    time tsu_dat; // setup data
    time thd_dat; // hold data
    time tsu_sto; // setup stop
    time t_buf;   // bus free time between P and S
  } abs_timing_cfg_t;

  typedef struct {
    abs_timing_cfg_t min;
    abs_timing_cfg_t max;
  } minmax_abs_timing_cfg_t;

  // In a synchronous system where we are deriving a slower bus clock
  // from a faster input clock, we typically use counters to create delays
  // from which the final output is derived. However, fractional-cycles do
  // not exist and we need to round the desired ratio up/down to an integer value.
  ///////////////////////////
  // Time Delays in Cycles //
  ///////////////////////////
  typedef struct {
    // Units are integer no. of (input) clock cycles
    rand bit [15:0] thigh;
    rand bit [15:0] tlow;
    rand bit [15:0] t_r;
    rand bit [15:0] t_f;
    rand bit [15:0] thd_sta;
    rand bit [15:0] tsu_sta;
    rand bit [15:0] tsu_sto;
    rand bit [15:0] tsu_dat;
    rand bit [15:0] thd_dat;
    rand bit [15:0] t_buf;
    rand bit        eTimeout;  // Timeout enable (CSR.TIMEOUT_CTRL.EN)
    rand bit [30:0] tTimeout;  // max time target may stretch the clock (CSR.TIMEOUT_CTRL.VAL)
  } cycles_timing_cfg_t;

  typedef struct    {
    cycles_timing_cfg_t min;
    cycles_timing_cfg_t max;
  } minmax_cycles_timing_cfg_t;

  ///////////////////////////////////
  // Derived Time Delays in Cycles //
  ///////////////////////////////////
  typedef struct {
    // Units are integer no. of (input) clock cycles
    bit [15:0] tSetupStart; // (t_r + tsu_sta)
    bit [15:0] tHoldStart;  // (t_f + thd_sta)
    bit [15:0] tSetupData;  // (t_r + tsu_dat)
    bit [15:0] tClockStart; // (thd_dat)
    bit [15:0] tClockLow;   // (t_low - thd_dat)
    bit [15:0] tClockPulse; // (t_r + thigh)
    bit [15:0] tClockHigh;  // (thigh)
    bit [15:0] tHoldBit;    // (t_f + thd_dat)
    bit [15:0] tClockStop;  // (t_f + tlow - thd_dat)
    bit [15:0] tSetupStop;  // (t_r + tsu_sto)
    bit [15:0] tHoldStop;   // (t_r + t_buf - tsu_sta)
    bit        eTimeOut; // en
    bit [30:0] tTimeOut;

    // tSetupStart  : The delay for SCL+SDA to release back to 1, plus the
    //                setup req for a start condition.
    // tHoldStart   : The delay for SDA to fall, plus it's hold req to makeup
    //                a valid start condition before driving SCL low.
    // tSetupData   : The delay from driving new data onto SDA until we allow
    //                the clock to be released (typically after ending stretching).
    // tClockStart  : The delay after the first negedge of SCL (after START)
    //                before we start driving SDA.
    // tClockLow    : The delay from driving SDA until we release SCL to create
    //                the next clock pulse.
    // tClockPulse  : The delay while SCL is high (and SDA holds it's current value).
    // tHoldBit     : The delay time where SDA must be stable after SCL
    //                falls at the end of a SCL pulse.
    // tClockStop   : The delay from the end of the ACK/NACK bit on SDA until
    //                the clock SCL is released high again before a stop condition.
    // tSetupStop   : The delay from SCL being released until SDA is also released
    //                to create a stop condition.
    // tHoldStop    : The delay from a SDA releasing as a stop condition until
    //                SDA can be pulled low again to create a START/RSTART.

    // Agent-Only Parameters //

    bit [31:0] tSetupBit; // aka. tSetupData

    // This variable holds the number of cycles the agent will stretch the clock in TARGET mode.
    rand uint tStretchHostClock;

    // Errors & Error Detection //

    // tSdaUnstable > 0 will cause SDA to glitch for this amount of time during 'tClockHigh'.
    // The 'sda_unstable' interrupt should be asserted if SDA glitches.
    uint tSdaUnstable;
    // If 'tSclInterference' is set to a non-zero value, create a glitch in SCL.
    // This is intended to stimulate the 'scl_interference' interrupt behaviour.
    uint tSclInterference;
    // If 'tSdaInterference' is set to a non-zero value, create a glitch in SDA.
    // This is intended to stimulate the 'sda_interference' interrupt behaviour.
    uint tSdaInterference;

  } timing_cfg_t;

  function static void print_time_property(cycles_timing_cfg_t tc);
    string str_timing_properties;
    string str_final;

    str_timing_properties = { // All values are in units of (input) clock cycles
      $sformatf("\nthigh     : %0d", tc.thigh),
      $sformatf("\ntlow      : %0d", tc.tlow),
      $sformatf("\nt_r       : %0d", tc.t_r),
      $sformatf("\nt_f       : %0d", tc.t_f),
      $sformatf("\nthd_sta   : %0d", tc.thd_sta),
      $sformatf("\ntsu_sta   : %0d", tc.thd_sta),
      $sformatf("\ntsu_sto   : %0d", tc.thd_sta),
      $sformatf("\ntsu_dat   : %0d", tc.thd_sta),
      $sformatf("\nthd_dat   : %0d", tc.thd_sta),
      $sformatf("\nt_buf     : %0d", tc.t_buf),
      $sformatf("\neTimeout  : %0d", tc.eTimeout),
      $sformatf("\ntTimeout  : %0d", tc.tTimeout)
    };

    str_final = {
      "\n-------------------------------------",
      "\ntiming_properties",
      str_timing_properties,
      "\n-------------------------------------"
    };
    `uvm_info("i2c_timing_pkg", str_final, UVM_LOW)
  endfunction

  function static void print_derived_time_property(timing_cfg_t dtc);
    string str_timing_properties, str_timing_errors;
    string str_final;

    str_timing_properties = { // All values are in units of (input) clock cycles
      // FSM Parameters
      $sformatf("\ntSetupStart       : %0d", dtc.tSetupStart),
      $sformatf("\ntHoldStart        : %0d", dtc.tHoldStart),
      $sformatf("\ntSetupData        : %0d", dtc.tSetupData),
      $sformatf("\ntClockStart       : %0d", dtc.tClockStart),
      $sformatf("\ntClockLow         : %0d", dtc.tClockLow),
      $sformatf("\ntClockPulse       : %0d", dtc.tClockPulse),
      $sformatf("\ntHoldBit          : %0d", dtc.tHoldBit),
      $sformatf("\ntClockStop        : %0d", dtc.tClockStop),
      $sformatf("\ntSetupStop        : %0d", dtc.tSetupStop),
      $sformatf("\ntHoldStop         : %0d", dtc.tHoldStop),
      $sformatf("\neTimeOut          : %0d", dtc.eTimeOut),
      $sformatf("\ntTimeOut          : %0d", dtc.tTimeOut),
      // Agent-Only Parameters
      $sformatf("\ntSetupBit         : %0d", dtc.tSetupBit),
      $sformatf("\ntStretchHostClock : %0d", dtc.tStretchHostClock)
    };
    str_timing_errors = {
    $sformatf("\ntSdaUnstable          : %0d", dtc.tSdaUnstable),
    $sformatf("\ntSclInterference      : %0d", dtc.tSclInterference),
    $sformatf("\ntSdaInterference      : %0d", dtc.tSdaInterference)
    };

    str_final = {
      "\n-------------------------------------",
      "\nderived_timing_properties",
      str_timing_properties,
      "\n-------------------------------------",
      "\ntiming_error_properties",
      str_timing_errors,
      "\n-------------------------------------"
    };
    `uvm_info("i2c_timing_pkg", str_final, UVM_LOW)
  endfunction

  // package sources
  `include "i2c_timing_cfg.sv"

endpackage: i2c_timing_pkg
