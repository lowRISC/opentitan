// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface i2c_if ();
  // interface pins
  logic scl_i;
  logic scl_o;
  logic scl_en_o;
  logic sda_i;
  logic sda_o;
  logic sda_en_o;

  bit BusIsFree=1;

/*
  // debug signals (TBD)
  int            SclFrequency;
  int            SclClockPeriod;
  int            SclMinFreq;
  int            SclMaxFreq;
  bus_speed_e    BusSpeed;

  //Timing0
  int            SclHighMinHoldTime;
  int            SclLowMinHoldTime;
  //Timing1
  int            NormRiseTime;
  int            NormFallTime;
  //Timing2
  int            StartMinSetupTime;
  int            StartMinHoldTime;
  //Timing3
  int            DataMinSetupTime;
  int            DataMinHoldTime;
  //Timing4
  int            StopMinSetupTime;
  int            StartStopMinTime;
  //Timing5
  int            ClockStretchTimeout;
  int            ClockStretchEnable;

  function void set_set_bus_frequency(int SclFrequency_i);
    SclFrequency = SclFrequency_i; //in kHz
  if ( SclFrequency>0 && SclFrequency<=100 ) begin
    bus_speed_e = I2cStdSpeed;
    set_std_speed_timing();
  end else if (m_sclFrequency>100 && m_sclFrequency<=400) begin
    bus_speed_e = I2cFastSpeed;
    set_fast_speed_timing();
  end else if (m_sclFrequency>400 && m_sclFrequency<=3400) begin
    bus_speed_e = I2cFastSpeedPlus;
    set_fast_speed_plus_timing();
  end else
    `uvm_fatal("I2C:set_set_bus_frequency",
               $psprintf("SCL frquency setting illegal : %d kHz",SclFrequency))

  //Create a SCL with 1:1 duty cycle
  m_sclLowTime     = ( 10 ** 6/(2 * SclFrequency) ) ;   // ns
  m_sclHighTime    = m_sclLowTime;                      // ns
  //Default bit set-up time is m_sclLowTime/2
  m_sdaChangePoint = m_sclLowTime/2;                    // ns

  m_sclClockPeriod = ( (10**9)/m_sclFrequency) / 1000;  // ns

  endfunction

 always @(negedge sda_in )  begin
  //START condition
  if (rst==0)
   if (scl_in==1) begin
    #m_fHdStaMin;
    busIsFree<=0;
   end
 end
 always @(posedge sda_in) begin
  //STOP condition
  if (rst==0) begin
   if (scl_in==1) begin
    #m_tBufMin;
    busIsFree<=1;
   end
  end
 end
*/

endinterface : i2c_if
