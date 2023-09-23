// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
interface usb20_if (
  input clk, 
  input rst,
  output wire usb_vbus,
  inout wire usb_Dp,
  inout wire usb_Dn
);

	// Data Inputs pins
	logic usb_dp_i;
	logic usb_dn_i;
	logic usb_rx_d_i;
	// Data Outputs pins
	logic usb_dp_o;
	logic usb_dp_en_o;
	logic usb_dn_o;
	logic usb_dn_en_o;
	logic usb_tx_se0_o;
	logic usb_tx_d_o;

	// Non-data pins
	logic usb_sense_i;          // indicates the presence of VBUS from Host
	logic usb_dp_pullup_o ;
	logic usb_dn_pullup_o ;
	logic usb_rx_enable_o;
	logic usb_tx_use_d_se0_o;
        

        
	assign usb_sense_i = usb_vbus;

	assign usb_dp_i = usb_Dp;
	assign usb_dn_i = usb_Dn;
	
	assign usb_Dp = usb_dp_en_o ? usb_dp_o : 1'bz;
	assign usb_Dn = usb_dn_en_o ? usb_dn_o : 1'bz;	

 clocking cb@(posedge clk);
 
 endclocking


endinterface
