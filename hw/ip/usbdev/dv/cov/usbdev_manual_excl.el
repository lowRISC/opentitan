// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The following exclusions have been written and added manually on account of the dynamic behavior
// and understanding of the USB and USBDEV being unavailable to UNR tooling.

// Since the signal `ev_reset` is asserted only at the end of Reset Signaling, but the entry to
// reset also causes `ev_bus_active` to become asserted (since it too is a non-Idle bus state and
// `rx_idle_det_i` deasserts), the state transitions from LinkPoweredSuspended -> LinkPowered and
// LinkSuspended -> LinkResuming occur at the start of reset signaling.
// At the end of the reset, the FSM then transitions into LinkActiveNoSOF, but not directly.

CHECKSUM: "2422748304 1897192179"
INSTANCE: tb.dut.usbdev_impl.u_usbdev_linkstate
Fsm link_state_q "3407598795"
ANNOTATION: "Signal `ev_reset` is delayed relative to the signal `ev_bus_active` which also triggers."
Transition LinkPoweredSuspended->LinkActiveNoSOF "2->5"
ANNOTATION: "Signal `ev_reset` is delayed relative to the signal `ev_bus_active` which also triggers."
Transition LinkSuspended->LinkActiveNoSOF "4->5"
ANNOTATION: "Signal `ev_reset` is delayed relative to the signal `ev_bus_active` which also triggers."
Branch 1 "2905358650" "((!see_pwr_sense) || (!usb_pullup_en_i))" (7) "((!see_pwr_sense) || (!usb_pullup_en_i)) 0,LinkPoweredSuspended ,-,-,-,-,1,-,-,-,-,-,-,-,-"
ANNOTATION: "Signal `ev_reset` is delayed relative to the signal `ev_bus_active` which also triggers."
Branch 1 "2905358650" "((!see_pwr_sense) || (!usb_pullup_en_i))" (18) "((!see_pwr_sense) || (!usb_pullup_en_i)) 0,LinkSuspended ,-,-,-,-,-,-,-,-,-,-,-,1,-"
ANNOTATION: "rtl/usbdev_linkstate.sv, LineNumber: 169"
Block 23 "99569725" "link_state_d = LinkActiveNoSOF;"
ANNOTATION: "rtl/usbdev_linkstate.sv, LineNumber: 213"
Block 41 "3734498758" "link_resume_o = 1;"

// The detection of Reset Signaling during device transmission is prevented in `usbdev_linkstate`
// in case the PHY does not echo the transmission on the receiver inputs (see `line_se0_raw`).
CHECKSUM: "3366248665 3589209376"
INSTANCE: tb.dut.usbdev_impl.u_usb_fs_nb_pe.u_usb_fs_tx
Fsm out_state_q "1388066855"
ANNOTATION: "Link reset will not be detected whilst the DUT is transmitting."
Transition OsWaitByte->OsIdle "1->0"
Fsm state_q "1416230131"
ANNOTATION: "Link reset will not be detected whilst the DUT is transmitting."
Transition Sync->Idle "1->0"

// DUT does not write into a RX FIFO when it is full.
CHECKSUM: "1206032831 1104852947"
ANNOTATION: "ModuleName: usbdev_usbif"
INSTANCE: tb.dut.usbdev_impl
ANNOTATION: "DUT shall not write into full FIFO"
Condition 16 "3133442943" "(av_rvalid & (std_write_q | (((~out_max_used_q[PktW])) & (out_max_used_q[1:0] != 2'b11) & out_ep_acked))) 1 -1" (1 "01")

// DUT does not read from AVOut/AVSetup FIFO when it is empty.
CHECKSUM: "7115036 3660765074"
ANNOTATION: "ModuleName: prim_fifo_sync ( parameter Width=5,Pass=0,Depth=4,OutputZeroIfEmpty=0,Secure=0,DepthW=3,gen_normal_fifo.PtrW=2 + Width=5,Pass=0,Depth=8,OutputZeroIfEmpty=0,Secure=0,DepthW=4,gen_normal_fifo.PtrW=3 ) "
INSTANCE: tb.dut.usbdev_avsetupfifo
ANNOTATION: "DUT shall not read from empty FIFO"
Condition 4 "1324655787" "(rvalid_o & rready_i & ((~gen_normal_fifo.under_rst))) 1 -1" (1 "011")
CHECKSUM: "7115036 3660765074"
ANNOTATION: "ModuleName: prim_fifo_sync ( parameter Width=5,Pass=0,Depth=4,OutputZeroIfEmpty=0,Secure=0,DepthW=3,gen_normal_fifo.PtrW=2 + Width=5,Pass=0,Depth=8,OutputZeroIfEmpty=0,Secure=0,DepthW=4,gen_normal_fifo.PtrW=3 ) "
INSTANCE: tb.dut.usbdev_avoutfifo
ANNOTATION: "DUT shall not read from empty FIFO"
Condition 4 "1324655787" "(rvalid_o & rready_i & ((~gen_normal_fifo.under_rst))) 1 -1" (1 "011")
