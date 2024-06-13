// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence tests the 'resume link active' functionality, in which the DUT requires
// software assistance to handle the power up condition when resuming from a Deep Sleep state.
class usbdev_resume_link_active_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_resume_link_active_vseq)

  `uvm_object_new

  virtual task body();
    uvm_reg_data_t enabled;

    // First disconnect VBUS and remove the pull up.
    set_vbus_state(0);
    usbdev_disconnect();

    // Just check that we're in the Disconnected state as expected.
    wait_for_link_state({LinkDisconnected}, 8);

    // Reinstate VBUS connection after a delay (visibility in waveforms).
    cfg.clk_rst_vif.wait_clks(1000);
    set_vbus_state(1);

    // When returning from Deep Sleep, the bus will be in Resume Signaling.
    fork
      begin
        // Just check that we're still in the Disconnected state; there should be no change at this
        // point because we have not yet asserted the pull up.
        wait_for_link_state({LinkDisconnected}, 200);

        // Now request connection.
        usbdev_connect();

        // The presence of VBUS and the pull up assertion should move the DUT into the Powered/
        // state.
        wait_for_link_state({LinkPowered}, 100);

        // Now prod the DUT into the Resuming state.
        ral.usbctrl.resume_link_active.set(1'b1);
        csr_update(ral.usbctrl);

        // This too should be almost immediate.
        wait_for_link_state({LinkResuming}, 8);
      end
      send_resume_signaling();
    join

    // At this point the DUT shall exit the Resuming state and move to Active(NoSOF) in
    // the usual manner in response to signaling on the USB; we have successfully resumed from
    // Deep Sleep.
    // This too should be almost immediate.
    wait_for_link_state({LinkActiveNoSOF}, 8);
  endtask

endclass : usbdev_resume_link_active_vseq
