// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_sleep_pin_mio_dio_val_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_sleep_pin_mio_dio_val_vseq)

  `uvm_object_new

  import chip_common_pkg::*;  // chip_io_e

  localparam int unsigned NumMioPads = top_earlgrey_pkg::MioPadCount;
  localparam int unsigned NumDioPads = top_earlgrey_pkg::DioCount;

  typedef enum bit [1:0] {
    Ret0,  // PAD driving 0 while in retention
    Ret1,  // PAD driving 1 while in retention
    HighZ, // PAD is input mode while in retention
    RetP   // PAD keeps the prev. value while in retention
  } pad_ret_t;

  pad_ret_t [NumMioPads-1:0] mio_pad_ret;
  pad_ret_t [NumDioPads-1:0] dio_pad_ret;

  virtual task cpu_init();
    super.cpu_init();
  endtask : cpu_init

  // SW sends chosen values via sw_logger_if. receive_chosen_value waits and
  // stores the values to the list.
  //
  // The transfer begins with "BEGIN Chosen Retention Types" and ends with
  // "END Chosen Retention Types".
  // In between, the data format is:
  //
  //   {M/D}IO [pad_num]: {0,1,2}
  //
  // For example, "MIO [14]: 2" indicates the MIO 14 will be configured as
  // High-Z mode in deep powerdown.
  task receive_chosen_values();
    string       printed_log;
    int unsigned idx;
    pad_ret_t    pad_type;

    `DV_WAIT(cfg.sw_logger_vif.printed_log == "BEGIN Chosen Retention Types")

    forever begin
      @(cfg.sw_logger_vif.printed_log_event);

      // Check if format matches
      printed_log = string'(cfg.sw_logger_vif.printed_log);

      // Check exit condition
      if (printed_log == "END Chosen Retention Types") break;

      case (printed_log.substr(0,4))

        "DIO [": begin
          idx      = cfg.sw_logger_vif.printed_arg[0];
          pad_type = pad_ret_t'(cfg.sw_logger_vif.printed_arg[1]);
          assert (cfg.sw_logger_vif.printed_arg[1] inside {[0:3]});

          dio_pad_ret[idx] = pad_type;
        end

        "MIO [": begin
          idx      = cfg.sw_logger_vif.printed_arg[0];
          pad_type = pad_ret_t'(cfg.sw_logger_vif.printed_arg[1]);
          assert (cfg.sw_logger_vif.printed_arg[1] inside {[0:3]});

          mio_pad_ret[idx] = pad_type;
        end

        default: begin
          `uvm_info(`gfn,
            $sformatf("Unexpected SW Log is received: %s", printed_log),
            UVM_LOW)
        end

      endcase

    end // forever

    // Print the received types
    `uvm_info(`gfn, $sformatf("BEGIN Received PAD Retention Types:"), UVM_LOW)
    foreach (dio_pad_ret[i]) begin
      `uvm_info(`gfn, $sformatf("  DIO [%d]: %d", i, dio_pad_ret[i]), UVM_LOW)
    end
    foreach (mio_pad_ret[i]) begin
      `uvm_info(`gfn, $sformatf("  MIO [%d]: %d", i, mio_pad_ret[i]), UVM_LOW)
    end
    `uvm_info(`gfn, $sformatf("END Received PAD Retention Types"), UVM_LOW)
  endtask : receive_chosen_values

  virtual task body();
    super.body();

    // TODO: Get expected MIO DIO value from SW
    fork
      receive_chosen_values();
    join_none

    // Release any driver interfaces.

    // Wait until Chip enters Low Power Mode
    wait (cfg.chip_vif.pwrmgr_low_power_if.low_power);

    // TODO: Sample the PADs and check with expected values

    // TODO: Fins out how to pass the test (maybe just $display()?)

  endtask : body

  virtual task post_start();
    super.post_start();
  endtask : post_start

endclass : chip_sw_sleep_pin_mio_dio_val_vseq
