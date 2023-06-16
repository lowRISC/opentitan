// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Thoroughly test the pin mux and pad attribute controls.
class chip_padctrl_attributes_vseq extends chip_stub_cpu_base_vseq;
  `uvm_object_utils(chip_padctrl_attributes_vseq)
  `uvm_object_new

  // Value to write for insel.
  typedef enum {
    InselZero,
    InselOne,
    InselPad
  } insel_value_e;

  // Value to write for outsel.
  typedef enum {
    OutselZero,
    OutselOne,
    OutselHighZ,
    OutselPad
  } outsel_value_e;

  localparam prim_pad_wrapper_pkg::pad_type_e DioPadType[DioCount] = '{
    prim_pad_wrapper_pkg::BidirStd, // DIO usbdev_usb_dp
    prim_pad_wrapper_pkg::BidirStd, // DIO usbdev_usb_dn
    prim_pad_wrapper_pkg::BidirStd, // DIO spi_host0_sd
    prim_pad_wrapper_pkg::BidirStd, // DIO spi_host0_sd
    prim_pad_wrapper_pkg::BidirStd, // DIO spi_host0_sd
    prim_pad_wrapper_pkg::BidirStd, // DIO spi_host0_sd
    prim_pad_wrapper_pkg::BidirStd, // DIO spi_device_sd
    prim_pad_wrapper_pkg::BidirStd, // DIO spi_device_sd
    prim_pad_wrapper_pkg::BidirStd, // DIO spi_device_sd
    prim_pad_wrapper_pkg::BidirStd, // DIO spi_device_sd
    prim_pad_wrapper_pkg::BidirOd,  // DIO sysrst_ctrl_aon_ec_rst_l
    prim_pad_wrapper_pkg::BidirOd,  // DIO sysrst_ctrl_aon_flash_wp_l
    prim_pad_wrapper_pkg::InputStd, // DIO spi_device_sck
    prim_pad_wrapper_pkg::InputStd, // DIO spi_device_csb
    prim_pad_wrapper_pkg::BidirStd, // DIO spi_host0_sck
    prim_pad_wrapper_pkg::BidirStd  // DIO spi_host0_csb
  };

  int dio_input_pads[$];

  // For pad attributes testing.
  //
  // The following attributes are not supported:
  // - od_en
  // - slew_rate
  // - schmitt_en
  // - keep_en
  // - drive_strength[3:1]
  //
  // The following attributes are supported for bi-directional pads:
  // - invert
  // - drive_strength[0] (0: pull, 1: strong)
  // - virt_od_en
  // - pull_en (0: hiz, 1: weak)
  // - pull_select
  //
  // The following attributes are supported for input-only pads:
  // - invert
  rand prim_pad_wrapper_pkg::pad_attr_t mio_pad_attr[MioPadCount];
  rand prim_pad_wrapper_pkg::pad_attr_t dio_pad_attr[DioCount];

  // For MIO pinmux testing.
  //
  // Driving out of the chip:
  //   There are MioOutCount signals that can be driven to MioPadCount number of MIO pads. There are
  //   thus, MioPadCount number of outsel registers. Randomly pick MioPadCount number of signals and
  //   map them onto each pad in the outsel direction.
  rand logic [MioOutCount-1:0]  periph_to_mio;
  rand logic [MioOutCount-1:0]  periph_to_mio_oe;
  rand mio_out_e                periph_to_mio_map[MioPadCount];
  rand outsel_value_e           outsel_value_kind[MioPadCount];

  constraint periph_to_mio_oe_c {
    // Favor oe = 1 over 0 70% of the time.
    foreach (periph_to_mio_oe[i]) {
      periph_to_mio_oe[i] dist {1 :/ 7, 0 :/ 3};
    }
  }

  constraint periph_to_mio_pad_map_c {
    unique {periph_to_mio_map};
    foreach (periph_to_mio_map[i]) {
      periph_to_mio_map[i] != MioOutCount;
    }
  }

  constraint outsel_value_kind_c {
    solve mio_pad_attr before outsel_value_kind;
    foreach (outsel_value_kind[i]) {
      outsel_value_kind[i] dist {OutselZero :/ 1, OutselOne :/ 2, OutselHighZ :/ 2, OutselPad :/ 5};
      // Pick Hi-Z only if pull_en is asserted. Otherwise, assertion errors may get thrown.
      if (!mio_pad_attr[i].pull_en) outsel_value_kind[i] != OutselHighZ;
    }
  }

  // Driving into the chip:
  //
  //   There are MioPadCount pads that can be driven externally and forwarded to any of the
  //   MioInCount core/peripheral facing signals inside the chip. Randomly map the pads to each
  //   peripheral input. Pads may be duplicated to more than one peripheral input.
  rand logic [MioPadCount-1:0]  mio_to_periph;
  rand logic [MioPadCount-1:0]  mio_to_periph_oe;
  rand mio_pad_e                mio_to_periph_map[MioInCount];
  rand insel_value_e            insel_value_kind[MioInCount];

  constraint mio_to_periph_oe_c {
    solve mio_pad_attr before mio_to_periph_oe;
    // Favor oe = 1 over 0 70% of the time, but only if pull is enabled (so that the peripherals do
    // not see Xs).
    foreach (mio_to_periph_oe[i]) {
      if (mio_pad_attr[i].pull_en) {
        mio_to_periph_oe[i] dist {1 :/ 7, 0 :/ 3};
      } else {
        mio_to_periph_oe[i] == 1;
      }
    }
  }

  constraint mio_to_periph_map_c {
    foreach (mio_to_periph_map[i]) {
      mio_to_periph_map[i] != MioPadCount;
    }
  }

  constraint insel_value_kind_c {
    foreach (insel_value_kind[i]) {
      insel_value_kind[i] dist {InselZero :/ 2, InselOne :/ 2, InselPad :/ 6};
    }
  }

  // For DIO pinmux testing.
  //
  // Pads are either analog, input only or bidirectional. For bdirectional, only drive either the
  // pad or the periph input. If none are driven, then on the pull. For input only, drive the periph
  // randomly - it should have no effect.
  rand logic [DioCount-1:0]  dio_to_periph;
  rand logic [DioCount-1:0]  dio_to_periph_oe;
  rand logic [DioCount-1:0]  periph_to_dio;
  rand logic [DioCount-1:0]  periph_to_dio_oe;

  // Either only drive the pad or the periph input for bidirectional pads.
  constraint periph_to_dio_oe_c {
    solve dio_pad_attr before dio_to_periph_oe;
    solve dio_pad_attr before periph_to_dio_oe;
    solve dio_to_periph_oe before periph_to_dio_oe;
    foreach (periph_to_dio_oe[i]) {
      if (DioPadType[i] != prim_pad_wrapper_pkg::InputStd) {
        if (dio_pad_attr[i].pull_en) {
          !(dio_to_periph_oe[i] && periph_to_dio_oe[i]);
        } else {
          dio_to_periph_oe[i] ^ periph_to_dio_oe[i];
        }
      } else {
        if (!dio_pad_attr[i].pull_en) {
          dio_to_periph_oe[i] == 1;
        }
      }
    }
  }

  virtual task body();
    // The chip_padctrl_attributes test verifies the input / output connections of the pads to
    // peripherals and fully verifies all pad attributes. In doing so, Xs may end up propagating
    // into the peripheral. We hence, disable SVAs in these blocks while the test is running.
    cfg.chip_vif.chip_padctrl_attributes_test_sva_disable = 1;

    // Remove default pulls on these interfaces.
    cfg.chip_vif.tap_straps_if.disconnect();
    cfg.chip_vif.mios_if.disconnect();

    foreach (DioPadType[i]) begin
      if (DioPadType[i] == prim_pad_wrapper_pkg::InputStd) dio_input_pads.push_back(i);
    end

    fork
      begin : mio_test
        pinmux_mio_outsel_test();
        cfg.chip_vif.io_div4_clk_rst_if.wait_clks($urandom_range(1, 20));
        pinmux_mio_outsel_reset();

        pinmux_mio_insel_test();
        cfg.chip_vif.io_div4_clk_rst_if.wait_clks($urandom_range(1, 20));
        pinmux_mio_insel_reset();
      end : mio_test
      // Note: this tests the USB DIOs as well, even though they are marked as "manual" in the
      // Hjson. They are only marked as "manual" so that custom connections can be implemented for
      // the FPGA target. For the ASIC target, these DIOs are connected to the padring in the same
      // way as regular DIOs.
      begin : dio_test
        bit enable_spi_host_save = cfg.chip_vif.enable_spi_host;
        cfg.chip_vif.cfg_default_weak_pulls_on_dios(0);
        cfg.chip_vif.enable_spi_host = 0;
        pinmux_dio_test();
        cfg.chip_vif.enable_spi_host = enable_spi_host_save;
        cfg.chip_vif.dios_if.disconnect();
        cfg.chip_vif.cfg_default_weak_pulls_on_dios(1);
      end : dio_test
      // Note: "manual" DIOs other than the USB ones mentioned above are not connected to the pinmux
      // and their pad attributes are tied off. We only perform a rudimentary pull-up/down/high-z
      // here since these signals do not have any effect in the open-source (these DIOs are
      // connected to closed source functionality and hence tested elsewhere in the closed source
      // DV environment). The POR_N pin is not tested here since that one is tested implicitly by
      // all tests asserting a reset.
      begin : manual_dio_test
        // Make sure nothing drives these pins before testing the pull values.
        cfg.chip_vif.ast_misc_if.disconnect();
        cfg.chip_vif.otp_ext_volt_if.disconnect();
        cfg.chip_vif.flash_test_mode_if.disconnect();
        cfg.chip_vif.flash_test_volt_if.disconnect();
        cfg.chip_vif.cc_if.disconnect();
        cfg.chip_vif.io_div4_clk_rst_if.wait_clks(1);
        check_manual_dios_pull();
      end : manual_dio_test
    join

    void'(cfg.chip_vif.signal_probe_pinmux_periph_to_mio_oe_i(SignalProbeRelease));
    void'(cfg.chip_vif.signal_probe_pinmux_periph_to_mio_i(SignalProbeRelease));
    void'(cfg.chip_vif.signal_probe_pinmux_periph_to_dio_oe_i(SignalProbeRelease));
    void'(cfg.chip_vif.signal_probe_pinmux_periph_to_dio_i_11_0(SignalProbeRelease));
    void'(cfg.chip_vif.signal_probe_pinmux_periph_to_dio_i_15_14(SignalProbeRelease));
    cfg.chip_vif.mios_if.disconnect();

    // Reset the DUT before reenabling the assertions.
    dut_init();
    cfg.chip_vif.chip_padctrl_attributes_test_sva_disable = 0;
  endtask : body

  // Test the pinmux outsel functionality with pad attributes.
  task pinmux_mio_outsel_test();
    int iterations;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(iterations, iterations inside {[5:20]};)
    for (int i = 1; i <= iterations; i++) begin
      `uvm_info(`gfn, $sformatf("pinmux_outsel_test %0d/%0d", i, iterations), UVM_LOW)
      pinmux_mio_pad_attr_config();
      pinmux_mio_outsel_config();
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(periph_to_mio_oe)
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(periph_to_mio)
      void'(cfg.chip_vif.signal_probe_pinmux_periph_to_mio_oe_i(SignalProbeForce,
                                                                periph_to_mio_oe));
      void'(cfg.chip_vif.signal_probe_pinmux_periph_to_mio_i(SignalProbeForce, periph_to_mio));
      repeat ($urandom_range(4, 20)) begin
        cfg.chip_vif.io_div4_clk_rst_if.wait_clks($urandom_range(1, 20));
        randcase
          1: begin
            `DV_CHECK_MEMBER_RANDOMIZE_FATAL(periph_to_mio_oe)
            void'(cfg.chip_vif.signal_probe_pinmux_periph_to_mio_oe_i(SignalProbeForce,
                                                                      periph_to_mio_oe));
          end
          1: begin
            `DV_CHECK_MEMBER_RANDOMIZE_FATAL(periph_to_mio)
            void'(cfg.chip_vif.signal_probe_pinmux_periph_to_mio_i(SignalProbeForce, periph_to_mio));
          end
        endcase
        cfg.chip_vif.io_div4_clk_rst_if.wait_clks(1);
        #(cfg.pad_pull_delay * 1ns);
        pinmux_mio_outsel_checks();
      end
    end
    // Restore the MIO pad attributes to default.
    pinmux_mio_pad_attr_reset();
  endtask

  // Program the MIO pad attr registers based on the values randomized.
  task pinmux_mio_pad_attr_config();
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(mio_pad_attr)
    for (int i = 0; i < MioPadCount; i++) begin
      uvm_reg_data_t value = '0;
      value = get_csr_val_with_updated_field(ral.pinmux_aon.mio_pad_attr[i].invert, value,
                                             mio_pad_attr[i].invert);
      value = get_csr_val_with_updated_field(ral.pinmux_aon.mio_pad_attr[i].virtual_od_en, value,
                                             mio_pad_attr[i].virt_od_en);
      value = get_csr_val_with_updated_field(ral.pinmux_aon.mio_pad_attr[i].pull_en, value,
                                             mio_pad_attr[i].pull_en);
      value = get_csr_val_with_updated_field(ral.pinmux_aon.mio_pad_attr[i].pull_select, value,
                                             mio_pad_attr[i].pull_select);
      value = get_csr_val_with_updated_field(ral.pinmux_aon.mio_pad_attr[i].keeper_en, value,
                                             mio_pad_attr[i].keep_en);
      value = get_csr_val_with_updated_field(ral.pinmux_aon.mio_pad_attr[i].schmitt_en, value,
                                             mio_pad_attr[i].schmitt_en);
      value = get_csr_val_with_updated_field(ral.pinmux_aon.mio_pad_attr[i].od_en, value,
                                             mio_pad_attr[i].od_en);
      value = get_csr_val_with_updated_field(ral.pinmux_aon.mio_pad_attr[i].slew_rate, value,
                                             mio_pad_attr[i].slew_rate);
      value = get_csr_val_with_updated_field(ral.pinmux_aon.mio_pad_attr[i].drive_strength, value,
                                             mio_pad_attr[i].drive_strength);
      `uvm_info(`gfn, $sformatf("%0d: mio_pad_attr = %0p / 0x%0h", i, mio_pad_attr[i], value),
                UVM_LOW)
      csr_wr(.ptr(ral.pinmux_aon.mio_pad_attr[i]), .value(value), .blocking(1), .predict(1));
    end
  endtask

  // Reset the MIO pad attr registers.
  task pinmux_mio_pad_attr_reset();
    for (int i = 0; i < MioPadCount; i++) begin
      uvm_reg_data_t value = ral.pinmux_aon.mio_pad_attr[i].get_reset();
      csr_wr(.ptr(ral.pinmux_aon.mio_pad_attr[i]), .value(value), .blocking(1), .predict(1));
    end
  endtask

  // Program the MIO outsel registers based on the values randomized.
  task pinmux_mio_outsel_config();
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(periph_to_mio_map)
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(outsel_value_kind)
    for (int i = 0; i < MioPadCount; i++) begin
      uvm_reg_data_t value = int'(outsel_value_kind[i]);
      if (outsel_value_kind[i] == OutselPad) begin
        value += periph_to_mio_map[i];
      end
      `uvm_info(`gfn, $sformatf("%0d: outsel_value_kind = %0s, periph_to_mio_map = %0s",
                                i, outsel_value_kind[i].name(), periph_to_mio_map[i].name()),
                UVM_LOW)
      csr_wr(.ptr(ral.pinmux_aon.mio_outsel[i].out), .value(value), .blocking(1), .predict(1));
    end
  endtask

  // Reset the MIO outsel registers.
  task pinmux_mio_outsel_reset();
    for (int i = 0; i < MioPadCount; i++) begin
      uvm_reg_data_t value = ral.pinmux_aon.mio_outsel[i].out.get_reset();
      csr_wr(.ptr(ral.pinmux_aon.mio_outsel[i].out), .value(value), .blocking(1), .predict(1));
    end
  endtask

  // Verifies the MIO pad value against the periph out value for the outsel test.
  function void pinmux_mio_outsel_checks();
    for (int i = 0; i < MioPadCount; i++) begin
      string msg = $sformatf("on MIO[%0d]", i);
      logic exp_oe, exp_out;
      string exp_strength, obs_strength;

      case (outsel_value_kind[i])
        OutselZero: begin
          exp_out = 0;
          exp_oe = 1;
        end
        OutselOne: begin
          exp_out = 1;
          exp_oe = 1;
        end
        OutselHighZ: begin
          exp_out = 0;
          exp_oe = 0;
        end
        OutselPad: begin
          exp_out = periph_to_mio[periph_to_mio_map[i]];
          exp_oe = periph_to_mio_oe[periph_to_mio_map[i]];
        end
        default: ;
      endcase
      if (mio_pad_attr[i].invert && exp_out !== 1'bz && exp_oe) exp_out = ~exp_out;
      // If virtual open drain is enabled, then the pad is driven to 0 if out is 0, else hi-z.
      if (mio_pad_attr[i].virt_od_en && exp_out && exp_oe) exp_oe = 0;
      if (mio_pad_attr[i].od_en && exp_out && exp_oe && cfg.is_mio_open_drain(i) == 1)
        exp_oe = 0;
      obs_strength = $sformatf("%v", cfg.chip_vif.mios_if.pins[i]);
      if (exp_oe && exp_out !== 1'bz) begin
        exp_strength = {mio_pad_attr[i].drive_strength[0] ? "St" : "Pu", $sformatf("%0d", exp_out)};
        `DV_CHECK_EQ(exp_out, cfg.chip_vif.mios_if.pins[i], msg)
        `DV_CHECK_STREQ(exp_strength, obs_strength, msg)
      end else begin
        if (mio_pad_attr[i].pull_en) begin
          exp_strength = $sformatf("We%0d", mio_pad_attr[i].pull_select);
          `DV_CHECK_EQ(mio_pad_attr[i].pull_select, cfg.chip_vif.mios_if.pins[i], msg)
          `DV_CHECK_STREQ(exp_strength, obs_strength, msg)
        end else begin
          `DV_CHECK_CASE_EQ(cfg.chip_vif.mios_if.pins[i], 1'bz, msg)
          `DV_CHECK_STREQ(obs_strength, "HiZ", msg)
        end
      end
    end
  endfunction

  // Test the pinmux insel functionality with pad attributes.
  task pinmux_mio_insel_test();
    int iterations;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(iterations, iterations inside {[5:20]};)
    for (int i = 1; i <= iterations; i++) begin
      `uvm_info(`gfn, $sformatf("pinmux_insel_test %0d/%0d", i, iterations), UVM_LOW)
      pinmux_mio_pad_attr_config();
      pinmux_mio_insel_config();
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(mio_to_periph_oe)
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(mio_to_periph)
      cfg.chip_vif.mios_if.pins_oe = mio_to_periph_oe;
      cfg.chip_vif.mios_if.pins_o = mio_to_periph;
      repeat ($urandom_range(4, 20)) begin
        cfg.chip_vif.io_div4_clk_rst_if.wait_clks($urandom_range(1, 20));
        randcase
          1: begin
            `DV_CHECK_MEMBER_RANDOMIZE_FATAL(mio_to_periph)
            cfg.chip_vif.mios_if.pins_o = mio_to_periph;
          end
          1: begin
            `DV_CHECK_MEMBER_RANDOMIZE_FATAL(mio_to_periph_oe)
            cfg.chip_vif.mios_if.pins_oe = mio_to_periph_oe;
          end
        endcase
        cfg.chip_vif.io_div4_clk_rst_if.wait_clks(1);
        pinmux_mio_insel_checks();
      end
    end
    // Restore the MIO pad attributes to default.
    pinmux_mio_pad_attr_reset();
  endtask

  // Program the MIO insel registers based on the values randomized.
  task pinmux_mio_insel_config();
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(mio_to_periph_map)
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(insel_value_kind)
    for (int i = 0; i < MioInCount; i++) begin
      uvm_reg_data_t value = int'(insel_value_kind[i]);
      if (insel_value_kind[i] == InselPad) begin
        value += mio_to_periph_map[i];
      end
      `uvm_info(`gfn, $sformatf("%0d: insel_value_kind = %0s, mio_to_periph_map = %0s",
                                i, insel_value_kind[i].name(), mio_to_periph_map[i].name()),
                UVM_LOW)
      csr_wr(.ptr(ral.pinmux_aon.mio_periph_insel[i].in), .value(value), .blocking(1), .predict(1));
    end
  endtask

  // Reset the MIO insel registers.
  task pinmux_mio_insel_reset();
    for (int i = 0; i < MioInCount; i++) begin
      uvm_reg_data_t value = ral.pinmux_aon.mio_periph_insel[i].in.get_reset();
      csr_wr(.ptr(ral.pinmux_aon.mio_periph_insel[i].in), .value(value), .blocking(1), .predict(1));
    end
  endtask

  // Verifies the MIO periph value against the pad input value for the insel test.
  function void pinmux_mio_insel_checks();
    for (int i = 0; i < MioInCount; i++) begin
      string msg = $sformatf("on MIO_IN[%0d]", i);
      mio_pad_e pad = mio_to_periph_map[i];
      logic act_in, exp_in;

      act_in = cfg.chip_vif.mio_to_periph[i];
      case (insel_value_kind[i])
        InselZero:  exp_in = 0;
        InselOne:   exp_in = 1;
        InselPad: begin
          exp_in = cfg.chip_vif.mios_if.pins[pad];
          if (mio_pad_attr[pad].invert && exp_in !== 1'bz) exp_in = ~exp_in;
          if (exp_in === 1'bz && mio_pad_attr[i].pull_en) exp_in = mio_pad_attr[i].pull_select;
        end
        default: ;
      endcase
      `DV_CHECK_CASE_EQ(exp_in, act_in, msg)
    end
  endfunction

  // Test the DIO pad attributes for both directions.
  task pinmux_dio_test();
    int iterations;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(iterations, iterations inside {[5:20]};)
     // Sanitize the inputs at the start of the test.
     foreach (dio_to_periph_oe[i]) begin
       if (DioPadType[i] == prim_pad_wrapper_pkg::InputStd) dio_to_periph_oe[i] = 1;
     end
     pinmux_dio_drive_inputs();
     for (int i = 1; i <= iterations; i++) begin
      `uvm_info(`gfn, $sformatf("pinmux_dio_test %0d/%0d", i, iterations), UVM_LOW)
      pinmux_dio_pad_attr_config();
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dio_to_periph_oe)
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(periph_to_dio_oe)
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dio_to_periph)
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(periph_to_dio)
      pinmux_dio_drive_inputs();
      repeat ($urandom_range(4, 20)) begin
        cfg.chip_vif.io_div4_clk_rst_if.wait_clks($urandom_range(1, 20));
        randcase
          1: `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dio_to_periph)
          1: `DV_CHECK_MEMBER_RANDOMIZE_FATAL(periph_to_dio)
          1: `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dio_to_periph_oe)
          1: `DV_CHECK_MEMBER_RANDOMIZE_FATAL(periph_to_dio_oe)
        endcase
        pinmux_dio_drive_inputs();
        cfg.chip_vif.io_div4_clk_rst_if.wait_clks(1);
        #(cfg.pad_pull_delay * 1ns);
        pinmux_dio_insel_checks();
      end
    end
    // Restore the DIO pad attributes to default.
    pinmux_dio_pad_attr_reset();
  endtask

  // Program the DIO pad attr registers based on the values randomized.
  task pinmux_dio_pad_attr_config();
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dio_pad_attr)
    for (int i = 0; i < DioCount; i++) begin
      uvm_reg_data_t value = '0;
      value = get_csr_val_with_updated_field(ral.pinmux_aon.dio_pad_attr[i].invert, value,
                                             dio_pad_attr[i].invert);
      value = get_csr_val_with_updated_field(ral.pinmux_aon.dio_pad_attr[i].virtual_od_en, value,
                                             dio_pad_attr[i].virt_od_en);
      value = get_csr_val_with_updated_field(ral.pinmux_aon.dio_pad_attr[i].pull_en, value,
                                             dio_pad_attr[i].pull_en);
      value = get_csr_val_with_updated_field(ral.pinmux_aon.dio_pad_attr[i].pull_select, value,
                                             dio_pad_attr[i].pull_select);
      value = get_csr_val_with_updated_field(ral.pinmux_aon.dio_pad_attr[i].keeper_en, value,
                                             dio_pad_attr[i].keep_en);
      value = get_csr_val_with_updated_field(ral.pinmux_aon.dio_pad_attr[i].schmitt_en, value,
                                             dio_pad_attr[i].schmitt_en);
      value = get_csr_val_with_updated_field(ral.pinmux_aon.dio_pad_attr[i].od_en, value,
                                             dio_pad_attr[i].od_en);
      value = get_csr_val_with_updated_field(ral.pinmux_aon.dio_pad_attr[i].slew_rate, value,
                                             dio_pad_attr[i].slew_rate);
      value = get_csr_val_with_updated_field(ral.pinmux_aon.dio_pad_attr[i].drive_strength, value,
                                             dio_pad_attr[i].drive_strength);
      `uvm_info(`gfn, $sformatf("%0d: dio_pad_attr = %0p / 0x%0h", i, dio_pad_attr[i], value),
                UVM_LOW)
      csr_wr(.ptr(ral.pinmux_aon.dio_pad_attr[i]), .value(value), .blocking(1), .predict(1));
    end
  endtask

  function void pinmux_dio_drive_inputs();
    cfg.chip_vif.dios_if.pins_oe = '0;
    void'(cfg.chip_vif.signal_probe_pinmux_periph_to_dio_i_11_0(SignalProbeForce,
                                                                periph_to_dio[11:0]));
    void'(cfg.chip_vif.signal_probe_pinmux_periph_to_dio_i_15_14(SignalProbeForce,
                                                                 periph_to_dio[15:14]));
    void'(cfg.chip_vif.signal_probe_pinmux_periph_to_dio_oe_i(SignalProbeForce, periph_to_dio_oe));
    for (int i = 0; i < DioCount; i++) begin
      cfg.chip_vif.dios_if.pins_oe[DioToDioPadMap[i]] = dio_to_periph_oe[i];
      cfg.chip_vif.dios_if.pins_o[DioToDioPadMap[i]] = dio_to_periph[i];
    end
  endfunction

  // Reset the DIO pad attr registers.
  task pinmux_dio_pad_attr_reset();
    for (int i = 0; i < DioCount; i++) begin
      uvm_reg_data_t value = ral.pinmux_aon.dio_pad_attr[i].get_reset();
      csr_wr(.ptr(ral.pinmux_aon.dio_pad_attr[i]), .value(value), .blocking(1), .predict(1));
    end
  endtask

  // Check both, the DIO pad and DIO periph value based on what is driven and the pad attributes.
  function void pinmux_dio_insel_checks();
    for (int i = 0; i < DioCount; i++) begin
      string msg = $sformatf("on DIO[%0d]", i);
      if (DioPadType[i] == prim_pad_wrapper_pkg::InputStd) begin
        logic exp;
        // periph_to_dio_oe / periph_to_dio_o have no effect.
        if (dio_to_periph_oe[i]) exp = dio_to_periph[i];
        else begin
          `DV_CHECK(dio_pad_attr[i].pull_en)
          exp = dio_pad_attr[i].pull_select;
        end
        if (dio_pad_attr[i].invert) exp = ~exp;
        `DV_CHECK_CASE_EQ(exp, cfg.chip_vif.dio_to_periph[i], msg)
      end else begin
        logic exp, exp_in, exp_out;
        case ({periph_to_dio_oe[i], dio_to_periph_oe[i]})
          2'b00: begin
            `DV_CHECK(dio_pad_attr[i].pull_en)
            exp = dio_pad_attr[i].pull_select;
            exp_in = exp;
            exp_out = exp;
          end
          2'b01: begin
            exp = dio_to_periph[i];
            exp_in = exp;
            exp_out = exp;
          end
          2'b10: begin
            exp = periph_to_dio[i];
            exp_out = exp;
            if (dio_pad_attr[i].invert) exp_out = ~exp_out;
            if (dio_pad_attr[i].virt_od_en && exp_out) exp_out = 1'bz;
            if (dio_pad_attr[i].od_en && exp_out && cfg.is_dio_open_drain(DioToDioPadMap[i]))
              exp_out = 1'bz;
            if (exp_out === 1'bz && dio_pad_attr[i].pull_en) exp_out = dio_pad_attr[i].pull_select;
            exp_in = exp_out;
            if (exp_in === 1'bz) exp_in = 1'bx;  // Undriven input treated as x.
          end
          2'b11: begin
            `DV_CHECK_FATAL(0, "Tricky, unsupported stimulus")
            continue;
          end
          default: ;
        endcase
        if (dio_pad_attr[i].invert) exp_in = ~exp_in;
        `DV_CHECK_CASE_EQ(exp_in, cfg.chip_vif.dio_to_periph[i], msg)
        `DV_CHECK_CASE_EQ(exp_out, cfg.chip_vif.dios_if.pins[DioToDioPadMap[i]], msg)
      end
    end
  endfunction

  task check_manual_dios_pull();
    string obs_strength;
    obs_strength = $sformatf("%v", cfg.chip_vif.ast_misc_if.pins[0]);
    `DV_CHECK_STREQ(obs_strength, "We0", "on AST_MISC")
    obs_strength = $sformatf("%v", cfg.chip_vif.otp_ext_volt_if.pins[0]);
    `DV_CHECK_STREQ(obs_strength, "HiZ", "on OTP_EXT_VOLT")
    obs_strength = $sformatf("%v", cfg.chip_vif.flash_test_mode_if.pins[0]);
    `DV_CHECK_STREQ(obs_strength, "HiZ", "on FLASH_TEST_MODE0")
    obs_strength = $sformatf("%v", cfg.chip_vif.flash_test_mode_if.pins[0]);
    `DV_CHECK_STREQ(obs_strength, "HiZ", "on FLASH_TEST_MODE1")
    obs_strength = $sformatf("%v", cfg.chip_vif.flash_test_volt_if.pins[0]);
    `DV_CHECK_STREQ(obs_strength, "HiZ", "on FLASH_TEST_VOLT")
    obs_strength = $sformatf("%v", cfg.chip_vif.cc_if.pins[0]);
    `DV_CHECK_STREQ(obs_strength, "HiZ", "on CC1")
    obs_strength = $sformatf("%v", cfg.chip_vif.cc_if.pins[1]);
    `DV_CHECK_STREQ(obs_strength, "HiZ", "on CC2")
  endtask

endclass
