// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_soc_proxy_gpio_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_soc_proxy_gpio_vseq)

  bit muxable_soc_gpis_mapped = 1'b0;
  bit muxable_soc_gpos_mapped = 1'b0;

  `uvm_object_new

  virtual task body();
    super.body();

    // Wait until we reach the SW test state.
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)

    // As it's hard to predict when during the execution of this vseq SW running on Ibex is done
    // with mapping the GPIs and GPOs, the tasks that monitor the SW log for GPI/GPO mapping
    // completion run in parallel to the test sequence.
    fork
      await_muxable_soc_gpis_mapped();
      await_muxable_soc_gpos_mapped();
      test_main();
    join

  endtask

  task test_main();
    test_dio_soc_gpis();
    test_dio_soc_gpos();
    test_mio_soc_gpis();
    send_external_irq();
    test_mio_soc_gpos();
  endtask

  task test_dio_soc_gpis();
    // Test directly mapped general-purpose inputs into SoC.
    for (int i = 0; i < soc_proxy_pkg::NumSocGpioMappedOnDio; i++) begin
      int unsigned pin = DioPadSocGpi0 + i;

      // Drive random pattern over multiple iterations.
      for (int iter = 0; iter < 10; iter++) begin
        bit exp_val = $urandom_range(0, 1);
        cfg.chip_vif.cpu_clk_rst_if.wait_clks($urandom_range(1, 100));
        `uvm_info(`gfn, $sformatf("Driving DIO pad for SoC GPI%0d to %0b.", i, exp_val), UVM_MEDIUM)
        cfg.chip_vif.dios_if.drive_pin(pin, exp_val);

        // Check that the signal appears at top_darjeeling's `soc_gpi_async_o` output.
        `DV_SPINWAIT_EXIT(
          // Wait thread: wait for correct value to appear.
          forever begin
            logic [soc_proxy_pkg::NumSocGpio-1:0] gpi;
            cfg.chip_vif.cpu_clk_rst_if.wait_clks(1);
            gpi = cfg.chip_vif.signal_probe_soc_gpi_async(.kind(dv_utils_pkg::SignalProbeSample));
            if (gpi[i] == exp_val) break;
          end
          ,
          // Exit thread: allow at most 100 CPU clock cycles until correct value.
          cfg.chip_vif.cpu_clk_rst_if.wait_clks(100);
          `dv_error("SoC GPI value did not appear within required time!")
        )

        // Release drive.
        cfg.chip_vif.dios_if.drive_en_pin(pin, 1'b0);
      end
    end
  endtask

  task test_dio_soc_gpos();
    // Test directly mapped general-purpose outputs from SoC with a random pattern over multiple
    // iterations.
    for (int iter = 0; iter < 10; iter++) begin
      bit [soc_proxy_pkg::NumSocGpio-1:0] gpo;
      bit [soc_proxy_pkg::NumSocGpioMappedOnDio-1:0] exp_val = $urandom();
      gpo[soc_proxy_pkg::NumSocGpioMappedOnDio-1:0] = exp_val;
      cfg.chip_vif.cpu_clk_rst_if.wait_clks($urandom_range(1, 100));
      `uvm_info(`gfn, $sformatf("Driving SoC GPOs to %0d'h%0x.",
                                soc_proxy_pkg::NumSocGpio,
                                gpo),
                UVM_MEDIUM)
      void'(cfg.chip_vif.signal_probe_soc_gpo_async(.kind(dv_utils_pkg::SignalProbeForce),
                                                    .value(gpo)));

      // Check that the signal appears at the DIOs.
      `DV_SPINWAIT_EXIT(
        // Wait thread: wait for correct values to appear.
        forever begin
          logic [top_darjeeling_pkg::DioPadCount-1:0] dios;
          cfg.chip_vif.cpu_clk_rst_if.wait_clks(1);
          dios = cfg.chip_vif.dios_if.sample();
          // if (dios[DioPadSocGpo0+soc_proxy_pkg::NumSocGpioMappedOnDio-1 : DioPadSocGpo0]
          //     == exp_val) break;
          if (dios[DioPadSocGpo0 +: soc_proxy_pkg::NumSocGpioMappedOnDio] == exp_val) break;
        end
        ,
        // Exit thread: allow at most 100 CPU clock cycles until correct value.
        cfg.chip_vif.cpu_clk_rst_if.wait_clks(100);
        `dv_error("DIO values did not appear within required time!")
      )

      // Release drive.
      void'(cfg.chip_vif.signal_probe_soc_gpo_async(.kind(dv_utils_pkg::SignalProbeRelease)));
    end
  endtask

  task test_mio_soc_gpis();
    // Wait until the CPU has mapped muxable GPIs in pinmux.
    `DV_WAIT(muxable_soc_gpis_mapped)

    // Test multiplexed general-purpose inputs into SoC.
    for (int i = 0; i < soc_proxy_pkg::NumSocGpioMuxed; i++) begin
      int unsigned pin = MioPadMio4 + i;

      // Drive random pattern over multiple iterations.
      for (int iter = 0; iter < 10; iter++) begin
        bit exp_val = $urandom_range(0, 1);
        cfg.chip_vif.cpu_clk_rst_if.wait_clks($urandom_range(1, 100));
        `uvm_info(`gfn, $sformatf("Driving MIO pad for %0d to %0b.", i, exp_val), UVM_MEDIUM)
        cfg.chip_vif.mios_if.drive_pin(pin, exp_val);

        // Check that the signal appears at top_darjeeling's `soc_gpi_async_o` output.
        `DV_SPINWAIT_EXIT(
          // Wait thread: wait for correct value to appear.
          forever begin
            logic [soc_proxy_pkg::NumSocGpio-1:0] gpi;
            cfg.chip_vif.cpu_clk_rst_if.wait_clks(1);
            gpi = cfg.chip_vif.signal_probe_soc_gpi_async(.kind(dv_utils_pkg::SignalProbeSample));
            if (gpi[i + soc_proxy_pkg::NumSocGpioMappedOnDio] == exp_val) break;
          end
          ,
          // Exit thread: allow at most 100 CPU clock cycles until correct value.
          cfg.chip_vif.cpu_clk_rst_if.wait_clks(100);
          `dv_error("SoC GPI value did not appear within required time!")
        )
      end

      // Release drive.
      cfg.chip_vif.mios_if.drive_en_pin(pin, 1'b0);
    end
  endtask

  task test_mio_soc_gpos();
    // Wait until the CPU has mapped muxable GPOs in pinmux.
    `DV_WAIT(muxable_soc_gpos_mapped)

    // Test multiplexed general-purpose outputs from SoC with a random pattern over multiple
    // iterations.
    for (int iter = 0; iter < 10; iter++) begin
      bit [soc_proxy_pkg::NumSocGpio-1:0] gpo;
      bit [soc_proxy_pkg::NumSocGpioMuxed-1:0] exp_val = $urandom();
      gpo[soc_proxy_pkg::NumSocGpio-1 -: soc_proxy_pkg::NumSocGpioMuxed] = exp_val;
      cfg.chip_vif.cpu_clk_rst_if.wait_clks($urandom_range(1, 100));
      `uvm_info(`gfn, $sformatf("Driving SoC GPOs to %0d'h%0x.",
                                soc_proxy_pkg::NumSocGpio,
                                gpo),
                UVM_MEDIUM)
      void'(cfg.chip_vif.signal_probe_soc_gpo_async(.kind(dv_utils_pkg::SignalProbeForce),
                                                    .value(gpo)));

      // Check that the signal appears at the MIOs.
      `DV_SPINWAIT_EXIT(
        // Wait thread: wait for correct values to appear.
        forever begin
          logic [top_darjeeling_pkg::MioPadCount-1:0] mios;
          cfg.chip_vif.cpu_clk_rst_if.wait_clks(1);
          mios = cfg.chip_vif.mios_if.sample();
          if (mios[MioPadMio4 +: soc_proxy_pkg::NumSocGpioMuxed] == exp_val) break;
        end
        ,
        // Exit thread: allow at most 100 CPU clock cycles until the correct value.
        cfg.chip_vif.cpu_clk_rst_if.wait_clks(100);
        `dv_error("MIO values did not appear within required time!")
      )

      // Release drive.
      void'(cfg.chip_vif.signal_probe_soc_gpo_async(.kind(dv_utils_pkg::SignalProbeRelease)));
    end
  endtask

  task send_external_irq();
    void'(cfg.chip_vif.signal_probe_soc_intr_async(.kind(dv_utils_pkg::SignalProbeForce),
                                             .value(1'b1)));
    cfg.chip_vif.cpu_clk_rst_if.wait_clks(100);
    void'(cfg.chip_vif.signal_probe_soc_intr_async(.kind(dv_utils_pkg::SignalProbeRelease)));
  endtask

  task await_muxable_soc_gpis_mapped();
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Muxable SoC GPIs mapped.")
    muxable_soc_gpis_mapped = 1'b1;
  endtask

  task await_muxable_soc_gpos_mapped();
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Muxable SoC GPOs mapped.")
    muxable_soc_gpos_mapped = 1'b1;
  endtask

endclass
