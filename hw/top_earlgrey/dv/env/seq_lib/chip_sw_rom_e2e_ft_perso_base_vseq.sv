// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Base-sequence for functionality related to simulation of the 'personalization' step of
// the manufacturing provisioning flow.
//
// This test is lengthy to simulate, as it involves 2 full ROM SPI-bootstrap procedures, lots of
// cryptograpy and key derivation, and software serdes of the uJSON control messages between the
// DUT and the test harness controller.
// Usefully, the software personalization component is written to be idempotent, and
// partial-progress through the program such that the OTP state has been updated can be taken as a
// checkpoint from which the software will skip over already completed operations. If we dump the
// memory states (OTP / Flash) at useful times during the test, we can start new simulations with
// those memory values backdoor-loaded into the memory models, and progress quickly to later stages
// of the test.
//
// A major complication to the above is that one of the early phases of the personalization program
// will write new flash scrambing seeds into OTP, generated on-device using the entropy complex.
// This means we cannot know these seeds ahead of time, and therefore cannot pre-scramble our test
// binaries for backdoor loading once the new seeds have been burned into OTP.
// The test program handles this by re-bootstrapping the test program at this point, and hence it
// is re-scrambled with the new keys by the flash controller frontdoor write mechanism. However,
// this bootstrap process is very slow to simulate.
// There are likely DV tricks we could play to make the new scrambling seeds deterministic in a
// simulation environment, but for the moment we can work around this problem as follows:
// - Run the simulation with no backdoor loading to completion (or at least to the point where the
//   two bootstrap operations have completed), while dumping memories at the important points.
//   1) Re-use the dumped memory images and the idempotent program properties to re-start the test
//      from an intermediate program location.
//   2) Modify the test software, and then use the gen-otp-img.py tooling to extract the generated
//      scrambling seeds from the dumped OTP image / OTP mmap, and then scramble any newly built
//      software binaries with these seeds.
//      No. 2 is quite a manual process, but can still usefully accelerate simulations.
//
// The appropriate places to dump/load memories are as follows:
// - dut_init()         Before the chip boots for the first time (normally managed by chip_env_cfg)
// - Phase0             This is after the initial bootstrap. The perso binary is now scrambled
//                      according to any default scrambling keys / configuration.
// - Phase1             After the new scrambling seeds / configuration has been deployed to OTP.
// - Phase2             After the second bootstrap, and the multi-slot binary has been
//                      reloaded/rescrambled with the new seeds.
// - Phase3             After sw_reset following provisioning of SECRET2 and flash info pages 1, 2,
//                      and 4 (keymgr / DICE keygen seeds).
// - Phase4             After personalization has completed.
//
// After the simulation has been run with no backdoor loading and dumping images (using +dump_mems),
// we can re-start the program from the intermediate state with intermediate images by passing the
// +perso_start_phase plusarg.
// For example, if we pass +perso_start_phase=2, the memory images that were dumped from this phase
// previously are loaded into the DUT at the start of stimulation-time, and any testbench stimulus
// related to the program execution before this phase is skipped.
//
// N.B.
//
// - As this test communicates over the OTTF SPI console, the test binary cannot be built for the
//   'sim_dv' execution environment, as the console is only initialized when
//   kDeviceType != kDeviceSimDV (see _ottf_main())

class chip_sw_rom_e2e_ft_perso_base_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_rom_e2e_ft_perso_base_vseq)
  `uvm_object_new

  bit dump_mems = 0; // Should memories be dumped mid-simulation?
  string load_path = ""; // Assumes working directory, but can be overridden by plusarg.

  typedef enum int {/* -- DUT MEMORY STATE AFTER PHASE COMPLETION -- */
    // Before the start of Phase0, the dut_init() routine will pre-load the base OTP image provided
    // by the +sw_images plusarg. Hence, the t=0 state begins as follows:
    // t=0       // Base OTP image + no flash image
    Phase0  = 0, // Base OTP image + perso slotA image scrambled w. base seeds
    Phase1  = 1, // OTP image w. new seeds + perso slotA image scrambled w. base seeds
    Phase2  = 2, // OTP image w. new seeds + multi-slot image (perso+rom_ext) scrambled w. new seeds
    Phase3  = 3, // OTP image w. new seeds w. SECRET2 w. flash info 1,2,4 +
                 //   multi-slot image (perso+rom_ext) scrambled w. new seeds
    Phase4  = 4  // OTP image w. full personalization +
                 //   multi-slot image (perso+rom_ext) scrambled w. new seeds
  } perso_phase_e;
  // (The explicit enumerations can be passed via +perso_start_phase for mid-test restart control)

  // Set the first perso phase to be executed in the simulation
  // (Dumped memory state corresponding to the end of the previous phase is automatically loaded)
  perso_phase_e perso_start_phase = Phase0;

  // SYNCHRONIZATION STRINGS
  string SYNC_STR_READ_BOOTSTRAP_REQ         = "Bootstrap requested.";
  string SYNC_STR_READ_RMA_TOKEN             = "Waiting For RMA Unlock Token Hash ...";
  string SYNC_STR_READ_PERSO_DICE_CERTS      = "Waiting for certificate inputs ...";
  string SYNC_STR_WRITE_TBS_CERTS            = "Exporting TBS certificates ...";
  string SYNC_STR_READ_ENDORSED_CERTS        = "Importing endorsed certificates ...";
  string SYNC_STR_READ_FINISHED_CERT_IMPORTS = "Finished importing certificates.";
  string SYNC_STR_READ_PERSO_DONE            = "Personalization done.";


  // Files containing personalization spi_console message payloads.
  //
  // WRITES
  // (These files are passed as inputs to the simulation via plusargs)
  string RMA_UNLOCK_TOKEN_HASH_FILE;
  string RMA_UNLOCK_TOKEN_HASH_CRC_FILE;
  string PERSO_CERTGEN_INPUTS_FILE;
  string MANUF_PERSO_DATA_BACK_FILE;
  // READS
  string TBS_CERTS_FILE = "tbs_certs.bin";
  string FINAL_HASH_FILE = "final_hash.bin";

  // Buffers for handling spi_console message payloads.
  //
  localparam uint kLcTokenHashSerializedMaxSize = 52;         // verilog_lint: waive parameter-name-style
  localparam uint kManufCertgenInputsSerializedMaxSize = 210; // verilog_lint: waive parameter-name-style
  localparam uint kPersoBlobSerializedMaxSize = 20535;        // verilog_lint: waive parameter-name-style
  localparam uint kSerdesSha256HashSerializedMaxSize = 98;    // verilog_lint: waive parameter-name-style
  // WRITES
  bit [7:0] RMA_UNLOCK_TOKEN_HASH[];
  bit [7:0] RMA_UNLOCK_TOKEN_HASH_CRC[];
  bit [7:0] PERSO_CERTGEN_INPUTS[];
  bit [7:0] MANUF_PERSO_DATA_BACK[];
  // READS
  bit [7:0] tbs_certs[];
  bit [7:0] final_hash[];
  bit [7:0] CRLF[];

  // Due to fully simulating both UART@115200baud and SPI Console traffic, this test is quite slow,
  // and we can spend quite a long time waiting for salient state changes. Hence the large timeout.
  uint spinwait_timeout_ns = 200_000_000; // 200ms

  extern function void read_plusarg_file(ref bit [7:0] tgt[], input string plusarg);
  extern virtual task get_plusarg_file_contents();
  extern virtual task await_ioa(string name, bit val = 1'b1, uint timeout_ns = 10_000_000);
  extern function string byte_array_as_str(bit [7:0] q[]);
  extern function void dump_byte_array_to_file(bit [7:0] array[], string filename);
  extern virtual task pre_start();
  extern virtual task body();
  extern task load_dut_memories(perso_phase_e perso_phase);
  extern task dump_dut_memories(perso_phase_e perso_phase);
  extern task await_test_start_after_reset(uint timeout_ns = 200_000_000);
  // This task sequences the sub-phases of the personalization flow. (See the header comment
  // for more context about the breakdown.)
  extern task do_ft_personalize();
  extern task do_ft_personalize_phase_0();
  extern task do_ft_personalize_phase_1();
  extern task do_ft_personalize_phase_2();
  extern task do_ft_personalize_phase_3();
  extern task do_ft_personalize_phase_4();

endclass : chip_sw_rom_e2e_ft_perso_base_vseq

function void chip_sw_rom_e2e_ft_perso_base_vseq::read_plusarg_file(ref bit [7:0] tgt[],
                                                                    input string  plusarg);
  string path;
  int    fd, len;
  string selector = {plusarg, "=%0s"};

  if (!$value$plusargs(selector, path)) begin
    `uvm_fatal(`gfn, $sformatf("No %s plusarg found.", plusarg));
  end

  fd = $fopen(path, "rb");
  if (!fd) begin
    `uvm_fatal(`gfn, $sformatf("Failed to open file %s (from the %s plusarg)", path, plusarg));
  end

  len = $fread(tgt, fd);
  `uvm_info(`gfn, $sformatf("%31s :: len=%0d", plusarg, len), UVM_LOW)

  $fclose(fd);
endfunction

task chip_sw_rom_e2e_ft_perso_base_vseq::get_plusarg_file_contents();
  RMA_UNLOCK_TOKEN_HASH     = new[kLcTokenHashSerializedMaxSize];
  RMA_UNLOCK_TOKEN_HASH_CRC = new[18];
  PERSO_CERTGEN_INPUTS      = new[kManufCertgenInputsSerializedMaxSize];
  MANUF_PERSO_DATA_BACK     = new[kPersoBlobSerializedMaxSize];
  read_plusarg_file(RMA_UNLOCK_TOKEN_HASH,     "RMA_UNLOCK_TOKEN_HASH_FILE");
  read_plusarg_file(RMA_UNLOCK_TOKEN_HASH_CRC, "RMA_UNLOCK_TOKEN_HASH_CRC_FILE");
  read_plusarg_file(PERSO_CERTGEN_INPUTS,      "PERSO_CERTGEN_INPUTS_FILE");
  read_plusarg_file(MANUF_PERSO_DATA_BACK,     "MANUF_PERSO_DATA_BACK_FILE");
endtask

function string chip_sw_rom_e2e_ft_perso_base_vseq::byte_array_as_str(bit [7:0] q[]);
  string str = "";
  foreach (q[i]) str = {str, $sformatf("%0s", q[i])};
  return str;
endfunction

function void chip_sw_rom_e2e_ft_perso_base_vseq::dump_byte_array_to_file(bit [7:0] array[],
                                                                          string    filename);
  integer fd = $fopen(filename, "w");
  if (!fd) `uvm_fatal(`gfn, $sformatf("Could not open file %s.", filename));
  $fwrite(fd, "%0s", byte_array_as_str(array));
  $fclose(fd);
endfunction

task chip_sw_rom_e2e_ft_perso_base_vseq::await_ioa(
  string name,
  bit    val = 1'b1,
  uint   timeout_ns = 10_000_000 /* 10ms */
);
  string timeout_m = $sformatf("Timed out waiting for %0s to be %0d.", name, val);

  // IOA6 (GPIO4) is the SPI console RX ready signal. (HOST->DEVICE flow control)
  // IOA5 (GPIO3) is the SPI console TX ready signal. (DEVICE->HOST flow control)
  // IOA4 (GPIO0) is for test start reporting.
  // IOA1 (GPIO1) is for test done reporting.
  // IOA0 (GPIO2) indicates an error has occurred.

  `uvm_info(`gfn, $sformatf("Waiting for %0s to be %0d now...", name, val), UVM_LOW)
  case (name)
    "IOA6": `DV_WAIT(cfg.chip_vif.mios[top_earlgrey_pkg::MioPadIoa6] == val, timeout_m, timeout_ns)
    "IOA5": `DV_WAIT(cfg.chip_vif.mios[top_earlgrey_pkg::MioPadIoa5] == val, timeout_m, timeout_ns)
    "IOA4": `DV_WAIT(cfg.chip_vif.mios[top_earlgrey_pkg::MioPadIoa4] == val, timeout_m, timeout_ns)
    "IOA1": `DV_WAIT(cfg.chip_vif.mios[top_earlgrey_pkg::MioPadIoa1] == val, timeout_m, timeout_ns)
    "IOA0": `DV_WAIT(cfg.chip_vif.mios[top_earlgrey_pkg::MioPadIoa0] == val, timeout_m, timeout_ns)
    default : `uvm_fatal(`gfn, "Given name of IOAx pad is not supported by await!")
  endcase

  `uvm_info(`gfn, $sformatf("Saw %0s as %0d now!", name, val), UVM_LOW)
endtask: await_ioa

task chip_sw_rom_e2e_ft_perso_base_vseq::pre_start();
  super.pre_start();

  if ($value$plusargs("dump_mems=%0b", dump_mems)) begin
    `uvm_info(`gfn, "Memory dumping enabled via +dump_mems", UVM_LOW)
  end
  if ($value$plusargs("load_path=%0s", load_path)) begin
    `uvm_info(`gfn, $sformatf("Will re-load dumped memories from dir: %s", load_path), UVM_LOW)
  end

  // Load the HOST->DEVICE spi_console precomputed/captured messages
  get_plusarg_file_contents();

  if ($value$plusargs("perso_start_phase=%0d", perso_start_phase)) begin
    `uvm_info(`gfn,
              $sformatf("Configured perso_start_phase=%0d (%0s) via plusarg.",
                        perso_start_phase,
                        perso_start_phase.name),
              UVM_LOW)
  end

  if ((perso_start_phase > Phase0) && dump_mems) begin
    // TODO: Calling load_mem_from_file() and write_mem_to_file() at the same time may not give a
    // repeatable result, and so for the moment we do not allow dumping and loading at the same
    // time. This could probably be fixed with some careful investigation.
    `uvm_fatal(`gfn, "Cannot dump memories when perso_start_phase >= 0.")
  end

  // Don't allow the first-boot dut_init() routine to load flash with an initial image.
  cfg.skip_flash_bkdr_load = 1'b1;
  // Don't use the ROM SPI Bootstrap in cpu_init(). We manage everything from the leaf vseq.
  cfg.use_spi_load_bootstrap = 1'b0;

  // Enable the UART agent to receive messages on the dbg console (e.g. via dbg_printf())
  // The 'silicon_creator' environment uses the follow baud rate...
  cfg.uart_baud_rate = BaudRate115200;
  configure_uart_agent(.uart_idx(ROM_CONSOLE_UART), .enable(1));
  // Monitor the CONSOLE UART throught the test for informational purposes
  fork print_uart_console_items(ROM_CONSOLE_UART); join_none

  if (!spi_agent_is_configured) begin
    spi_agent_configure_flash_cmds(cfg.m_spi_host_agent_cfg);
    spi_agent_is_configured = 1'b1;
  end

  // Spawn the spi_console polling process in the background.
  // The polling is still mediated by enabling/disabling the control bit
  // cfg.ottf_spi_console_h.enable_read_polling. Polling begins disabled.
  fork cfg.ottf_spi_console_h.host_spi_console_poll_reads(); join_none
  // Enable polling to capture the OTTF messages printed before starting the test.
  cfg.ottf_spi_console_h.enable_read_polling = 1'b1;

endtask

task chip_sw_rom_e2e_ft_perso_base_vseq::body();
  super.body();
  `uvm_info(`gfn, "chip_sw_rom_e2e_ft_perso_base_vseq::body()", UVM_LOW)

  fork begin: iso_fork
    fork
      begin : apply_stimulus
        do_ft_personalize();
        // After the completion of all stimulus, the device should raise the test done gpio
        await_ioa("IOA1", 1'b1, cfg.sw_test_timeout_ns);
        // Wait for the OTTF to send the 'Finished %s' message, and don't disconnect the
        // spi_console since software will block awaiting console traffic to be sent, which will
        // prevent SW reaching wfi and allowing the tilelink monitors to signal ok_to_end.
        cfg.ottf_spi_console_h.host_spi_console_read_wait_for_polled_str("PASS!");
        override_test_status_and_finish(.passed(1'b1));
      end
      begin : detect_error_gpio
        // If we see the error gpio, immediately end the test with a failure
        await_ioa("IOA0", 1'b1, cfg.sw_test_timeout_ns);
        override_test_status_and_finish(.passed(1'b0));
      end
    join_any
    disable fork;
  end : iso_fork join
endtask

task chip_sw_rom_e2e_ft_perso_base_vseq::load_dut_memories(perso_phase_e perso_phase);

  // Flash
  string FB0D_s = $sformatf("%0s%0s_dump_FlashBank0Data.64.scr.vmem", load_path, perso_phase.name);
  string FB1D_s = $sformatf("%0s%0s_dump_FlashBank1Data.64.scr.vmem", load_path, perso_phase.name);
  string FB0I_s = $sformatf("%0s%0s_dump_FlashBank0Info.64.scr.vmem", load_path, perso_phase.name);
  string FB1I_s = $sformatf("%0s%0s_dump_FlashBank1Info.64.scr.vmem", load_path, perso_phase.name);
  // OTP
  string OTP_s = $sformatf("%0s%0s_dump_OTP.24.vmem", load_path, perso_phase.name);

  // Flash
  cfg.mem_bkdr_util_h[FlashBank0Data].load_mem_from_file(FB0D_s);
  cfg.mem_bkdr_util_h[FlashBank1Data].load_mem_from_file(FB1D_s);
  cfg.mem_bkdr_util_h[FlashBank0Info].load_mem_from_file(FB0I_s);
  cfg.mem_bkdr_util_h[FlashBank1Info].load_mem_from_file(FB1I_s);
  // OTP
  cfg.mem_bkdr_util_h[Otp].load_mem_from_file(OTP_s);

  `uvm_info(`gfn, $sformatf("Loaded DUT mems with '%0s' images now.", perso_phase.name), UVM_LOW)
endtask

task chip_sw_rom_e2e_ft_perso_base_vseq::dump_dut_memories(perso_phase_e perso_phase);
  // Flash
  string FB0D_s = $sformatf("%0s_dump_FlashBank0Data.64.scr.vmem", perso_phase.name);
  string FB1D_s = $sformatf("%0s_dump_FlashBank1Data.64.scr.vmem", perso_phase.name);
  string FB0I_s = $sformatf("%0s_dump_FlashBank0Info.64.scr.vmem", perso_phase.name);
  string FB1I_s = $sformatf("%0s_dump_FlashBank1Info.64.scr.vmem", perso_phase.name);
  // OTP
  string OTP_s = $sformatf("%0s_dump_OTP.24.vmem", perso_phase.name);

  if (!dump_mems) return;

  // Flash
  cfg.mem_bkdr_util_h[FlashBank0Data].write_mem_to_file(FB0D_s);
  cfg.mem_bkdr_util_h[FlashBank1Data].write_mem_to_file(FB1D_s);
  cfg.mem_bkdr_util_h[FlashBank0Info].write_mem_to_file(FB0I_s);
  cfg.mem_bkdr_util_h[FlashBank1Info].write_mem_to_file(FB1I_s);
  // OTP
  cfg.mem_bkdr_util_h[Otp].write_mem_to_file(OTP_s);

  `uvm_info(`gfn, $sformatf("Dumped DUT memories in phase '%0s' now.", perso_phase.name), UVM_LOW)
endtask

task chip_sw_rom_e2e_ft_perso_base_vseq::await_test_start_after_reset(
  uint timeout_ns = 200_000_000
);
  `uvm_info(`gfn, "Waiting for reset...", UVM_MEDIUM)
  `DV_SPINWAIT(
    /*WAIT_*/       cfg.chip_vif.cpu_clk_rst_if.wait_for_reset();,
    /*MSG_*/        "Timeout waiting for reset to occur and complete.",
    /*TIMEOUT_NS_*/ spinwait_timeout_ns)

  // Now wait until the start of the test binary.
  // This can be a long time due to UART traffic and SPI Bootstrapping.
  `uvm_info(`gfn, "Device out of reset, awaiting TestStart GPIO.", UVM_MEDIUM)
  await_ioa("IOA4", 1'b1, timeout_ns); // IOA4 == TestStart
endtask

task chip_sw_rom_e2e_ft_perso_base_vseq::do_ft_personalize();
  /////////////
  // PHASE 0 //
  /////////////

  if (perso_start_phase > Phase0) begin
    // We're starting at a phase after 0. Don't load this phase, or drive any stimulus.
    `uvm_info(`gfn, "Skipping Phase0 loading and stimulus.", UVM_LOW)
  end else begin
    // We started at Phase0. There is no flash loading needed (the base_vseq handled OTP loading).
    `uvm_info(`gfn, "Starting Phase0 stimulus now.", UVM_LOW)
    do_ft_personalize_phase_0();
  end

  dump_dut_memories(Phase0); // (optionally) dump memories...
  /////////////
  // PHASE 1 //
  /////////////

  if (perso_start_phase > Phase1) begin
    // We're starting at a phase after 1. Don't load this phase, or drive any stimulus.
    `uvm_info(`gfn, "Skipping Phase1 loading and stimulus.", UVM_LOW)
  end else if (perso_start_phase == Phase1) begin
    // If starting at this phase, load the memory state and then drive the stimulus.
    `uvm_info(`gfn, "Loading Phase0 mems, starting Phase1 stimulus now.", UVM_LOW)
    load_dut_memories(Phase0);
    do_ft_personalize_phase_1();
  end else begin
    // We started at an earlier phase. Stimulus only.
    `uvm_info(`gfn, "Starting Phase1 stimulus now.", UVM_LOW)
    do_ft_personalize_phase_1();
  end

  dump_dut_memories(Phase1); // (optionally) dump memories...
  /////////////
  // PHASE 2 //
  /////////////

  if (perso_start_phase > Phase2) begin
    // We're starting at a phase after 2. Don't load this phase, or drive any stimulus.
    `uvm_info(`gfn, "Skipping Phase2 loading and stimulus.", UVM_LOW)
  end else if (perso_start_phase == Phase2) begin
    // If starting at this phase, load the memory state and then drive the stimulus.
    `uvm_info(`gfn, "Loading Phase1 mems, starting Phase2 stimulus now.", UVM_LOW)
    load_dut_memories(Phase1);
    do_ft_personalize_phase_2();
  end else begin
    // We started at an earlier phase. Stimulus only.
    `uvm_info(`gfn, "Starting Phase2 stimulus now.", UVM_LOW)
    do_ft_personalize_phase_2();
  end

  dump_dut_memories(Phase2); // (optionally) dump memories...
  /////////////
  // PHASE 3 //
  /////////////

  if (perso_start_phase > Phase3) begin
    // We're starting at a phase after 3. Don't load this phase, or drive any stimulus.
    `uvm_info(`gfn, "Skipping Phase3 loading and stimulus.", UVM_LOW)
  end else if (perso_start_phase == Phase3) begin
    // If starting at this phase, load the memory state and then drive the stimulus.
    `uvm_info(`gfn, "Loading Phase2 mems, starting Phase3 stimulus now.", UVM_LOW)
    load_dut_memories(Phase2);
    do_ft_personalize_phase_3();
  end else begin
    // We started at an earlier phase. Stimulus only.
    `uvm_info(`gfn, "Starting Phase3 stimulus now.", UVM_LOW)
    do_ft_personalize_phase_3();
  end

  dump_dut_memories(Phase3); // (optionally) dump memories...
  /////////////
  // PHASE 4 //
  /////////////

  // We never skip the stimulus for the final phase.
  if (perso_start_phase == Phase4) begin
    // If starting at this phase, load the memory state and then drive the stimulus.
    `uvm_info(`gfn, "Loading Phase3 mems, starting Phase4 stimulus now.", UVM_LOW)
    load_dut_memories(Phase3);
    do_ft_personalize_phase_4();
  end else begin
    // We started at an earlier phase. Stimulus only.
    `uvm_info(`gfn, "Starting Phase4 stimulus now.", UVM_LOW)
    do_ft_personalize_phase_4();
  end

  dump_dut_memories(Phase4); // (optionally) dump memories...
endtask : do_ft_personalize

task chip_sw_rom_e2e_ft_perso_base_vseq::do_ft_personalize_phase_0();
  // Perform the first ROM Bootstrap
  fork
    spi_device_load_bootstrap({cfg.sw_images[SwTypeTestSlotA], ".64.vmem"});

    // POR must be asserted externally at the end of the bootstrap process.
    // This is handled by the load_bootstrap() routine above.
    // Wait for the chip to restart, and the ROM to complete loading the bootstrapped Flash image.
    await_test_start_after_reset();
  join
endtask

task chip_sw_rom_e2e_ft_perso_base_vseq::do_ft_personalize_phase_1();
  // Wait for write of new scrambling seeds to the CREATOR_SW_CFG_FLASH_DATA_DEFAULT_CFG region.
  // Hence, we need to reset the chip and re-bootstrap the test binary that is loaded into flash
  // and re-scrambled with the new scrambling key (aka. the final transport image)
  //
  // The test requests this second bootstrap over the console.
  cfg.ottf_spi_console_h.host_spi_console_read_wait_for_polled_str(SYNC_STR_READ_BOOTSTRAP_REQ);

  `uvm_info(`gfn, "Resetting chip for second bootstrap now.", UVM_LOW)
  assert_por_reset();
endtask

task chip_sw_rom_e2e_ft_perso_base_vseq::do_ft_personalize_phase_2();

  // Perform the second ROM Bootstrap of Flash
  // > (the multi-slot binary of perso + ROM_EXT + Owner FW binaries)
  fork
    spi_device_load_bootstrap({cfg.sw_images[SwTypeMultiSlot], ".64.vmem"});

    // POR must be asserted externally at the end of the bootstrap process.
    // This is handled by the load_bootstrap() routine above.
    // Wait for the chip to restart, and the ROM to complete loading the bootstrapped Flash image.
    // This time we are bootstrapping a multi-slot image, so a large timeout is necessary.
    await_test_start_after_reset(.timeout_ns(1_000_000_000 /* 1s */));
  join
endtask

task chip_sw_rom_e2e_ft_perso_base_vseq::do_ft_personalize_phase_3();
  // After the second bootstrap, the test checks the previous steps have been completed successfully
  // by checking for non-default OTP values in the fields we expected to provision.
  // Assuming everying is in-order, the next point of host-interaction over the console is the
  // request for provisioning of the RMA Unlock Token.
  //
  // Wait for the DEVICE to request the RMA Unlock Token (personalize_otp_and_flash_secrets()).
  cfg.ottf_spi_console_h.host_spi_console_read_wait_for_polled_str(SYNC_STR_READ_RMA_TOKEN);
  // The device has now requested the Unlock Token. Write it over the spi console.
  cfg.ottf_spi_console_h.host_spi_console_write_when_ready('{RMA_UNLOCK_TOKEN_HASH,
                                                             RMA_UNLOCK_TOKEN_HASH_CRC});

  // After the OTP SECRET2 partition is programmed, the chip performs a SW reset.
  // At this point, personalize_otp_and_flash_secrets() has completed.
  await_test_start_after_reset();
endtask

task chip_sw_rom_e2e_ft_perso_base_vseq::do_ft_personalize_phase_4();
  // After the previous reset at the completion of provisioning of SECRET2, the test again checks
  // the previous steps have completed successfully, and if so, advances to the next phase of the
  // personalization flow.
  // At this point, there are no further resets or bootstraps.

  // Next, we provision all device certificates.
  `uvm_info(`gfn, "Awaiting sync-str to start write of certificate provisioning data...", UVM_LOW)
  cfg.ottf_spi_console_h.host_spi_console_read_wait_for_polled_str(SYNC_STR_READ_PERSO_DICE_CERTS);
  cfg.ottf_spi_console_h.host_spi_console_write_when_ready('{PERSO_CERTGEN_INPUTS});

  // Wait until the device exports the TBS certificates.
  `uvm_info(`gfn, "Awaiting sync-str to start read of exported certificate payload...", UVM_LOW)
  cfg.ottf_spi_console_h.host_spi_console_read_wait_for_polled_str(SYNC_STR_WRITE_TBS_CERTS);

  // Read the TBS certificate payload from the console.
  cfg.ottf_spi_console_h.enable_read_polling = 1'b0;
  cfg.ottf_spi_console_h.host_spi_console_read_payload(tbs_certs, kPersoBlobSerializedMaxSize);
  dump_byte_array_to_file(tbs_certs, TBS_CERTS_FILE);
  cfg.ottf_spi_console_h.enable_read_polling = 1'b1;

  // Process the certificate payload...
  // > Nothing to do, we cheat and already have the response in a file.

  // Wait until the device indicates it can import the endorsed certificate files.
  `uvm_info(`gfn, "Awaiting sync-str to start write of endorsed certificates...", UVM_LOW)
  cfg.ottf_spi_console_h.host_spi_console_read_wait_for_polled_str(SYNC_STR_READ_ENDORSED_CERTS);
  cfg.ottf_spi_console_h.host_spi_console_write_when_ready('{MANUF_PERSO_DATA_BACK});

  // Wait until the device indicates it has successfully imported the endorsed certificate files.
  `uvm_info(`gfn, "Awaiting sync-str for completion of endorsed certificate import...", UVM_LOW)
  cfg.ottf_spi_console_h.host_spi_console_read_wait_for_polled_str(
    SYNC_STR_READ_FINISHED_CERT_IMPORTS);

  // The device now checks the imported certificate package.

  // Read out the final hash sent from the device
  `uvm_info(`gfn, "Awaiting export of the final hash...", UVM_LOW)
  cfg.ottf_spi_console_h.enable_read_polling = 1'b0;
  cfg.ottf_spi_console_h.host_spi_console_read_payload(final_hash,
                                                       kSerdesSha256HashSerializedMaxSize);
  dump_byte_array_to_file(final_hash, FINAL_HASH_FILE);
  cfg.ottf_spi_console_h.enable_read_polling = 1'b1;

  // Wait until the device indicates it has successfully completed perso!
  `uvm_info(`gfn, "Awaiting sync-str for completion of personalization...", UVM_LOW)
  cfg.ottf_spi_console_h.host_spi_console_read_wait_for_polled_str(SYNC_STR_READ_PERSO_DONE);
endtask
