// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Routines to interact with an OTTF SPI console using an OpenTitan spi_host agent.
//
// This package provides the 'ottf_spi_console' class which can be instantiated as a testbench
// component to provide methods to drive HOST-side communications of an OpenTitan OTTF SPI console.
// The env can configure this object by connecting the virtual interfaces (clk_rst and flow_ctrl),
// and the base_vseq should assign handles for the parent sequence (seq_h) and the sequencer for
// the OpenTitan spi_host UVC (spi_host_sequencer_h).
//
// After configuration, the primary interface for sequences to make use of this are the methods:
// - host_spi_console_poll_reads()
// - host_spi_console_read_wait_for_polled_str()
// - host_spi_console_read_payload()
// - host_spi_console_write_when_ready()
//
// Note.
// This is a bare-bones library for driving a console interaction. The methods here are crude.
// Many methods fatally timeout if they see no stimulus or response to stimulus within a relatively
// short window of time, and they are not currently written to handle errors / timeouts robustly.
// They should be used with prior knowledge about how the DEVICE-side will behave with regards to
// message types and message content.
// It also only works with the sideband wired indicator signal-based flow control mechanism.

package ottf_spi_console_pkg;

  import dv_utils_pkg::uint;

  import uvm_pkg::*;
  import spi_agent_pkg::*;
  import csr_utils_pkg::*;

  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // Default timeouts and delays used in this package.
  // Due to console activity being very slow relative to many other parts of the system, these
  // delays and timeouts are large. They are also very top and application specific, and would
  // require tuning for significantly different use cases.
  // Note that this stimulus may be timing-sensitive due to interactions with the software running
  // the DEVICE-side of the OTTF SPI Console, so test appropriately if changing these values.
  uint await_flow_ctrl_timeout_ns  = 1_000_000_000; // 1s
  uint wait_on_busy_timeout_ns     =   200_000_000; // 200ms
  uint write_completion_timeout_ns =   200_000_000; // 200ms
  uint min_interval_ns             =         3_000; //   3us

  // Typical opcodes used by SPI NOR-flash devices.
  // Ensure that both parties are using the same encodings.
  typedef enum bit [7:0] {
    SpiFlashReadJedec    = 8'h9F,
    SpiFlashReadSfdp     = 8'h5A,
    SpiFlashReadNormal   = 8'h03,
    SpiFlashReadFast     = 8'h0B,
    SpiFlashReadDual     = 8'h3B,
    SpiFlashReadQuad     = 8'h6B,
    SpiFlashReadSts1     = 8'h05,
    SpiFlashReadSts2     = 8'h35,
    SpiFlashReadSts3     = 8'h15,
    SpiFlashWriteDisable = 8'h04,
    SpiFlashWriteEnable  = 8'h06,
    SpiFlashWriteSts1    = 8'h01,
    SpiFlashWriteSts2    = 8'h31,
    SpiFlashWriteSts3    = 8'h11,
    SpiFlashChipErase    = 8'hC7,
    SpiFlashSectorErase  = 8'h20,
    SpiFlashPageProgram  = 8'h02,
    SpiFlashEn4B         = 8'hB7,
    SpiFlashEx4B         = 8'hE9
  } spi_flash_cmd_e;

  typedef enum int {
    rx_ready = 1,
    tx_ready = 0
  } flow_ctrl_idx_e;

  `include "ottf_spi_console.sv"

endpackage : ottf_spi_console_pkg
