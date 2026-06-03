// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// FIFO-related constants and structure descriptions.
//
// - The Host Controller Interface specification employs a number of FIFOs and this I3C block
//   implements all of those FIFOs using a single shared message buffer.
// - Each of the FIFOs carries data words that are 32 bits in width and are referred to as `DWORD`s.
// - The OpenTitan TTI mimics the HCI to a significant degree and its FIFOs share the same message
//   buffer.
// - The FIFOs are:
//
//   Controller side:
//   - Command Queue  - carries 2-DWORD command descriptors.
//   - Response Queue - carries 1-DWORD response descriptors.
//   - IBI Queue      - carries In-Band Interrupt data.
//   - IBI Stat Desc  - carries 1-DWORD IBI Status Descriptors.
//   - TX Buffer      - carries data for transmission over the I3C bus.
//   - RX Buffer      - carries data received over the I3C bus.
//
//   Target side:
//   - Targ Txi Buffers - carries data for transmission over the I3C bus, for each Virtual Target.
//   - Targ Txi Descs   - descriptors for transmitted data, for each Virtual Target.
//   - Targ IBI Data    - In-Band interrupt payload from all Virtual Targets combined.
//   - Targ IBI Desc    - descriptors for IBI transmission.
//   - Targ Rx Buffer   - carries data received over the I3C bus.
//   - Targ Rx Descs    - descriptors for received data.
//   - Targ Async Evt   - Asynchronous Events to be reported to software.
//
// - Read data will be presented, with `rvalid` asserted, as soon as it becomes available,
//   and is removed from the FIFO in the presence of `rvalid & rready`.
// - Write data is accepted into the FIFO only when `wvalid & wready`, with `wready` denoting
//   the availability of space.
// - Read data is presented combinationally, so the message buffer and the immediately-associated
//   reader/writer logic are expected to be operating synchronously on the main clock of the IP
//   block.

package i3c_fifo_pkg;
  // Width of offsets and the `base index` of the FIFO within the shared memory.
  // (FIFO fill level and available space are also derived from this parameter.)
  localparam int unsigned DepthW = i3c_pkg::BufAddrW;

  // Data width of FIFO, in bits.
  localparam int unsigned Width = 32;

  // FIFO identifier.
  // - Note: index 0 is highest priority at the arbiter in `i3c_buffer`.
  typedef enum {
    FIFO_TxTarg0   = 0,   // Target 0 transmission buffer.
    FIFO_TxTarg1   = 1,   // Target 1 transmission buffer.
    FIFO_TxBuf     = 2,   // Controller transmission buffer.
    FIFO_IBITarg   = 3,   // IBI Payload, Targets.
    FIFO_RxTarg    = 4,   // Targets' reception buffer.
    FIFO_RxBuf     = 5,   // Controller reception buffer.
    FIFO_IBIQ      = 6,   // IBI Data Queue within the Controller.
    FIFO_IBIStD    = 7,   // IBI Status Descriptor FIFO within the Controller.
    FIFO_RspQ      = 8,   // Response Queue, Controller.
    FIFO_CmdQ      = 9,   // Command Queue, Controller.
    FIFO_TxDTarg0  = 10,  // Transmission Descriptor, Target 0.
    FIFO_TxDTarg1  = 11,  // Transmission Descriptor, Target 1.
    FIFO_RxDTarg   = 12,  // Reception Descriptor, Targets.
    FIFO_IBIDTarg  = 13,  // IBI Descriptor, Targets.
    FIFO_AsyncTarg = 14,  // Asynchronous Events Queue, Targets.
    // Number of FIFOs.
    FIFO_Count
  } fifo_id_e;

  // FIFO configuration.
  typedef struct packed {
    logic  [DepthW-1:0] min;  // Base address of the FIFO within the shared memory.
    logic  [DepthW-1:0] max;  // End address, inclusive.
    logic    [DepthW:0] size; // Size of the FIFO, in DWORD entries.
  } fifo_config_t;

  // FIFO state information.
  // - `wptr` and `rptr` are both in the range [0, BufWords)
  typedef struct packed {
    logic  [DepthW-1:0] wptr;   // Current write pointer within buffer.
    logic  [DepthW-1:0] rptr;   // Current read pointer within buffer.
    logic               full;   // Disambiguates the `wptr == rptr` case.
    logic               empty;  // Convenience, but may be derived from the above.
    logic    [DepthW:0] used;   // Number of used entries.
    logic    [DepthW:0] avail;  // Number of available entries.
    logic               pre;    // Prefetched data is available; for diagnostic use only.
  } fifo_state_t;

  // FIFO input signals to the `i3c_buffer` module.
  typedef struct packed {
    // Read/write requests.
    logic             rready;  // Consume read data when available.
    logic             wvalid;  // Perform write when space available.
    logic [Width-1:0] wdata;   // Data to be written.
  } fifo_in_t;

  // FIFO output signals from the `i3c_buffer` module.
  typedef struct packed {
    // Responses to read/write requests.
    logic             wready;
    logic             rvalid;
    logic [Width-1:0] rdata;
  } fifo_out_t;

  // Convenience function that returns the size of the FIFO in DWORD entries; this is not supplied
  // in the register configuration but is instead derived from the programmed min/max bounds.
  function automatic bit [DepthW-1:0] fifo_size(input fifo_config_t cfg);
    return DepthW'(cfg.max - cfg.min) + 'b1;
  endfunction

endpackage
