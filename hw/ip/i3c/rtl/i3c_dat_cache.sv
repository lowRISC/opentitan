// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Device Address Table cache.

module i3c_dat_cache
  import i3c_controller_pkg::*;
  import i3c_pkg::*;
#(
  // Number of entries in the DAT.
  parameter int unsigned NumDATEntries,
  // Maximum number of entries in the DAT cache.
  parameter int unsigned CacheSize,

  // Derived parameters.
  localparam int unsigned DATAddrW = $clog2(NumDATEntries)
) (
  // Clock and reset.
  input                   clk_i,
  input                   rst_ni,

  // Control inputs.
  input                   enable_i,
  input                   sw_reset_i,

  // Update an entry within the cache, if present.
  // - used when the driver software writes to a DAT entry.
  input                   we_i,
  input    [DATAddrW-1:0] widx_i,
  input  i3c_datc_wdata_t wdata_i,

  // Read access.
  // - reads are performed by the Controller transceiver logic.
  // - the read request (`re_i` and `raddr_i` must remain static until the request is granted,
  //   or a sw reset occurs.
  // - when granted, `rhit_o` indicates whether data is available for the address requested,
  //   and iff so, the three signals `ibi_payload_o`, `ibi_reject_o` and `crr_reject_o` are valid.
  input                   re_i,           // Read request.
  output                  rgnt_o,         // Proceed; decision available.
  input             [6:0] raddr_i,        // Dynamic address.
  output logic            rhit_o,         // Device information available?
  output logic            ibi_payload_o,
  output logic            ibi_reject_o,
  output logic            crr_reject_o,

  // Interface to DAT memory for walking the table.
  // - TODO: with the present simple implementation this is not required.
  //         Once ratified, decide whether these ports should persist or be removed.
  output                  dat_re_o,
  output [DATAddrW-1:0]   dat_idx_o,
  input  i3c_dat_mem_t    dat_rdata_i
);

  // This module implements a small cache of DAT fields that are required quickly when responding to
  // a Target request. It could fairly by considered a design flaw of the HCI that the DAT entries
  // _contain_ the device address, requiring that the DAT entries be searched.
  // Since the HCI Specification Version 1.2 constrains the DAT to no more than 32 entries, we opt
  // to implement a cache that mirrors the current DAT entries exactly, to keep things simple.
  //
  // - an IBI/CRR request occurs potentially at SDR0 signaling speed (12.5MHz), and we need to
  //   respond within 2 cycles at 50MHz or resort to delaying the ACK/NACK response by stalling SCL.
  // - the address received, however, is available on the rising SCL edge of the final address bit
  //   (we don't need to wait for the RnW bit), so that gives us 6-7 cycles (at 50MHz) to perform
  //   the lookup without sacrificing performance.
  // - write operations may occur on successive clock cycles from the HCI/Driver.

  // Special address value indicating an unused cache entry; this is an invalid I3C address.
  localparam logic [6:0] AddrUnused = 7'h00;

  // Cache entry.
  // - presently this is the same as the write data; in principle they could differ.
  typedef i3c_datc_wdata_t entry_t;
  entry_t entry[CacheSize];

  // Zero is not a valid I3C address and shall not be matched (HCI 8.1.2).
  // - we therefore use a `dyn_addr` field of zero to mark cache entries as unused.
  // - we should never be called upon to provide information for an invalid I3C address because we
  //   can only return the 'accept/reject' indications; invalid addresses should already have been
  //   filtered out and raised as errors instead of becoming requests.
  wire raddr_valid = (raddr_i != AddrUnused);  // Just a precaution.

  // Associative lookup.
  // - nothing prevents software updates from occurring at the same time as reads by the hardware
  //   so we must handle both concurrently.
  // - matching on the transceiver side is done using the I3C address.
  // - software accesses just update the specified entry; software updates modify the dynamic
  //   address and/or attributes, or indeed invalidate an entry by setting the dynamic address to
  //   AddrUnused (0).
  logic [CacheSize-1:0] rmatched;
  for (genvar e = 0; e < CacheSize; e++) begin : gen_rmatched
    assign rmatched[e] = &{re_i, raddr_valid, raddr_i == entry[e].dyn_addr};
  end

  // Request may be granted immediately with this simple implementation.
  assign rgnt_o = re_i & |{rmatched, !raddr_valid};
  // Valid details found?
  // - all requests will be denied if the device properties could not be found; this signal may be
  //   used to notify driver software that a Target is attempting to communicate but is not known
  //   to the DAT.
  // - the Controller logic may always just use `ibi_payload_o`, `ibi_reject_o` and `crr_reject_o`
  //   and ignore `rhit_o`.
  assign rhit_o = |rmatched;

  // Reading is simply combinational, caller must use the returned data during the cycle for which
  // `rgnt_o` is asserted and/or store it.
  logic [CacheSize-1:0] ibi_payload, ibi_reject, crr_reject;
  for (genvar e = 0; e < CacheSize; e++) begin : gen_verdict
    assign ibi_payload[e] =   rmatched[e] &  entry[e].ibi_payload;  // Default to no payload.
    assign ibi_reject[e]  = ~(rmatched[e] & ~entry[e].ibi_reject);  // Default to rejecting IBI.
    assign crr_reject[e]  = ~(rmatched[e] & ~entry[e].crr_reject);  // Default to rejecting CRR.
  end
  assign ibi_payload_o = |ibi_payload;  // Default to no payload.
  assign ibi_reject_o  = &ibi_reject;   // Default to rejecting IBI.
  assign crr_reject_o  = &crr_reject;   // Default to rejecting CRR.

  // Handle write accesses.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin : init_cache
      for (int unsigned e = 0; e < CacheSize; e++) begin
        entry[e].dyn_addr     <= AddrUnused;
        entry[e].ibi_payload  <= 1'b0;
        entry[e].ibi_reject   <= 1'b0;
        entry[e].crr_reject   <= 1'b0;
      end
    end else begin : update_cache
      // Note: updating of the cache is not clock-gated with `enable_i` as a precaution against
      //       software modifying the Device Address Table whilst the Controller is not enabled;
      //       it's important that the DAT and the cache remain consistent.
      if (we_i) entry[widx_i] <= wdata_i;
    end
  end

  // Read requests to the Device Address Table; not required with this simple implementation.
  assign dat_re_o   = 1'b0;
  assign dat_idx_o  = DATAddrW'('b0);
  wire unnused_rdata = ^dat_rdata_i;

  // This simple implementation requires that the cache has the same number of entries as the
  // Device Address Table (DAT) itself.
  if (CacheSize != NumDATEntries) $fatal(1, "DAT and DAT Cache sizes must match.");

endmodule
