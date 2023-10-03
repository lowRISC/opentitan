// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module mbx_ombx #(
  parameter int unsigned CfgSramAddrWidth   = 32,
  parameter int unsigned CfgSramDataWidth   = 32,
  parameter int unsigned CfgObjectSizeWidth = 11
) (
  input  logic                          clk_i,
  input  logic                          rst_ni,
  output logic                          ombx_state_error_o,
  output logic                          ombx_doe_intr_state_set_o,
  output logic                          ombx_pending_o,
  output logic                          ombx_status_ready_update_o,
  output logic                          ombx_status_ready_o,
  input  logic                          hostif_range_valid_i,
  input  logic [CfgSramAddrWidth-1:0]   hostif_base_i,
  input  logic [CfgSramAddrWidth-1:0]   hostif_limit_i,
  output logic                          sys_read_all_o,
  // Control and status signals from the host and system interface
  // Writing a 1 to control.abort register clears the abort condition
  input  logic                          sysif_status_ready_i,
  input  logic                          hostif_control_abort_clear_i,
  input  logic                          hostif_control_error_set_i,
  input  logic                          sysif_control_abort_set_i,
  input  logic                          sysif_read_data_read_valid_i,
  input  logic                          sysif_read_data_write_valid_i,
  // Interface for the object size register
  input logic                           hostif_ombx_object_size_write_i,
  input logic [CfgObjectSizeWidth-1:0]  hostif_ombx_object_size_i,
  output logic                          hostif_ombx_object_size_update_o,
  output logic [CfgObjectSizeWidth-1:0] hostif_ombx_object_size_o,
  // DOE data coming from the SRAM
  output  logic [CfgSramDataWidth-1:0]  ombx_read_data_o,
  // Host interface to the private SRAM
  output logic                          ombx_sram_read_req_o,
  input  logic                          ombx_sram_read_gnt_i,
  output logic [CfgSramAddrWidth-1:0]   ombx_sram_read_ptr_o,
  input  logic                          ombx_sram_read_resp_valid_i,
  input  logic [CfgSramDataWidth-1:0]   ombx_sram_read_resp_i
);
  localparam int unsigned LCFG_SRM_ADDRINC = CfgSramDataWidth / 8;

  logic [CfgSramAddrWidth-1:0] sram_read_ptr_d, sram_read_ptr_q;
  logic [CfgSramAddrWidth-1:0] sram_read_ptr_limit_d, sram_read_ptr_limit_q;

  // Status signals from the FSM
  logic mbx_empty, mbx_read, mbx_sys_abort;
  logic set_first_req, clear_first_req;

  // Generate the read request
  // - Mbx reader ACK the current read data and initate the first request
  // First is initiated by mbx owner writes object size register
  // Note that pointer comparison with hostif_limit_i is inclusive, while comparison with internal
  // limit of the object size is exclusive
  logic read_req, first_req_q;
  assign read_req = first_req_q |
                    (mbx_read & sysif_read_data_write_valid_i   &
                    (sram_read_ptr_q <= hostif_limit_i)         &
                    (sram_read_ptr_q < sram_read_ptr_limit_q));

  // Create a sticky TLUL read request until its granted
  logic req_q;
  assign ombx_sram_read_req_o = read_req | req_q;

  prim_flop #(
    .Width(1)
  ) u_req_state (
    .clk_i ( clk_i                                        ),
    .rst_ni( rst_ni                                       ),
    .d_i   ( ombx_sram_read_req_o & ~ombx_sram_read_gnt_i ),
    .q_o   ( req_q                                        )
  );

  // Backpressure the next read data until the current write data brings back the data from SRAM
  // Exclude last ack
  logic set_pending, clear_pending;

  // Block the request from TLUL until the SRAM read is complete
  // Note that pointer comparison with hostif_limit_i is inclusive, while comparison with internal
  // limit of the object size is exclusive
  assign set_pending   = mbx_read & sysif_read_data_write_valid_i &
                        (sram_read_ptr_q <= hostif_limit_i)       &
                        (sram_read_ptr_q < sram_read_ptr_limit_q);
  assign clear_pending = ombx_sram_read_resp_valid_i;

  prim_flop #(
    .Width(1)
  ) u_pending (
    .clk_i ( clk_i                                           ),
    .rst_ni( rst_ni                                          ),
    .d_i   ( set_pending | (ombx_pending_o & ~clear_pending) ),
    .q_o   ( ombx_pending_o                                  )
  );

  logic writer_close_mbx;
  // move FSM to MbxRead (Ready) after the 1st read comes back
  assign writer_close_mbx = mbx_empty & ombx_sram_read_resp_valid_i;

  // Terminate mbx_read state (Ready = 1 -> 0) if ombx is already drained (sram_read is not issued)
  assign  sys_read_all_o = mbx_read                       &
                           sysif_read_data_write_valid_i  &
                           (sram_read_ptr_q == sram_read_ptr_limit_q);

  logic host_clear_abort;
  assign host_clear_abort = hostif_control_abort_clear_i & mbx_sys_abort;

  // SRAM read pointer management
  logic load_read_ptr, advance_read_ptr;

  // Rewind the read pointer to the base
  assign load_read_ptr = set_first_req | sys_read_all_o | host_clear_abort;

  // Advance the read pointer when one request went through
  assign  advance_read_ptr = ombx_sram_read_req_o & ombx_sram_read_gnt_i;

  always_comb begin
    sram_read_ptr_d = sram_read_ptr_q;

    if (load_read_ptr) begin
      sram_read_ptr_d = hostif_base_i;
    end else if (advance_read_ptr) begin
      sram_read_ptr_d = sram_read_ptr_q + LCFG_SRM_ADDRINC;
    end
  end

  prim_generic_flop_en #(
    .Width(CfgSramAddrWidth)
  ) u_sram_read_ptr (
    .clk_i ( clk_i                            ),
    .rst_ni( rst_ni                           ),
    .en_i  ( load_read_ptr | advance_read_ptr ),
    .d_i   ( sram_read_ptr_d                  ),
    .q_o   ( sram_read_ptr_q                  )
  );
  assign ombx_sram_read_ptr_o = sram_read_ptr_q;

  // Clear ombx read data register in case of all data is read, an error happens,
  // or the requester aborts the transaction
  logic clear_read_data;
  assign clear_read_data = sys_read_all_o             |
                           hostif_control_error_set_i |
                           sysif_control_abort_set_i;
  // Advance the SRAM read response to read data
  prim_generic_flop_en #(
    .Width(CfgSramDataWidth)
  ) u_sram_read_data (
    .clk_i ( clk_i                                                        ),
    .rst_ni( rst_ni                                                       ),
    .en_i  ( ombx_sram_read_resp_valid_i | clear_read_data                ),
    .d_i   ( {CfgSramDataWidth{~clear_read_data}} & ombx_sram_read_resp_i ),
    .q_o   ( ombx_read_data_o                                             )
  );

  // The following logic creates the status signals to update the hostif.object_size register,
  // which is part of the host interface.

  logic host_write_object_size_q;
  logic ombx_object_size_update_valid_q;

  // The following flop creates an indicator that hostif.object_size has been written such that
  // in the next cycle, the read pointer limit can be updated and the first transfer from the
  // SRAM to the internal data flop can be initiated. Only update the object size when not a
  // transfer was successful.

  prim_flop #(
    .Width(1)
  ) u_host_write_object_size (
    .clk_i ( clk_i                                                              ),
    .rst_ni( rst_ni                                                             ),
    .d_i   ( hostif_ombx_object_size_write_i & ~ombx_object_size_update_valid_q ),
    .q_o   ( host_write_object_size_q                                           )
  );

  logic [CfgObjectSizeWidth-1:0] hostif_ob_object_size_minus_one;
  // Update the hostif.object_size register on every transaction or when aborting the transaction
  assign hostif_ombx_object_size_update_o = (read_req & ombx_sram_read_gnt_i) |
                                             sysif_control_abort_set_i;
  // The updated value is the decremented by 1 size or zero-ed out if the transaction is aborted
  assign hostif_ob_object_size_minus_one = hostif_ombx_object_size_i - 1;
  assign hostif_ombx_object_size_o       = {CfgObjectSizeWidth{~sysif_control_abort_set_i}} &
                                           hostif_ob_object_size_minus_one;

  prim_flop #(
    .Width(1)
  ) u_host_object_size_update_valid (
    .clk_i ( clk_i                            ),
    .rst_ni( rst_ni                           ),
    .d_i   ( hostif_ombx_object_size_update_o ),
    .q_o   ( ombx_object_size_update_valid_q  )
  );

  // Compute the read pointer limit after object size is written
  assign sram_read_ptr_limit_d = hostif_base_i +
                                 CfgSramAddrWidth'({hostif_ombx_object_size_i, 2'b0});

  prim_generic_flop_en #(
    .Width(CfgSramAddrWidth)
  ) u_sram_read_ptr_limit (
    .clk_i ( clk_i                                ),
    .rst_ni( rst_ni                               ),
    // Factor in ~mbx_read because HW update can trigger host_write_object_size_q
    .en_i  ( host_write_object_size_q & ~mbx_read ),
    .d_i   ( sram_read_ptr_limit_d                ),
    .q_o   ( sram_read_ptr_limit_q                )
  );

  // Logic to initiate the first read (mbx_empty) from the SRAM to the requester
  // Only starts the transmitting if the mailbox is configured properly
  // (SRAM range is valid and the object size has been written to a non-zero)
  // value. mbx_empty means there hasn't been read anything but range is valid.
  assign set_first_req   = mbx_empty & host_write_object_size_q & (|hostif_ombx_object_size_i);
  assign clear_first_req = ombx_sram_read_gnt_i;

  prim_flop #(
    .Width(1)
  ) u_pop_entry (
    .clk_i ( clk_i                                            ),
    .rst_ni( rst_ni                                           ),
    .d_i   ( set_first_req | (first_req_q & ~clear_first_req) ),
    .q_o   ( first_req_q                                      )
  );

  // Create a DOE interrupt request when the obmx FSM turns into the ready state or when an error
  // is raised
  assign ombx_doe_intr_state_set_o = (ombx_status_ready_o & ombx_status_ready_update_o) |
                                      hostif_control_error_set_i;

  mbx_fsm #(
    .CfgOmbx ( 1 )
  ) u_mbxfsm(
    .clk_i                     ( clk_i                        ),
    .rst_ni                    ( rst_ni                       ),
    .mbx_range_valid_i         ( hostif_range_valid_i         ),
    .hostif_abort_ack_i        ( hostif_control_abort_clear_i ),
    .hostif_control_error_set_i( hostif_control_error_set_i   ),
    .sysif_control_abort_set_i ( sysif_control_abort_set_i    ),
    .sys_read_all_i            ( sys_read_all_o               ),
    .writer_close_mbx_i        ( writer_close_mbx             ),
    .writer_write_valid_i      ( 1'b0                         ),
    // Status signals
    .mbx_empty_o               ( mbx_empty                    ),
    .mbx_write_o               (                              ),
    .mbx_read_o                ( mbx_read                     ),
    .mbx_sys_abort_o           ( mbx_sys_abort                ),
    .mbx_ready_update_o        ( ombx_status_ready_update_o   ),
    .mbx_ready_o               ( ombx_status_ready_o          ),
    .mbx_state_error_o         ( ombx_state_error_o           )
  );

  //////////////////////////////////////////////////////////////////////////////
  // Assertions
  //////////////////////////////////////////////////////////////////////////////

  // When reading from the ombx doe_status.ready must have been asserted
  `ASSERT_NEVER(ReadyAssertedWhenRead_A, ombx_sram_read_req_o &
                ~(first_req_q | sysif_status_ready_i))
  // System write-to-read data is non-posted.  No subsequential read or write comes before the
  // write is ACKed
  `ASSERT_NEVER(NoReadBeforeWriteAcked_A, ombx_pending_o &
                (sysif_read_data_read_valid_i | sysif_read_data_write_valid_i))
  // Never read the SRAM if it is empty
  logic ombx_is_empty;
  assign  ombx_is_empty = (sram_read_ptr_q == sram_read_ptr_limit_q);
  `ASSERT_NEVER(NeverReadWhenEmpty_A, ombx_sram_read_req_o & ombx_is_empty)
  // Never let the read pointer run out of the limit
  `ASSERT_NEVER(NeverRunOutOfLimit_A, sram_read_ptr_q > sram_read_ptr_limit_q)

`ifdef INC_ASSERT

  logic[CfgSramAddrWidth-1:0] sram_read_ptr_assert_q;
  prim_flop #(
    .Width(CfgSramAddrWidth)
  ) u_sram_ptr_assert (
    .clk_i ( clk_i                  ),
    .rst_ni( rst_ni                 ),
    .d_i   ( sram_read_ptr_d        ),
    .q_o   ( sram_read_ptr_assert_q )
  );
  // A granted write by the host adapter must advance the write pointer
  `ASSERT_IF(GntMustAdvanceReadPtr_A, sram_read_ptr_assert_q == sram_read_ptr_q,
             ombx_sram_read_gnt_i)
`endif
endmodule
