// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module cheriot_tag_filter #(
  // The number of outstanding TL transaction the IP supports
  parameter int unsigned NumOutstanding      = 32'd4,
  // TL-UL address type
  parameter type   addr_t                    = logic [top_pkg::TL_AW-1:0],
  // Memory regions that have a capability tag store
  parameter addr_t MainSramBaseAddr          = 'h1000_0000,
  parameter addr_t MainSramTopAddr           = 'h1003_0000,
  parameter addr_t NvmBaseAddr               = 'h3000_0000,
  parameter addr_t NvmTopAddr                = 'h3020_0000,
  // Base addresses of the corresponding tag regions in the meta SRAM
  parameter addr_t MetaMainSramTagBase       = 'h1100_8C00,
  parameter addr_t MetaNvmTagBase            = 'h1100_0C00,
  // Writes only update the capability tag and are never forwarded to the host port; the filter
  // answers them itself. A write that does not update a tag is answered with an error.
  parameter bit    TagOnlyWrites             = 1'b0
)(
  input clk_i,
  input rst_ni,

  // CHERIoT mode enabled
  input  prim_mubi_pkg::mubi4_t cheriot_ena_i,

  // Device port
  input  tlul_pkg::tl_h2d_t tl_d_i,
  input  logic              tag_d_i,
  output tlul_pkg::tl_d2h_t tl_d_o,
  output logic              tag_d_o,

  // Meta port
  output tlul_pkg::tl_h2d_t tl_m_o,
  output logic              tag_m_o,
  output logic  [4:0]       bit_sel_m_o,
  input  tlul_pkg::tl_d2h_t tl_m_i,
  input  logic              tag_m_i,

  // Host port
  output tlul_pkg::tl_h2d_t tl_h_o,
  input  tlul_pkg::tl_d2h_t tl_h_i
);

  ///////////
  // Types //
  ///////////

  // The meta data type handed between the host's request and response channel
  typedef struct packed {
    logic lookup;
    logic aligned;
  } req_rsp_meta_t;

  localparam int unsigned MetaWidth = $bits(req_rsp_meta_t);

  // The fields of a request the filter answers itself, kept in the meta FIFO next to the meta data
  // with tag-only writes only
  typedef struct packed {
    logic                       host;
    logic [top_pkg::TL_AIW-1:0] source;
    logic [top_pkg::TL_SZW-1:0] size;
  } local_meta_t;

  localparam int unsigned LocalWidth = TagOnlyWrites ? $bits(local_meta_t) : 32'd0;
  localparam int unsigned FifoWidth  = MetaWidth + LocalWidth;

  localparam int unsigned AddrWidth = $bits(addr_t);

  // The fields of an access address that locate its capability tag.
  typedef struct packed {
    logic [AddrWidth-1:8] meta_word;
    logic           [7:3] bit_sel;
    logic           [2:0] rsvd;
  } meta_addr_t;


  /////////////
  // Signals //
  /////////////

  // Request handshaking signals
  logic tl_d_req_ready;
  logic tl_m_req_valid;
  logic tl_h_req_valid;

  // Input port of the meta FIFO
  logic          meta_req_valid;
  logic          meta_req_ready;
  req_rsp_meta_t meta_req;

  // Output port of the meta FIFO
  logic          meta_rsp_valid;
  logic          meta_rsp_ready;
  req_rsp_meta_t meta_rsp;

  // Meta FIFO contents, including the fields of requests the filter answers itself
  logic [FifoWidth-1:0] meta_fifo_wdata;
  logic [FifoWidth-1:0] meta_fifo_rdata;
  local_meta_t          local_req;
  local_meta_t          local_rsp_meta;

  // Whether a request goes to the host port, and whether its response comes from there
  logic host_fork;
  logic host_join;

  // Response the filter gives itself
  tlul_pkg::tl_d2h_t local_rsp_intg;

  // Whether we need to lookup or fork into the meta memory
  logic require_lookup;
  // Whether we need to join a meta lookup
  logic require_join;

  // Response handshaking signals
  logic tl_d_rsp_valid;
  logic tl_h_rsp_ready;
  logic tl_m_rsp_ready;

  // Unused meta response signals
  logic unused_m_rsp;

  // Meta responses, always accepted into a buffer until joined
  logic meta_buf_wready;
  logic meta_buf_valid;
  logic meta_buf_tag;
  logic meta_buf_err;

  // Tag bit store. We only do the lookup on the lower word of a capability to save
  // bandwidth into the meta memory. For the directly following meta word, we store
  // the capability
  logic tag_d_d, tag_d_q;

  logic tl_d_is_read;
  logic tl_d_is_write;
  logic tl_d_is_aligned;

  // Offset of the access within its tagged region, and whether it is in one at all
  meta_addr_t addr_stem;
  addr_t      meta_addr;
  logic       addr_tagged;

  // Unused address signals
  logic unused_addr;


  //////////
  // Fork //
  //////////

  assign tl_d_is_read    = tl_d_i.a_opcode == tlul_pkg::Get;
  assign tl_d_is_write   = tl_d_i.a_opcode == tlul_pkg::PutFullData ||
                           tl_d_i.a_opcode == tlul_pkg::PutPartialData;
  assign tl_d_is_aligned = !tl_d_i.a_address[2];

  ///////////////////////
  // Address Remapping //
  ///////////////////////

  // Check if access points to a capability-enabled region
  always_comb begin: proc_address_remap
    // defaults (an access outside every tagged region has no metadata)
    addr_stem   = '0;
    meta_addr   = '0;
    addr_tagged = 1'b0;

    if(tl_d_i.a_address >= MainSramBaseAddr && tl_d_i.a_address < MainSramTopAddr) begin
      addr_stem   = tl_d_i.a_address - MainSramBaseAddr;
      meta_addr   = MetaMainSramTagBase + (addr_t'(addr_stem.meta_word) << 32'd2);
      addr_tagged = 1'b1;
    end else if(tl_d_i.a_address >= NvmBaseAddr && tl_d_i.a_address < NvmTopAddr) begin
      addr_stem   = tl_d_i.a_address - NvmBaseAddr;
      meta_addr   = MetaNvmTagBase + (addr_t'(addr_stem.meta_word) << 32'd2);
      addr_tagged = 1'b1;
    end
  end

  assign bit_sel_m_o = addr_stem.bit_sel;
  assign unused_addr = ^addr_stem.rsvd;

  // We need to perform a lookup on 64-bit-aligned reads where the host hints
  // us a valid capability load or on any write. A lookup is only required if CHERIoT is enabled.
  assign require_lookup = prim_mubi_pkg::mubi4_test_true_strict(cheriot_ena_i) ?
                          addr_tagged       &&                                   // CHERIoT dev,
                          ((tl_d_is_read    &&                                   // and: Read,
                            tl_d_is_aligned &&                                   // 64-bit-aligned,
                            tag_d_i)        ||                                   // hinted cap
                            tl_d_is_write)                                     : // or write
                          1'b0;

  // With tag-only writes, a write is not forwarded to the host port
  assign host_fork = !(TagOnlyWrites && tl_d_is_write);

  // We only fork the meta channel if a lookup is required
  stream_fork_dynamic #(
    .N_OUP(32'd3)
  ) u_stream_fork_dynamic (
    .clk_i,
    .rst_ni,
    .valid_i    ( tl_d_i.a_valid                                   ),
    .ready_o    ( tl_d_req_ready                                   ),
    .sel_i      ( {1'b1, require_lookup, host_fork}                ),
    .sel_valid_i( tl_d_i.a_valid                                   ),
    .sel_ready_o( /* NOT CONNECTED */                              ),
    .valid_o    ( {meta_req_valid, tl_m_req_valid, tl_h_req_valid} ),
    .ready_i    ( {meta_req_ready, tl_m_i.a_ready, tl_h_i.a_ready} )
  );


  ////////////////
  // Meta Store //
  ////////////////

  // Assemble meta data between host's request and response channel.
  assign meta_req = '{
    lookup:  require_lookup,
    aligned: tl_d_is_aligned
  };

  assign local_req = '{
    host:   host_fork,
    source: tl_d_i.a_source,
    size:   tl_d_i.a_size
  };

  // The local fields only occupy FIFO bits with tag-only writes
  assign meta_fifo_wdata = FifoWidth'({local_req, meta_req});
  assign meta_rsp        = req_rsp_meta_t'(meta_fifo_rdata[MetaWidth-1:0]);

  prim_fifo_sync #(
    .Width(FifoWidth),
    .Pass(1'b0),
    .Depth(NumOutstanding),
    .NeverClears(1'b1)
  ) u_prim_fifo_sync_align (
    .clk_i,
    .rst_ni,
    .clr_i   ( 1'b0           ),
    .wvalid_i( meta_req_valid ),
    .wready_o( meta_req_ready ),
    .wdata_i ( meta_fifo_wdata),
    .rvalid_o( meta_rsp_valid ),
    .rready_i( meta_rsp_ready ),
    .rdata_o ( meta_fifo_rdata),
    .full_o  (                ),
    .depth_o (                ),
    .err_o   (                )
  );


  //////////
  // Join //
  //////////

  // Unjoined lookups are bounded by the meta FIFO's entries plus the one lookup the fork can issue
  // while that FIFO is full, so a buffer one entry deeper never refuses a response.
  prim_fifo_sync #(
    .Width(2),
    .Pass(1'b1),
    .Depth(NumOutstanding + 32'd1)
  ) u_prim_fifo_sync_meta_rsp (
    .clk_i,
    .rst_ni,
    .clr_i   ( 1'b0                        ),
    .wvalid_i( tl_m_i.d_valid              ),
    .wready_o( meta_buf_wready             ),
    .wdata_i ( {tag_m_i, tl_m_i.d_error}   ),
    .rvalid_o( meta_buf_valid              ),
    .rready_i( tl_m_rsp_ready              ),
    .rdata_o ( {meta_buf_tag, meta_buf_err}),
    .full_o  (                             ),
    .depth_o (                             ),
    .err_o   (                             )
  );

  // We join in exactly the transactions we forked.
  assign require_join = meta_rsp.lookup;
  assign host_join    = local_rsp_meta.host;

  stream_join_dynamic #(
    .N_INP(32'd3)
  ) u_stream_join_dynamic (
    .inp_valid_i( {meta_rsp_valid, meta_buf_valid, tl_h_i.d_valid} ),
    .inp_ready_o( {meta_rsp_ready, tl_m_rsp_ready, tl_h_rsp_ready} ),
    .sel_i      ( {1'b1, require_join, host_join} ),
    .oup_valid_o( tl_d_rsp_valid ),
    .oup_ready_i( tl_d_i.d_ready )
  );


  //////////////////////////
  // Stick Capability Tag //
  //////////////////////////

  assign tag_m_o = tag_d_i;

  always_comb begin: proc_sticky_tag_d_o
    tag_d_d = tag_d_q;
    tag_d_o = meta_rsp.aligned ? require_join && meta_buf_tag : tag_d_q;
    if(tl_d_o.d_valid && tl_d_i.d_ready) begin
      if(meta_rsp.aligned) begin
        tag_d_d = require_join && meta_buf_tag;
      end else begin
        tag_d_d = 1'b0;
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_store_r_cap_tag
    if(!rst_ni) begin
      tag_d_q <= 1'b0;
    end else begin
      tag_d_q <= tag_d_d;
    end
  end


  ////////////////////
  // TL connections //
  ////////////////////

  // We forward the host requests to both endpoints
  always_comb begin: proc_connect_tl_req
    tl_h_o         = tl_d_i;
    tl_h_o.a_valid = tl_h_req_valid;
    tl_h_o.d_ready = tl_h_rsp_ready;

    // We inject the meta address here
    tl_m_o                 = tl_d_i;
    tl_m_o.a_address       = meta_addr;
    tl_m_o.a_user.cmd_intg = tlul_pkg::get_cmd_intg(tl_m_o);
    tl_m_o.a_valid         = tl_m_req_valid;
    tl_m_o.d_ready         = meta_buf_wready;
  end

  // We disregard all of the meta SRAM response except for the tag bit and the error bit
  always_comb begin: proc_connect_tl_rsp
    tl_d_o         = tl_h_i;
    tl_d_o.d_error = tl_d_o.d_error || (require_join && meta_buf_err);
    if (!host_join) begin
      tl_d_o = local_rsp_intg;
    end
    tl_d_o.a_ready = tl_d_req_ready;
    tl_d_o.d_valid = tl_d_rsp_valid;
  end

  // Tag-only writes are answered by the filter itself: the meta response only carries the error,
  // and a write without a tag update is refused.
  if (TagOnlyWrites) begin : gen_local_rsp
    tlul_pkg::tl_d2h_t local_rsp;
    logic              unused_local_rsp_intg;

    assign local_rsp_meta = local_meta_t'(meta_fifo_rdata[FifoWidth-1:MetaWidth]);

    always_comb begin : proc_local_rsp
      local_rsp          = tlul_pkg::TL_D2H_DEFAULT;
      local_rsp.d_opcode = tlul_pkg::AccessAck;
      local_rsp.d_size   = local_rsp_meta.size;
      local_rsp.d_source = local_rsp_meta.source;
      local_rsp.d_error  = require_join ? meta_buf_err : 1'b1;
    end

    tlul_rsp_intg_gen #(
      .EnableRspIntgGen (1'b1),
      .EnableDataIntgGen(1'b1)
    ) u_tlul_rsp_intg_gen_local (
      .tl_i(local_rsp),
      .tl_o(local_rsp_intg)
    );

    // The handshake comes from the join
    assign unused_local_rsp_intg = ^{local_rsp_intg.a_ready, local_rsp_intg.d_valid};
  end else begin : gen_no_local_rsp
    logic unused_local_meta;
    assign unused_local_meta = ^{local_req.source, local_req.size,
                                 local_rsp_meta.source, local_rsp_meta.size};

    assign local_rsp_meta = '{host: 1'b1, default: '0};
    assign local_rsp_intg = tlul_pkg::TL_D2H_DEFAULT;
  end

  // The response and data integrity is not checked, as both the RMW and the tag filter are
  // lock-stepped.
  assign unused_m_rsp = ^{tl_m_i.d_data,
                          tl_m_i.d_opcode,
                          tl_m_i.d_param,
                          tl_m_i.d_sink,
                          tl_m_i.d_size,
                          tl_m_i.d_source,
                          tl_m_i.d_user
                        };

  ////////////////
  // Assertions //
  ////////////////

  // Meta FIFO has to be valid when device port handshakes its response
  `ASSERT(MetaRspValidOnDHs_A, (tl_d_o.d_valid && tl_d_i.d_ready) |-> meta_rsp_valid)

  // The meta path never waits on a join
  `ASSERT(MetaRspAlwaysAccepted_A, tl_m_i.d_valid |-> meta_buf_wready)

endmodule
