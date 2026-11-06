# OTP_MACRO Agent

`otp_macro_agent` plays `otp_ctrl` on the OTP macro interface (`otp_ctrl_macro_pkg::otp_ctrl_macro_req_t` / `otp_ctrl_macro_rsp_t`).
It sends `Init`, `Read`, `Write`, `ReadRaw`, `WriteRaw` and `Zeroize` commands to the block that stores the OTP contents, such as `rram_ctrl`, and collects the responses.
It is built on the agent classes in [`dv_base_agent`](../dv_base_agent) and only supports `Host` mode.

## Interface

`otp_macro_if` holds the request (`req`) and response (`rsp`) structs.
A request is accepted in the cycle where `req.valid` and `rsp.ready` are both high.
Some time later the responder pulses `rsp.rvalid` for a single cycle, with `rsp.rdata` and `rsp.err`.
Responses come back in request order.

The interface checks that a request is held unchanged until it is accepted, and that a presented request is known.

## Components

* **Item** (`otp_macro_item`): one complete transaction.
  The request fields (`cmd`, `size`, `addr`, `wdata`) are randomized, with constraints that match how `otp_ctrl` uses the interface: 1, 2 or 4 words, aligned to the transfer size.
  The response fields (`rdata`, `err`) are filled in once the response arrives.
* **Sequence** (`otp_macro_base_seq`): sends one request, with the fields set by the caller, and returns the completed transaction in `rsp_item`.
* **Driver** (`otp_macro_host_driver`): drives the request, holds it until it is accepted, waits for the response (with a timeout of `cfg.rsp_timeout_ns`) and copies `rdata` and `err` back into the item.
  It sends one request at a time.
* **Monitor** (`otp_macro_monitor`): records each accepted request, pairs it with the next response and writes the completed transaction to `analysis_port`.
  It also maintains `cfg.in_reset`.

The agent does not start any sequence by itself: the environment's virtual sequences decide which commands to send.
Checking and coverage depend on the responder, so they live in the environment that uses the agent.

## Usage

```systemverilog
// tb
otp_macro_if otp_macro_if (.clk(clk_otp), .rst_n(rst_otp_n));
// .otp_macro_i(otp_macro_if.req), .otp_macro_o(otp_macro_if.rsp)
uvm_config_db#(virtual otp_macro_if)::set(null, "*.env.m_otp_macro_agent", "vif", otp_macro_if);

// env
m_otp_macro_agent = otp_macro_agent::type_id::create("m_otp_macro_agent", this);
uvm_config_db#(otp_macro_agent_cfg)::set(this, "m_otp_macro_agent", "cfg",
                                         cfg.m_otp_macro_agent_cfg);
m_otp_macro_agent.monitor.analysis_port.connect(scoreboard.m_otp_macro_fifo.analysis_export);

// vseq
otp_macro_base_seq seq = otp_macro_base_seq::type_id::create("seq");
seq.cmd  = otp_ctrl_macro_pkg::Read;
seq.addr = 'h40;
seq.size = 1;
seq.start(p_sequencer.otp_macro_sequencer_h);
// seq.rsp_item.rdata and seq.rsp_item.err hold the response
```
