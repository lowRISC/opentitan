# OTP_MACRO Agent

`otp_macro_agent` is an agent for the OTP macro interface (`otp_ctrl_macro_pkg::otp_ctrl_macro_req_t` / `otp_ctrl_macro_rsp_t`).
When active, it acts as `otp_ctrl`: it sends `Init`, `Read`, `Write`, `ReadRaw`, `WriteRaw` and `Zeroize` commands to the block that stores the OTP contents, and collects the responses.
When passive, it only watches the interface.
It is built on the agent classes in [`dv_base_agent`](../dv_base_agent).

## Interface

`otp_macro_if` holds the request (`req`) and response (`rsp`) structs.
A request is accepted in the cycle where `req.valid` and `rsp.ready` are both high.
Some time later the responder pulses `rsp.rvalid` for a single cycle, with `rsp.rdata` and `rsp.err`.
Responses come back in request order.

The agent sets the interface's `if_mode`: `req` is only driven in `Host` mode (an active agent), and is left undriven in `Monitor` mode (a passive agent).
The interface checks that a request is held unchanged until it is accepted, and that a presented request is known.

## Components

* **Request item** (`otp_macro_req_seq_item`): the command, size, address and write data of one request, and the number of cycles to wait before presenting it.
  Its constraints match how `otp_ctrl` uses the interface: 1, 2 or 4 words, aligned to the transfer size.
* **Response item** (`otp_macro_rsp_seq_item`): the read data and error code of one response, and a handle to its request (`m_req`).
* **Sequence** (`otp_macro_cmd_seq`): sends one command, `m_req`, and collects its response in `m_rsp`.
  `m_rsp` is null if a reset interrupted the command.
* **Driver** (`otp_macro_driver`): waits the request's delay, then presents the request until it is accepted.
  It finishes the item at that point, so later requests can be sent while earlier ones wait for their responses.
  Each response is sent back to the sequence that sent the request.
* **Monitor** (`otp_macro_monitor`): records each accepted request, pairs it with the next response and writes the completed transaction (a response item holding its request) to the agent's `analysis_port`.
* **Sequencer** (`otp_macro_sequencer`): a typedef of `dv_base_sequencer`.

## Usage

The testbench instantiates `otp_macro_if`, connects `req` and `rsp` to the responder, and passes the interface to the environment, which puts it in the agent's configuration (`m_vif`).
Before the agent's `build_phase`, the environment sets the agent's configuration under the name `cfg` in `uvm_config_db`.
To send commands, a sequence starts `otp_macro_cmd_seq` on the agent's sequencer:

```systemverilog
otp_macro_cmd_seq seq = otp_macro_cmd_seq::type_id::create("seq");
if (!seq.randomize() with {m_req.m_cmd == otp_ctrl_macro_pkg::Read; m_req.m_size == 1;}) begin
  `uvm_fatal("rand_failed", "Failed to randomize the OTP command")
end
seq.start(otp_macro_sequencer_h);
// seq.m_rsp.m_rdata and seq.m_rsp.m_err hold the response
```

To have several commands waiting for responses at once, start sequences from parallel threads.
The first command after a reset must be `Init`.
