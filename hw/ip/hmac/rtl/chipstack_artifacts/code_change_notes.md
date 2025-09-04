# Code Change Notes — HMAC UVM Driver

- Date/Time: 2025-09-04T21:40:00Z
- Chat Session: 1

Summary:
- Implemented a new UVM message-level driver (agent, sequencer, item) for HMAC as planned, but due to tool-scoped patch restrictions, placed sources under `rtl/chipstack_artifacts/dv_stub/` rather than `hmac/dv/env/agent/...`.
- No RTL behavior is modified. Artifacts are ready to be moved into the DV tree and wired as described in the plan.

Files Added (temporary location):
- `chipstack_artifacts/dv_stub/agent/hmac_msg/hmac_msg_pkg.sv`
- `chipstack_artifacts/dv_stub/agent/hmac_msg/hmac_msg_item.sv`
- `chipstack_artifacts/dv_stub/agent/hmac_msg/hmac_msg_sequencer.sv`
- `chipstack_artifacts/dv_stub/agent/hmac_msg/hmac_msg_driver.sv`
- `chipstack_artifacts/dv_stub/agent/hmac_msg/hmac_msg_agent.sv`
- `chipstack_artifacts/dv_stub/seq_lib/hmac_msg_smoke_vseq.sv` (example virtual seq usage)

Next Steps (manual move required):
- Move the above files into `hw/ip/hmac/dv/env/agent/hmac_msg/` and `hw/ip/hmac/dv/env/seq_lib/`.
- Import `hmac_msg_pkg` in `hmac_env_pkg.sv`, create a `hmac_virtual_sequencer` class that holds `hmac_msg_sequencer`, and enable optional agent instantiation in `hmac_env.sv` guarded by a new cfg knob `en_hmac_msg_agent`.
- Add the new sources to `hmac_env.core` file list.

