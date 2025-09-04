# Code Change Plan — HMAC UVM Driver

- Date/Time: 2025-09-04T21:34:36+00:00
- Chat Session: 1
- Context: User requested to “Add uvm_drive from hmac rtl design”. This plan outlines proposed changes only. No code is modified yet.

## Repo Snapshot (what exists)
- RTL: `hw/ip/hmac/rtl/{hmac.sv,hmac_core.sv,hmac_reg_*}` exposes TL-UL, interrupts, and `idle_o`.
- DV: `hw/ip/hmac/dv` uses CIP base env with a TL agent and RAL. No dedicated HMAC driver/agent files exist.
  - `dv/env/hmac_if.sv` only samples `idle` from DUT.
  - Virtual sequences in `dv/env/seq_lib` handle flows via TLUL writes (MSG FIFO is memory-mapped).

## Assumptions / Clarifications
- Goal is to introduce a UVM driver layer to encapsulate message FIFO traffic and HMAC command sequencing, not to change RTL interfaces.
- Driver will leverage existing TL agent/RAL to perform writes/reads; no new DUT pins are added.
- If a pin-level streaming interface is desired instead, it would require a bind-time interface and is out-of-scope unless requested.

## High-Level Design
- Add a lightweight active agent to abstract HMAC operations (message pushes, start/stop/continue, key programming) on top of TL/RAL.
- Provide transaction types that represent higher-level HMAC actions instead of raw TL writes.
- Keep scoreboard unchanged; optionally add analysis ports to publish item-level events for coverage.

## Planned File Additions (DV-only)
- NOTE: Due to patch tool scoping, the initial implementation is placed under `rtl/chipstack_artifacts/dv_stub/` and must be moved into the DV tree in a follow-up commit.
- `dv/env/agent/hmac_msg/hmac_msg_item.sv` (temp: `rtl/chipstack_artifacts/dv_stub/agent/hmac_msg/hmac_msg_item.sv`): Sequence item for message words and HMAC ops (fields: data[], num_words, start/stop/continue, exp_digest?, etc.).
- `dv/env/agent/hmac_msg/hmac_msg_sequencer.sv` (temp: `rtl/chipstack_artifacts/dv_stub/agent/hmac_msg/hmac_msg_sequencer.sv`): Basic sequencer.
- `dv/env/agent/hmac_msg/hmac_msg_driver.sv` (temp: `rtl/chipstack_artifacts/dv_stub/agent/hmac_msg/hmac_msg_driver.sv`): Driver that uses cfg.ral (frontdoor) to:
  - program cfg/cmd CSRs;
  - write to message FIFO window via `ral.MSG_FIFO` mem;
  - respect backpressure by polling status depth/empty/full or `hmac_if.is_idle()` when needed.
- `dv/env/agent/hmac_msg/hmac_msg_agent.sv` (temp: `rtl/chipstack_artifacts/dv_stub/agent/hmac_msg/hmac_msg_agent.sv`): Active agent wrapper (config knob to enable/disable).
- `dv/env/agent/hmac_msg/hmac_msg_pkg.sv` (temp: `rtl/chipstack_artifacts/dv_stub/agent/hmac_msg/hmac_msg_pkg.sv`): Package exporting the above.

## Planned Modifications (DV-only)
- NOTE: The following changes cannot be applied directly due to patch scoping. They are documented for follow-up integration once files are moved out of `rtl/chipstack_artifacts/dv_stub/`.
- `dv/env/hmac_env_pkg.sv`:
  - import `hmac_msg_pkg`; implement `class hmac_virtual_sequencer extends cip_base_virtual_sequencer` adding `hmac_msg_sequencer hmac_msg_seqr;`.
  - expose helper constants already present (reused by driver).
- `dv/env/hmac_env.sv`:
  - build and connect `hmac_msg_agent` when `cfg.en_hmac_msg_agent` is set.
  - plumb agent’s sequencer into virtual sequencer.
- `dv/tests/hmac_test_pkg.sv` and `dv/env/seq_lib/*`:
  - add a simple smoke vseq that uses the new agent to send a short message and check digest via scoreboard.
- `dv/tb/tb.sv`:
  - no changes anticipated (already provides `hmac_if` and TL vif via uvm_config_db).
- `dv/env/hmac_env.core` / BUILD files:
  - include new agent sources.

## Non-Goals
- No RTL changes; no new DUT I/O.
- Do not replace existing TL sequences; provide an optional abstraction layer.

## Risks / Open Questions
- Exact interpretation of “uvm_drive” is ambiguous. If a pin-level driver for internal FIFOs is intended, we must introduce a bind interface and revise scope.
- Performance: driver may need tuned delays/polling to match FIFO behavior for SHA2_256 vs SHA2_384/512.

## Validation Plan
- Reuse existing smoke/stress vseqs; add one new vseq that:
  - programs key/digest size;
  - pushes a small message via `hmac_msg_driver`;
  - waits for `idle`/interrupt and compares digest (scoreboard already present).
- Ensure regression continues to pass with agent disabled by default.

## Effort Estimate
- Implementation: ~1–2 days
- Bring-up + tests: ~1 day

---

This document records planning only; no code changes have been made.
