# Summary — Add uvm_drive from HMAC RTL design

- Task: Add a UVM driver ("uvm_drive") for the HMAC IP, introducing a message-level UVM agent/driver on top of TL/RAL without changing RTL.
- Plan (concise): Implement a lightweight HMAC message agent (item, sequencer, driver, agent, pkg) as DV stubs under `rtl/chipstack_artifacts/dv_stub/`, then move and wire into the DV environment in a follow-up.

Files touched (Added/Edited/Deleted):
- Added: `hw/ip/hmac/rtl/chipstack_artifacts/code_change_notes.md`
- Added: `hw/ip/hmac/rtl/chipstack_artifacts/code_change_plan.md`
- Added: `hw/ip/hmac/rtl/chipstack_artifacts/dv_stub/agent/hmac_msg/hmac_msg_agent.sv`
- Added: `hw/ip/hmac/rtl/chipstack_artifacts/dv_stub/agent/hmac_msg/hmac_msg_driver.sv`
- Added: `hw/ip/hmac/rtl/chipstack_artifacts/dv_stub/agent/hmac_msg/hmac_msg_item.sv`
- Added: `hw/ip/hmac/rtl/chipstack_artifacts/dv_stub/agent/hmac_msg/hmac_msg_pkg.sv`
- Added: `hw/ip/hmac/rtl/chipstack_artifacts/dv_stub/agent/hmac_msg/hmac_msg_sequencer.sv`
- Added: `hw/ip/hmac/rtl/chipstack_artifacts/dv_stub/seq_lib/hmac_msg_smoke_vseq.sv`
- Added: `hw/ip/hmac/rtl/chipstack_artifacts/git_manager.md`
- Added: `hw/ip/hmac/rtl/logs/sessions/2025/09/04/rollout-2025-09-04T21-32-09-cb852da2-369a-4fe1-a5e6-82d34ba9c474.jsonl`
- Added: `hw/ip/hmac/rtl/logs/sessions/2025/09/04/rollout-2025-09-04T21-33-38-141c5378-5853-4412-8176-e7815359a22b.jsonl`
- Added: `hw/ip/hmac/rtl/logs/sessions/2025/09/04/rollout-2025-09-04T21-35-21-f47568d8-1588-4975-bc73-e74ed6d8e956.jsonl`
- Added: `hw/ip/hmac/rtl/logs/sessions/2025/09/04/rollout-2025-09-04T21-41-02-31428806-d5fd-4aa0-b5b6-dbae7324dcef.jsonl`

Git branch:
- `shivang-chipstack-chipstack-hmac-uvm-drive`

Pull Request:
- Create PR link: https://github.com/chipstack-ai/opentitan/pull/new/shivang-chipstack-chipstack-hmac-uvm-drive

Commit hash:
- `ffb2087d088a4f072ec3c9ceaa39e07e470f852e`

Confidence:
- High — artifacts and plan are complete; DV integration will follow by moving files into `dv/env` and wiring as outlined.

