# Theory of Operation

<%text>## Simple Address Translation</%text>

The wrapper supports a simple address translation scheme.
The goal of the scheme is to provide hardware support for A/B software copies.

Each copy of the software is stored at a different location.
Depending upon which execution slot is active, a different copy is used.
This creates an issue because each copy of software has different addresses and thus must be linked differently.
Ideally, software should be able to assume one address all the time, and the hardware should remap to the appropriate physical location.

The translation scheme is based on NAPOT (natural alignment to power of two).
Software picks a matching region and also a remap address.
When an incoming transaction matches the selected power-of-2 region, it is redirected to the new address.
If a transaction does not match, then it is directly passed through.

This allows software to place the executable code at a virtual address in the system and re-map that to the appropriate physical block.

There are separate translations controls for instruction and data.
Each control contains two programmable regions (2 for instruction and 2 for data).
If a transaction matches multiple regions, the lowest indexed region has priority.

For details on how to program the related registers, please see [`IBUS_ADDR_MATCHING_0`](registers.md#ibus_addr_matching) and [`IBUS_REMAP_ADDR_0`](registers.md#ibus_remap_addr).

<%text>### Translation and Instruction Caching</%text>

The simple address translation scheme used in this design is not aware of the processor context, specifically, any instruction caching done in the core.
This means if the address translation scheme were to change, instructions that are already cached may not reflect the updated address setting.

In order to correctly utilize simple address translation along with instruction caching, it is recommended that after the address is updated a `FENCE.I` instruction is issued.
The `FENCE.I` instruction forces the instruction cache to flush, and this aligns the core to the new address setting.

<%text>## Random Number Generation</%text>

The wrapper has a connection to the [Entropy Distribution Network (EDN)](../../../../ip/edn/README.md) with a register based interface.
The [`RND_DATA`](registers.md#rnd_data) register provides 32-bits directly from the EDN.
[`RND_STATUS.RND_DATA_VALID`](registers.md#rnd_status) indicates if the data in [`RND_DATA`](registers.md#rnd_data) is valid or not.
A polling style interface is used to get new random data.
Any read to [`RND_DATA`](registers.md#rnd_data) when it is valid invalidates the data and triggers an EDN request for new data.
Software should poll [`RND_STATUS.RND_DATA_VALID`](registers.md#rnd_status) until it is valid and then read from [`RND_DATA`](registers.md#rnd_data) to get the new random data.
Either the data is valid or a request for new data is pending.
It is not possible to have a state where there is no valid data without new data being requested.

Upon reset [`RND_DATA`](registers.md#rnd_data) is invalid.
A request is made to the EDN immediately out of reset, this will not be answered until the EDN is enabled.
Software should take care not to enable the EDN until the entropy complex configuration is as desired.
When the entropy complex configuration is changed reading [`RND_DATA`](registers.md#rnd_data) when it is valid will suffice to flush any old random data to trigger a new request under the new configuration.
If a EDN request is pending when the entropy complex configuration is changed ([`RND_STATUS.RND_DATA_VALID`](registers.md#rnd_status) is clear), it is advisable to wait until it is complete and then flush out the data to ensure the fresh value was produced under the new configuration.

<%text>## Crash Dump Collection</%text>

In general, when the CPU encounters an error, it is software's responsibility to collect error status and supply it for debug.

However, there are situations where it may not be possible for software to collect any error logging.
These situations include but are not limited to:
* A hung transaction that causes watchdog to expire.
* A double fault that causes the processor to stop execution.
* An alert escalation that directly resets the system without any software intervention.

Under these situations, the software has no hints as to where the error occurred.
To mitigate this issue, Ibex provides crash dump information that can be directly captured in the `rstmgr` for last resort debug after the reset event.

The Ibex crash dump state contains 5 words of debug data:
* word 0: The last exception address (`mtval`)
* word 1: The last exception PC (`mepc`)
* word 2: The last data access address
* word 3: The next PC
* word 4: The current PC

The crash dump information transmitted to the `rstmgr` contains 7 words of debug data and a 1-bit valid indication:
* words 0-4: The current crash dump state
* word 5: The previous exception address (`mtval`)
* word 6: The previous exception PC (`mepc`)
* MSB: Previous state valid indication.

Under normal circumstances, only the current crash dump state is valid.
When the CPU encounters a double fault, the current crash dump is moved to previous, and the new crash dump is shown in current.

This allows the software to see both fault locations and debug accordingly.

In terms of how the crash state information can be used, the following are a few examples.

<%text>### Hung Transaction</%text>

Assuming the system has a watchdog counter setup, when a CPU transaction hangs the bus (accessing a device whose clock is not turned on or is under reset), the PC and bus access freeze in place until the watchdog resets the system.
Upon reset release, software can check the last PC and data access address to get an idea of what transaction might have caused the bus to hang.

<%text>### Double Exception</%text>

If the software has some kind of error and encounters two exceptions in a row, the previous exception PC and address show the location of the first exception, while the current exception address and PC show the location of the most recent exception.


<%text>## Fetch Enable</%text>

Ibex has a top-level fetch enable input (``fetch_enable_i``), which uses the same multi-bit encoding used by the lifecycle controller.
When Ibex fetch is disabled it will cease to execute, but will complete instructions currently in the pipeline.
Ibex fetch is enabled when all of the following conditions are met:
  - The lifecycle controller has enabled it
  - The power manager has enabled it
  - A ``fatal_hw_err`` alert hasn't been raised

<%text>### Local Escalation Path</%text>

When the ``fatal_hw_err`` alert is raised Ibex fetch is disabled and will remain disabled until ``rv_core_ibex`` is reset.
% if cheriot_available:

<%text>## Execution Mode Switch</%text>

When CHERIoT is available, Ibex is synthesized with a CHERIoT-capable base ISA and can execute either the base RV32 ISA with ePMP, or the CHERIoT ISA.
The two memory protection schemes are mutually exclusive, so exactly one of them is active at a time.
The Ibex wrapper contains a write-once switch that selects between them.
It resets unlocked in ePMP mode.

The selected mode gates the CHERIoT memory subsystem, but is not routed to Ibex yet.

<%text>### Write Sequence</%text>

The switch is programmed through two registers:

1. Write the desired mode to [`CHERIOT_ENA`](registers.md#cheriot_ena): `MuBi4True` selects CHERIoT mode, `MuBi4False` keeps the system in ePMP mode.
2. Write `MuBi4True` to [`CHERIOT_LOCK`](registers.md#cheriot_lock).

The `MuBi4True` write to [`CHERIOT_LOCK`](registers.md#cheriot_lock) is what advances the switch: it samples [`CHERIOT_ENA`](registers.md#cheriot_ena) and latches the selected mode.
Both values are decoded strictly: [`CHERIOT_ENA`](registers.md#cheriot_ena) must be exactly `MuBi4True` or `MuBi4False`, and [`CHERIOT_LOCK`](registers.md#cheriot_lock) exactly `MuBi4True`.
From then on the mode is fixed until `rv_core_ibex` is reset.
Further writes to either register have no effect.

<%text>### Error State</%text>

The switch has a terminal error state.
It is entered when [`CHERIOT_LOCK`](registers.md#cheriot_lock) is written with a value other than `MuBi4True`, when [`CHERIOT_ENA`](registers.md#cheriot_ena) holds an invalid multi-bit value at that moment, or when the switch state is corrupted.

In the error state, the `fatal_hw_err` alert is raised, which also disables Ibex fetch through the local escalation path described above.
The state is only left by resetting `rv_core_ibex`.
In the error state the mode output is driven to an invalid multi-bit value.
The consumers are expected to escalate.
% endif
