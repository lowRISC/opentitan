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

<%text>## Non-Maskable Interrupts</%text>

The wrapper raises the non-maskable interrupt (NMI) of Ibex for two sources:
* The escalation signal from the alert handler on ``esc_tx_i``.
* The watchdog bark from the AON timer on ``nmi_wdog_i``.

An NMI is raised while a source is set in both [`NMI_STATE`](registers.md#nmi_state) and [`NMI_ENABLE`](registers.md#nmi_enable).

Software can both set and clear the bits of [`NMI_ENABLE`](registers.md#nmi_enable).
An enabled source is therefore only truly non-maskable once software also clears [`NMI_ENABLE_REGWEN`](registers.md#nmi_enable_regwen), which locks [`NMI_ENABLE`](registers.md#nmi_enable) until the next reset.
A boot stage that enables NMIs can leave the lock to a later stage, so that the owner of that stage decides which sources stay enabled.


<%text>## Fetch Enable</%text>

Ibex has a top-level fetch enable input (``fetch_enable_i``), which uses the same multi-bit encoding used by the lifecycle controller.
When Ibex fetch is disabled it will cease to execute, but will complete instructions currently in the pipeline.
Ibex fetch is enabled when all of the following conditions are met:
  - The lifecycle controller has enabled it
  - The power manager has enabled it
  - No fatal internal error has been seen ([`FATAL_CORE_ERR`](registers.md#err_status))

<%text>### Local Escalation Path</%text>

When a fatal internal error sets [`FATAL_CORE_ERR`](registers.md#err_status), which also raises the ``fatal_hw_err`` alert, Ibex fetch is disabled and will remain disabled until ``rv_core_ibex`` is reset.
The other causes of the ``fatal_hw_err`` alert, such as integrity errors, do not disable fetch locally; their escalation is left to the alert handler.

<%text>## Lockstep</%text>

When `SecureIbex` is set, Ibex runs a shadow core in lockstep with the main core, `LockstepOffset` cycles behind, and compares their outputs (see the [Ibex documentation](https://ibex-core.readthedocs.io/en/latest/03_reference/security.html#dual-core-lockstep)).
The wrapper extends this comparison to its bus logic.
The requests of the shadow core go through a second copy of the address translation and of the TL-UL adapters, which see the responses of the main core delayed by `LockstepOffset` cycles.
Their TL-UL requests are compared with the ones of the main core, delayed alike.
A mismatch is a fatal core error and raises the ``fatal_hw_err`` alert.
The comparison of the data and instruction interfaces pauses for `LockstepOffset` + 1 cycles from a write to the address translation registers.
% if cheriot_available:

The core and its TRVK filter form one unit, so the shadow core has its own TRVK filter.
Ibex compares the encoded request tag itself, and the revocation bitmap interface has its own shadow TL-UL adapter.

<%text>## Execution Mode Switch</%text>

When CHERIoT is available, Ibex is synthesized with a CHERIoT-capable base ISA and can execute either the base RV32 ISA with ePMP, or the CHERIoT ISA.
The two memory protection schemes are mutually exclusive, so exactly one of them is active at a time.
The Ibex wrapper contains a write-once switch that selects between them.
It resets unlocked in ePMP mode.

The selected mode gates the CHERIoT memory subsystem and Ibex.

<%text>### Write Sequence</%text>

The switch is programmed through three registers:

1. Write the desired mode to [`CHERIOT_ENA`](registers.md#cheriot_ena): `MuBi4True` selects CHERIoT mode, `MuBi4False` keeps the system in ePMP mode.
2. Write its complement to [`CHERIOT_ENA_BAR`](registers.md#cheriot_ena_bar).
3. With interrupts disabled, write `MuBi4True` to [`CHERIOT_LOCK`](registers.md#cheriot_lock) from Ibex.
4. Poll until the core runs in the selected mode, before the first instruction that depends on it, and only then enable interrupts again.

The `MuBi4True` write to [`CHERIOT_LOCK`](registers.md#cheriot_lock) is what advances the switch: it samples [`CHERIOT_ENA`](registers.md#cheriot_ena) and [`CHERIOT_ENA_BAR`](registers.md#cheriot_ena_bar) and latches the selected mode.
All values are decoded strictly: [`CHERIOT_ENA`](registers.md#cheriot_ena) must be exactly `MuBi4True` or `MuBi4False`, [`CHERIOT_ENA_BAR`](registers.md#cheriot_ena_bar) exactly its complement, and [`CHERIOT_LOCK`](registers.md#cheriot_lock) exactly `MuBi4True`.
From then on the mode is fixed until `rv_core_ibex` is reset.
The lock also clears [`CHERIOT_ENA_REGWEN`](registers.md#cheriot_ena_regwen), so later writes to [`CHERIOT_ENA`](registers.md#cheriot_ena) and [`CHERIOT_ENA_BAR`](registers.md#cheriot_ena_bar) are ignored, and further writes to [`CHERIOT_LOCK`](registers.md#cheriot_lock) have no effect.
A change of [`CHERIOT_ENA`](registers.md#cheriot_ena) or [`CHERIOT_ENA_BAR`](registers.md#cheriot_ena_bar) in the staging cycles after the lock fails the re-check and moves the switch into the error state.

The switch raises the core's enable two cycles before the CHERIoT memory subsystem's (see [Enable Distribution](#enable-distribution)).
A capability access that reached the memory subsystem before its enable would lose the tag of a stored capability, or load a capability untagged.
The poll rules this out: no general-purpose register holds a tagged capability after the switch, so at least the poll's branch and an instruction that derives a capability separate the read that returns the new mode from the first access.

<%text>### Enable Distribution</%text>

The switch resets with a compare enable on and all other enables off.
After the lock, it raises the other enables one per cycle: the core's, the lockstep shadow core's, the CHERIoT memory subsystem's and the memory subsystem shadow's.
For CHERIoT mode, it turns the compare enable off together with the core's enable, and on again one cycle after the last one; for ePMP mode, no enable changes and the compare enable stays on.
In every staging cycle it checks [`CHERIOT_ENA`](registers.md#cheriot_ena) and [`CHERIOT_ENA_BAR`](registers.md#cheriot_ena_bar) again.
Each enable comes from its own flop, which the switch writes only on the step that changes it, or with an invalid value on a step into the error state, and otherwise holds, so a fault on the switch state alone cannot set the enables of the other mode.
Each enable passes one layer of buffers that synthesis keeps, so its multi-bit encoding survives up to the receivers, and none of them adds a flop, so Ibex and the memory subsystem see the enables in the switch's order.
The core's enable goes to Ibex and to the debug module, and the compare enable to both comparisons, through a `prim_mubi4_sync` with one copy each; the other enables go through a `prim_mubi4_sender` without a flop.

Ibex receives the core's and the shadow core's enable on separate inputs and, while the compare enable is on, checks that both are valid and equal; the memory subsystem does the same with the enables of its two lockstep copies.
A mismatch or an invalid enable raises a fatal alert: in Ibex an internal major alert, which sets [`FATAL_CORE_ERR`](registers.md#err_status), in the memory subsystem its `fatal_fault` alert.
Both delay the compare enable by `LockstepOffset - 1` cycles, as they do the second copy's enable, and the switch turns the compare enable off in the cycle the core's enable changes and two cycles before the memory subsystem's, so `LockstepOffset` must be 1 in Ibex and at most 3 in the memory subsystem.
The shadow core's enable trails the core's by one cycle only while Ibex's clock runs, so Ibex writes [`CHERIOT_LOCK`](registers.md#cheriot_lock) itself: a write over the debug module's system bus while Ibex sleeps with its clock gated can raise a lockstep alert.

<%text>### Switching to CHERIoT Mode at Runtime</%text>

Switching from RV32I to CHERIoT mode at runtime needs the software sequence described in the [Ibex documentation](https://ibex-core.readthedocs.io/en/latest/03_reference/cheriot.html).
On Earl Grey, it consists of the following steps, which `sw/device/tests/cheriot_smoketest.S` implements:

1. Disable interrupts until `mtcc` is set up in CHERIoT mode.
   NMIs are not masked by this.
   Unless [`NMI_ENABLE`](registers.md#nmi_enable) is already locked, software can disable them during the switch and only lock them afterwards.
   Otherwise the `mtvec` handler must work in both modes, including a mode change while it runs.
   As an NMI is fatal, the handler can raise a fatal alert and stop.
2. Zero-initialize the meta SRAM, which holds the capability tags and the revocation bitmap.
3. Save `cpuctrlsts`, clear `cpuctrlsts.dummy_instr_en` and write zero to `x16`-`x31`.
4. Write `MuBi4True` to [`CHERIOT_ENA`](registers.md#cheriot_ena) and `MuBi4False` to [`CHERIOT_ENA_BAR`](registers.md#cheriot_ena_bar).
5. Write `MuBi4True` to [`CHERIOT_LOCK`](registers.md#cheriot_lock) and poll `misa` until `misa.E` is set.
   In CHERIoT mode, Ibex is set to RV32E, and in ePMP mode on Earl Grey to RV32I, so `misa.E` tells the two modes apart.
   Until then, only use 32-bit instructions that behave the same in both modes.
6. Restore `cpuctrlsts`, and set up `mtcc` before any instruction that can trap.

Debug is not supported during the switch.

In CHERIoT mode, a key renewal or initialization of `sram_ctrl_meta`, `sram_ctrl_main` or `sram_ctrl_sec` replaces the data under existing tags, which then loads as valid capabilities.
Only trusted code should therefore have access to their `CTRL` registers, or their `CTRL_REGWEN` can be cleared before the switch.

CHERIoT mode turns off the ePMP protection, including locked entries.
The boot stage that configures the ePMP should therefore make the mode decision, or lock ePMP mode, before it hands over to less trusted code.

<%text>### Error State</%text>

The switch has a terminal error state.
It is entered when [`CHERIOT_LOCK`](registers.md#cheriot_lock) is written with a value other than `MuBi4True`, when [`CHERIOT_ENA`](registers.md#cheriot_ena) holds an invalid multi-bit value or [`CHERIOT_ENA_BAR`](registers.md#cheriot_ena_bar) does not hold its complement at that moment or in any staging cycle after it, or when the switch state is corrupted.

In the error state, the `fatal_hw_err` alert is raised, and every step into it writes an invalid multi-bit value into all enables of the switch.
For an invalid state encoding, the enables become invalid one cycle after the alert, with the step into the error state.

Consumers of the enables are expected to escalate invalid values. Ibex does so by detecting the invalid multi-bit mode on its CHERIoT enables and raising an internal major alert. This sets [`FATAL_CORE_ERR`](registers.md#err_status) and halts instruction fetch.
The CHERIoT memory subsystem raises its `fatal_fault` alert: the invalid compare enable turns its enable comparison on, which flags the invalid enables.

Both the error status bit and the disabled fetch state are sticky.
Ibex will not resume execution, and the switch error state cannot be cleared, until `rv_core_ibex` is reset.

<%text>## Capability Tag Sideband</%text>

Every data access of Ibex carries a capability validity tag next to the TL-UL structs of the data port.
`cored_tag_h2d_o` goes with the request: it is the tag of a store, or on a load the hint that it loads a capability.
`cored_tag_d2h_i` comes with the response: it is the tag of the loaded capability.
Both are `mubi4_t` towards the CHERIoT memory subsystem (`cheriot_mem_sys`).
Ibex encodes the request tag and decodes the response tag itself as `ibex_mubi_t`, in each lockstep copy, so the lockstep compares the encoded request tag and the shadow core decodes its own copy of the response tag.
The wrapper converts between `ibex_mubi_t` and `mubi4_t` by swapping bits 1 and 0, so the tag stays multi-bit encoded on its whole way, including inside the data FIFO.
The encoding adds no flop, so the tag stays in the cycle of its TL-UL beat.

Decoding is strict: only `MuBi4True` reads as tagged.
An invalid encoding therefore reads as untagged.
A data request or response with an invalid encoding at the input or the output of the data FIFO also sets [`FATAL_INTG_ERR`](registers.md#err_status) and raises the `fatal_hw_err` alert.
Like other integrity errors, it does not disable fetch locally (see [Local Escalation Path](#local-escalation-path)); its escalation is left to the alert handler.
% endif
