# Theory of Operation

## Block Diagram

![Block Diagram](../doc/block_diagram.svg)

When Flash mode is selected, the command parser accepts the first byte of the SPI MOSI line and then activates the flash submodules, such as Status, JEDEC, Read command, and Upload functionality.

The Status logic processes the three Read Status commands.
The SW may configure three bytes of the Flash Status CSR then the Status submodule returns the CSR data into the SPI MISO line.
The SW may configure the Read Status commands' opcodes.

The JEDEC submodule returns the JEDEC Manufacturer ID and Device ID.

The Read submodule processes the Read SFDP (Serial Flash Discoverable Parameters) command, and up to six different types of the read commands.
The read submodule receives address information from the SPI transaction, fetches the data from the read buffer in the DPSRAM, and returns the data on SPI lines (single, dual, or quad lines).
If the received address falls into the SW-programmable mailbox address space, the logic fetches data not from the read buffer but from the mailbox buffer in the DPSRAM.

SW may configure command information slots to upload the command into the FIFOs and the payload buffer in the DPSRAM.
SW may additionally let HW set the `BUSY` bit in the Status register when the HW uploads the command.

In Passthrough mode, the logic can filter the incoming transaction if the command is not permitted.
The SW may configure the logic to change a portion of the address and/or the first 4 bytes of the payload.

## SPI Flash and Passthrough Modes

### Command Information List

The HW provides SW-configurable command information entries ([`CMD_INFO`](registers.md#cmd_info) CSRs) that represent SPI commands and their settings.
SPI Device currently provides 28 command information entries: [`CMD_INFO_0`-`CMD_INFO_23`](registers.md#cmd_info) and
[`CMD_INFO_EN4B`](registers.md#cmd_info_en4b)-[`CMD_INFO_WRDI`](registers.md#cmd_info_wrdi).

The first 11 command entries (`CMD_INFO_0`-`CMD_INFO_10`) are assigned to specific HW submodules.

Index  | Assigned Submodule
-------|:-------------------
[2:0]  | Read Status
[3]    | Read JEDEC ID
[4]    | Read SFDP
[10:5] | Read Commands

The remaining 13 command entries are for generic SW use.

4 additional stripped-down command entries are provided for controlling address size ([`CMD_INFO_EN4B`](registers.md#cmd_info_en4b)/[`CMD_INFO_EX4B`](registers.md#cmd_info_ex4b))
and write enable/disable ([`CMD_INFO_WREN`](registers.md#cmd_info_wren)/[`CMD_INFO_WRDI`](registers.md#cmd_info_wrdi)). The commands are also handled by HW.

In Flash mode, or in Passthrough mode with the corresponding [`INTERCEPT_EN`](registers.md#intercept_en) fields set, the submodules directly return data on the MISO line (SD[1]) without SW intervention.
EN4B, EX4B, WREN and WRDI are always handled by HW in Passthrough mode.
If the Read Status and Read JEDEC ID commands are intercepted as above, only the *valid* and *opcode* fields in the corresponding command information entry are used.

Fields other than *opcode* and *valid* are primarily used to control the behaviour of passthrough mode logic, see [Output Enable Control](#output-enable-control) for more.

The *upload* and *busy* fields are used to control command upload in Flash and Passthrough modes, see [Command Upload](#command-upload) for more.

### Command Parser

![Command Parser block](../doc/cmdparse.svg)

The command parser (*cmdparse*) processes the first byte of the SPI transfer, and activates the processing submodule depending on the received opcode and the command information list described in the previous section.

The command parser looks for the received opcode byte in the *opcode* field of each command information entry.
If the opcode is found and the *valid* bit is set for that entry, the entry is *matched* and the submodule corresponding to the matched entry's index is activated (see [previous section](#command-information-list)).
In the unlikely case of multiple matching entries, the entry with the highest index is used.

If the matched command information slot entry not assigned to a HW submodule (`CMD_INFO_11`-`CMD_INFO_23`) and the *upload* field is set in the matched entry, the upload submodule is activated.

In Passthrough mode, the configuration of [`INTERCEPT_EN`](registers.md#intercept_en) determines whether the matched entry is processed (intercepted) by the corresponding HW submodule or passed-through.
EN4B, EX4B, WREN, and WRDI are always intercepted by HW.

### Status Control

If the received opcode matches one of the Read Status commands, the Status control module is activated and returns the corresponding status byte from the [`FLASH_STATUS`](registers.md#flash_status) register.
This register is not reset by CSb.
Bits other than [`BUSY`](registers.md#flash_status_busy) and [`WEL`](registers.md#flash_status_wel) are controlled by SW and have no special designation.

The `BUSY` bit is set by the upload submodule on a matched command with the *upload* and *busy* fields set.
SW may clear this bit when it completes the received command (for example, an Erase or Program operation), but it may not set the bit.

If the `BUSY` bit is set, the SPI Device IP blocks the passthrough interface in Passthrough mode.
The blocking of the interface occurs in the SPI transaction idle state (CSb high).
When SW clears the `BUSY` bit, it is applied to the status register in the SPI clock domain when SPI clock toggles, meaning the update happens when the next SPI transaction is received.
The `BUSY` bit seen in the `FLASH_STATUS` CSR is the synchronized value of the busy status bit in the SPI clock domain.
Due to the CDC latency, SW may observe a long delay before the updated value (`BUSY` clear) is visible.

The `WEL` bit is updated by HW when the [WREN](registers.md#cmd_info_wren) or [WRDI](registers.md#cmd_info_wrdi) commands are received.
SW may clear this bit when it completes the received commands, but it may not set the bit.

The SW update of the status register via [`FLASH_STATUS`](registers.md#flash_status) is not instantaneous.
The IP first stores the SW request into the asynchronous FIFO and then the request is processed in the SPI clock domain.
The request updates the staged registers, which are latched into the committed registers when CSb is de-asserted.
SW sees the committed registers when reading the [`FLASH_STATUS`](registers.md#flash_status) CSR.

The attached host system reads the committed registers using the Read Status commands.
This scheme is to guarantee the atomicity of the status register.
On every 8th SPI clock cycle, the SPI domain commits the latest resolved value to the committed registers.
Each byte beat of the Read Status commands will return the latest committed value of the targeted register.
A Read Status command can thus repeatedly poll the `BUSY` bit and see updates during the same transaction.

Note that the passthrough gate only updates on CSb de-assertion and derives its value from the committed `BUSY` bit.
This means that after the `BUSY` bit is set, there must be at least one command before the passthrough gate will open again.
Typically, a Read Status command follows any command that would set the `BUSY` bit to check that the bit has cleared -
this is sufficient to unblock passthrough for the next command.

This module only processes Read Status commands. If the SW wishes to handle Write Status commands,
SW must configure the remaining command information entries with the Write Status opcode and set the *upload* field,
then handle the uploaded command in SW.

If the host sends the Write Status commands, the commands are not processed in this module.
SW must configure the remaining command information entries to upload the Write Status commands to the FIFOs.

### JEDEC ID Control

The JEDEC module returns the JEDEC Manufacturer ID and Device ID of the flash device.

SW may configure the Continuation Code byte in [`JEDEC_CC.cc`](registers.md#jedec_cc_cc),
and the number of Continuation Code repeats in [`JEDEC_CC.num_cc`](registers.md#jedec_cc_num_cc).
For example, the lowRISC JEDEC ID consists of twelve `0x7f` Continuation Codes followed by `0xef`.

SW may configure the [`JEDEC_ID`](registers.md#jedec_id) CSR to set the Manufacturer ID and 2-byte Device ID.

The HW sends the Continuation Codes first, then manufacturer ID, followed by bits `[7:0]` and `[15:8]` of the device ID.

### Serial Flash Discoverable Parameters (SFDP) Control

HW parses the SFDP command then fetches the data from SFDP space in the DPSRAM.
HW provides 256B SFDP space.
HW uses the lower 8 bits of the received 24-bit address to access DPSRAM.
The upper 16 bits are ignored.
SW should prepare proper SFDP contents before the host system issues SFDP commands.

HW fetches 4 bytes at a time from DPSRAM and returns the data on the SPI line, repeating until CSb is de-asserted.

### Read Command Processor

The read command block has multiple sub-blocks to process normal Read, Fast Read, Fast Read Dual/Quad from the internal DPSRAM.
The DPSRAM has a 2kB region for the read command access.
The read command region has two 1kB buffers.
If HW receives the read access to the other half of the space first time, then the HW reports to the SW to refill the current 1kB region with new content.

The double buffering scheme aids the SW in preparing the next chunk of data.
SW copies a portion of data (1kB) from the internal flash memory into the SPI Device's DPSRAM.
With the double buffering scheme, the host system can see the emulated flash as containing more than 2kB of storage,
assuming that the host system reads mostly sequentially.

#### Address Handling

For read commands such as Normal Read, Fast Read Single/Dual/Quad Output commands, the address comes through ID0 only.
The state machine in this block shifts the address one-by-one and decrements the address counter register by 1.

When it reaches the 4B address (`addr[2]`), the module triggers the DPSRAM state machine to fetch data from the DPSRAM.
When the module receives `addr[0]`, at the positive edge of SCK, the module moves to appropriate command state based on the given `CMD_INFO` data.

If the received address falls into mailbox address range and mailbox feature is enabled, the module turns on the mailbox selection bit.
Then all out-going requests to the DPSRAM are forwarded to the mailbox section, not the read buffer section.

#### Dummy Cycle

The SW may configure the number of dummy cycles for each individual read command, from 0 to 8 cycles.

#### Pipelined Reads

![Flash Read Pipeline Diagram](../doc/read_pipeline.svg)

For commands with dummy cycles, the SPI Device IP can be configured to insert a 2-stage pipeline into the return path to enable higher clock rates.
The high-speed read pipeline is of particular interest to Passthrough mode, as it moves the delay from the SPI Device IP to the Host to another cycle, relaxing the timing requirement.
To use the high-speed read pipeline for Passthrough operation, the SPI Device IP should be configured to intercept SFDP reads and advertise 2 more dummy cycles than specified by the downstream SPI flash.
The command information entry (['CMD_INFO'](registers.md#cmd_info)) should have the same number of dummy cycles as the downstream SPI flash.

The high-speed read pipeline can be configured for either full-cycle or half-cycle sampling.
With full-cycle sampling, the first stage samples the read data from the downstream SPI flash a full cycle after it shifts data out (with launching and sampling edges being the same direction).
With half-cycle sampling, a "zeroth" stage samples the read data from the downstream SPI flash half a cycle after it shifts data out (with launching and sampling edges being opposite).
Full-cycle sampling is available to provide the longest period possible for the longer read path of `Host -> SPI Device -> SPI Flash -> SPI Device`.
However, half-cycle sampling is available if hold time requirements cannot be met for full-cycle sampling.

From a compatibility perspective, the high-speed read pipeline is expected to have broad compatibility for Quad Output Read commands, so long as the Host has some flexibility for the number of dummy cycles.
The 2-stage pipeline also ensures that the transaction ends on full byte boundaries for Quad Output Read.
By contrast, Fast Read and Dual Output Read conventionally require 8 dummy cycles, though Dual Output Read can also advertise a different number in the SFDP.

Note that the pipeline does function for intercepted reads in Passthrough mode.
For example, reads addressed to the mailbox will appear with the same number of dummy cycles as reads that were passed-through.

See the ['CMD_INFO'](registers.md#cmd_info) descriptions for the specific programming values.

#### Buffer Management

![Read Buffer Management](../doc/buffer-management.svg)

The SPI Device IP uses the first half of the DPSRAM as a read buffer when the SPI mode is Flash or Passthrough mode.
The IP returns data from the read buffer based on the given address in the received read command.
In the current version, the read buffer size is 2kB.
The IP only uses lower 11 bits of the received read command address (`addr[10:0]`) to issue the read requests to the DPSRAM.

The read buffer feature is intended for an upstream device's initial firmware load, which manifests as a contiguous block read (typically a single SPI flash read command).
SW is responsible for updating the read buffer contents.
The HW notifies the SW to update the buffer contents when needed.

The HW provides a read-only [`LAST_READ_ADDR`](registers.md#last_read_addr) CSR that shows the last read address of the most recent read command.
For instance, if the host system issues a read from address `0xABCDE000` and reads 128 (`0x80`) bytes, `LAST_READ_ADDR` will be `0xABCDE07F` after the transaction.

`LAST_READ_ADDR` does not show a read falling into the mailbox region or Read SFDP's command address space - if a read enters either region,
`LAST_READ_ADDR` does not update until the read exits the region.

The [`READ_THRESHOLD`](registers.md#read_threshold) CSR provides a SW-configurable watermark for reads from the read buffer.
The read watermark address width is 1 bit smaller than the read buffer address.

This is designed so that SW implements a double-buffering scheme - when the host system accesses one half of the read buffer (1kB),
the SW should prepare the other 1kB by copying data from the internal non-volatile memory.
If the received read address crosses the SW configured watermark address, the HW informs the SW.
SW should configure the watermark CSR low enough so that the SW has enough time to copy over the data.

If a new read command crosses the current buffer boundary, the SW flips the internal buffer index bit and clears the cross event for the HW to detect the address cross event again.

### 4B Address Management (EN4B/EX4B)

SW may configure the HW to handle the EN4B ([`CMD_INFO_EN4B`](registers.md#cmd_info_en4b)) and EX4B ([`CMD_INFO_EX4B`](registers.md#cmd_info_ex4b)) commands and change the address size for read commands between 3 bytes and 4 bytes.

When the HW receives one of the commands, the HW changes the broadcast signal *cfg_addr_4b_en*.
The HW also updates [`ADDR_MODE.addr_4b_en`](registers.md#addr_mode) after passing through CDC.
It takes at most three SYS_CLK cycles to update the value in the `ADDR_MODE` register after the completion of the SPI transaction (CSb de-assertion).

The HW changes the broadcasting signal and the CSR even if the SPI host system sends more than the opcode byte.
After the logic matches the received command byte with EN4B or EX4B, the rest of the transfer is ignored.

The broadcasted *cfg_addr_4b_en* signal affects the read commands for which `addr_mode` is *AddrCfg* in their command information entries.

SW may also configure the initial address mode by writing to [`ADDR_MODE.addr_4b_en`](registers.md#addr_mode).
SW must not write to this CSR unless it knows the upstream host is inactive and expects initial values for the next transaction.
After initialization (from the upstream SPI host's perspective), it is a protocol violation for the address mode to change outside the host's explicit commands.
A SW request will set the [`ADDR_MODE.pending`](registers.md#addr_mode) bit, which will remain set until HW consumes the update.
SW will see the intended mode in [`ADDR_MODE.addr_4b_en`](registers.md#addr_mode) until HW completes the request.
However, SW may overwrite the requested value, so long as the SPI host is held inactive.
The request does not complete until the SPI host completes the opcode phase of the transaction, and it will take effect for that same transaction's address phase (if any).

### Command Upload

If the received command meets following conditions, the HW stores the command into the command/address FIFOs and the payload buffer:

- The command does not match to the first 11 command information entries nor EN4B, EX4B, WREN, or WRDI.
- The command matches any of the rest command information entries.
- The matched entry has the *upload* field set.

The upload module checks the command information entry to determine whether the address/payload fields are to be uploaded or not.
The `addr_mode` is used to determine the address size in the command.

If the *busy* field in the command information entry is set, the upload module also sets `BUSY` bit in the [`FLASH_STATUS`](registers.md#flash_status) register.
SW may clear the *BUSY* bit after processing the command.

In addition, the HW stores some metadata alongside the opcode in the [`CMD_FIFO`](registers.md#upload_cmdfifo).
Included are the state of the address mode, the `BUSY` status bit, and the `WEL` status bit at the time the command was uploaded.
With these, SW can determine what size the address should be and whether the uploaded command should be rejected.

The upload module provides the [`UPLOAD_STATUS`](registers.md#upload_status) and [`UPLOAD_STATUS2`](registers.md#upload_status2) CSRs for SW to parse the command, address, and payload.
If a received command has payload, SW may read the payload from the Payload buffer starting from offset [`UPLOAD_STATUS2.payload_start_idx`](registers.md#upload_status2).
Under normal operation, `payload_start_idx` shows 0.
If the host systems sends more than the maximum allowed payload size (currently 256B), `payload_start_idx` may be non-zero.
In that case it is expected that [`UPLOAD_STATUS2.payload_depth`](registers.md#upload_status2) is the maximum payload size.
SW should read from `payload_start_idx` to the end of the payload buffer, then do a second read from the beginning of the buffer to read the remaining bytes.
If more bytes are sent than the maximum allowed payload size, the IP reports the payload_overflow interrupt.

### Passthrough

The passthrough module is an intermediary between a host system and a downstream SPI flash device.
The passthrough module snoops in on SPI transactions, and can perform the following functions:

- [Filtering commands](#command-filtering) that are not permitted to reach the downstream SPI flash.
- [Intercepting commands](#interceptedinternally-processed-commands) so that they are handled by HW.
- Transparently manipulating sent [address](#address-manipulation) and [payload](#write-payload-manipulation) data bytes on-the-fly.

#### Command Filtering

Filtering of incoming commands is a key role of the passthrough module.

![Command Filtering logic in Passthrough mode](../doc/passthrough-filter.svg)

```wavejson
{ signal: [
  { name: 'CSb_in',  wave: '10.........|....1.'},
  { name: 'SCK_in',  wave: '0.p........|....l.'},
  { name: 'IO[0]_i',  wave: 'z.=..=.=.=.=.=.=.=.=|=.=.=.=.z......',
   data:["C[7]", "C[6]", "C[5]", "C[4]", "C[3]", "C[2]", "C[1]", "C[0]"],
    period:0.5, },
  { name: 'filter',  wave: '0................10.................',
    period:0.5},
  { name: 'filtered', wave: '0.................1.................',
    period:0.5},
  { name: 'SCK_out', wave: '0.p......0........'},
  { name: 'CSb_out', wave: '10................1.................', period:0.5}
  ],
  head:{
    text: 'Command Filtering',
    tick: ['-2 -1 0 n-1 n+' ]
  }
}
```

The passthrough logic filters a command by de-asserting CSb if the opcode's corresponding bit is set in the 256-bit [`CMD_FILTER`](registers.md#cmd_filter_0) CSR.
For example, if bit 5 of [`CMD_FILTER_0`](registers.md#cmd_filter_0) is set, the passthrough logic de-asserts CSb when it receives opcode `0x05` at the start of a command.

SW is not notified when a received command is filtered or not.
If the SW wants to check, it should set the *upload* field in the command's information entry, so that the filtered command is uploaded for SW to inspect and process.

#### Address Manipulation

The passthrough logic provides a way to modify the address bytes sent to the downstream SPI flash device at the start of a command on-the-fly.
Address swapping is not applied in Flash mode.

Address swapping is applied to commands with the *addr_swap_en* field set.
SW should ensure that the *addr_mode* field is set correctly for the command - even if address swapping is not used - for correct framing.

Address swapping only applies to the address bytes sent to the downstream flash - if the command has the *upload* field set, the address uploaded to the address FIFO consists of the unmodified bytes.
SW can choose to apply the address swapping when processing the command.

SW may configure the [`ADDR_SWAP_MASK`](registers.md#addr_swap_mask) and [`ADDR_SWAP_DATA`](registers.md#addr_swap_data) CSRs to set or unset any bits of the written address.
For any bit set in `ADDR_SWAP_MASK`, the passthrough logic instead uses the value of the corresponding bit in `ADDR_SWAP_DATA` for that address bit.

Addresses sent over SPI are sent most-significant bit first, meaning bits `[7:0]` control the least-significant (last sent) address byte, then bits `[15:8]`, and so on.
If the size of a command's address field is not 4 bytes (`CMD_INFO.addr_mode != Addr4B`, or `CMD_INFO.addr_mode == AddrCfg` and `CFG.addr_4b_en` is unset), bits `[31:24]` are unused.

For example, if `ADDR_SWAP_MASK` is set to `0x000f0000` and `PAYLOAD_SWAP_DATA` is set to `0x000f0000`, bits 0 and 2 of the third address byte are set to 1, bits 1 and 3 of the third address byte are set to 0,
and the rest of the address is unchanged.

#### Write Payload Manipulation

The passthrough logic also provides a way to modify the first 4 bytes of the payload sent to the downstream SPI flash device on-the-fly.
The primary use of this feature is to protect writes to the downstream SPI flash's status register.
Payload swapping is not applied in Flash mode.

Payload swapping is applied to commands with the *payload_swap_en* field set in their command information entries.
SW must also configure *payload_dir* to be `PayloadIn` and *payload_en* to be `0b0001` in order for payload swapping to work correctly.
SW should also ensure the command's address size and dummy cycle count are set correctly for correct framing.

Payload swapping only applies to the payload bytes sent to the downstream flash - if the command has the *upload* field set, the payload uploaded to the payload buffer consists of the unmodified bytes.
SW can choose to apply the payload swapping when processing the command.

SW may configure the [`PAYLOAD_SWAP_MASK`](registers.md#payload_swap_mask) and [`PAYLOAD_SWAP_DATA`](registers.md#payload_swap_data) CSRs to set or unset any bits of the first 4 bytes of the written payload.
For any bit set in `PAYLOAD_SWAP_MASK`, the passthrough logic instead uses the value of the corresponding bit in `PAYLOAD_SWAP_DATA` for that payload bit.

The bits are processed from least to most-significant, i.e bits `[7:0]` control the first byte of payload, followed by bits `[15:8]`, `[23:16]`, and `[31:24]`.

For example, if `PAYLOAD_SWAP_MASK` is set to `0x0000000f` and `PAYLOAD_SWAP_DATA` is set to `0x00000005`, bits 0 and 2 of the first payload byte are set to 1, bits 1 and 3 of the first payload byte are set to 0,
and the rest of the payload is unchanged.

#### Output Enable Control

The passthrough module controls the output enable signals on both the host and downstream sides.
Controlling the output enable ports is critical to not overdrive the PAD directions.

SW should configure each command information entry with the appropriate pad enable and pad direction for the command.

If no command information entry is matched on the received opcode, it is assumed that the command is a Single IO `PayloadIn` command.

SW is strongly recommended to set the filter bits for any opcodes that do not appear in command information entries to not deliver unmatched commands to the downstream flash device.

#### Intercepted/Internally Processed Commands

As described in [SPI Device Modes](../README.md#spi-device-modes-and-active-submodules), SPI Device may intercept commands and return data from HW even if Passthrough mode is enabled.

The HW can process the Read Status, Read JEDEC ID, and Read SFDP commands, as well as Read commands accessing the mailbox region, EN4B/EX4B, and WREN/WRDI.

SW may selectively enable/disable which commands are intercepted by HW using the [`INTERCEPT_EN`](registers.md#intercept_en) CSR.
For example, if only `INTERCEPT_EN.status` is set, only the Read Status commands are intercepted and processed by HW.

In the Flash and Passthrough modes, the EN4B, EX4B, WREN and WRDI commands are always processed internally if the *valid* bit is set in their command information entries.

It is recommended to also filter the intercepted commands (except for Read commands).

## TPM over SPI

![TPM over SPI block diagram](../doc/tpm-blockdiagram.svg)

The TPM over SPI submodule processes the low level data only, and it is not compliant with the SPI TPM command timing specifications.
The TPM submodule parses the incoming SPI MOSI line and stacks the stream up to the SW accessible registers, such as TPM_CMD_ADDR and the write FIFO buffer.
The SW must decode the command and the address.
Then the SW reads the data from the write FIFO or pushes data into the read FIFO depending on the command.

The TPM submodule returns appropriate data for read commands depending on the current read FIFO status, the received address, and the Locality.
The module sends bytes from the return-by-HW registers to the parallel-to-serial logic right after the address phase when the received address falls into the HW managed registers.

The TPM specification mandates the TPM module to return the data right after the address phase or send the WAIT at the last bit of the address phase.
The address of the return-by-HW registers has a 4B boundary.
The TPM submodule has enough time to determine if the incoming address falls into the return-by-HW registers or not.
As the logic decides if the HW returns data or waits for the SW response at the address[2] bit phase, the logic always sends `WAIT(0x00)` at the last byte of the incoming address phase.
The module sends `START(0x01)` at the next byte followed by the actual return-by-HW value if the received address falls into the list of the return-by-HW registers.

The module, by default, returns `WAIT` when the address does not fall into the return-by-HW register address.
In the wait state, the TPM submodule watches the read FIFO status.
The module stays in the wait state until the read FIFO has the data >= requested transfer size.
The module sends `START` at the next byte when the read FIFO has enough data.
Then the module pops data from the read FIFO and sends the data over SPI.

The TPM submodule accepts the payload for the TPM write command without the `WAIT` state if the write and command FIFOs are empty.
In other case, the TPM submodule sends `WAIT` until the write and command FIFOs become available (empty).

### Configuring Return-by-HW registers

The return-by-HW register values come from the SW read-writable CSRs.
The module latches the CSRs from the SYS_CLK domain into the SPI SCK domain when CSb is asserted.
The SW is allowed to modify the return-by-HW registers when CSb is de-asserted.

The [TCG PC Client Platform TPM Profile][TPM PCCP] spec describes in the section 6 that the TPM device returns registers values based on the received locality (address[15:12]) and the `TPM_ACCESS_x.activeLocality`.
The HW uses `TPM_ACCESS_x.activeLocaltiy` and the address bit 15:12 to determine what value the logic should return.
If `invalid_locality` configuration is set, the logic returns `INVALID` value to the host system, when the host system sends a read request to the Locality greater than 4.
If the request is in the supported locality (0-4), the logic checks `TPM_ACCESS_x.activeLocality` then returns data based on the table 39 in the spec for Return-by-HW registers.
Other registers in the table should be processed by SW.

Note that firmware is in the loop to process write commands to these registers.
Consequently, the TPM over SPI submodule cannot meet timing requirements for updated data to be available within one wait state.
Once firmware writes the CSRs, the submodule can return the data as specified, however.

## Detecting Reliability Errors

This version of the SPI Device IP implements the parity to detect bit flip errors on the internal SRAM.
The HW checks the parity error when the SW reads data from the SRAM.
The error is reported to the SW via TL D channel error signal.
SW is recommended to discard the current context if any transaction is ongoing then to reset the IP.

# Design Details

## Clock and Phase

The SPI Device IP only internally supports mode 0, where data is shifted out on the falling edge and sampled on the rising edge, and SPI clock returns to low at the end of the transaction.
For further details, please refer to this diagram from Wikipedia:
[File:SPI_timing_diagram2.svg](https://en.wikipedia.org/wiki/File:SPI_timing_diagram2.svg)
