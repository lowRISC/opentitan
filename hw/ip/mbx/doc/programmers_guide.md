# Programmer's Guide

In a typical use case there are two software agents involved in the mailbox communication:

- RoT firmware configures the mailbox IP block and awaits requests from the SoC side.
- SoC-side software makes requests of the RoT firmware and awaits its responses.

A note on terminology: The request is received from the SoC side into an _Inbox_ on the RoT and the response is deposited into the _Outbox_ by the RoT, i.e. the mailbox directions are named from the perspective of the RoT.

Each of the request and the response is composed of 'DWORD's which are 32 bits in size, so all messages sent and received by the mailbox must be a multiple of 4 bytes in length.
An additional constraint of at most 1024 DWORDs (4 KiB) applies to the size of any response from the RoT (Outbox message).

## Initialization

Since the mailbox logic acts as a host on the TileLink fabric, before requests may be received from the SoC side the firmware of the RoT must configure the address ranges that may be accessed by the Inbox (SoC->RoT) and Outbox (RoT->SoC) logic.

To configure the mailbox for use, four registers - two for each side (Inbox and Outbox) - must be written:

1. Program [`inbound_base_address`](registers.md#inbound_base_address) with the _inclusive_ base address of the Inbox memory region.
2. Program [`inbound_limit_address`](registers.md#inbound_limit_address) with the _inclusive_ end address of the Inbox, i.e. this is the highest valid address to which a DWORD may be written by the Inbox logic.
3. Program [`outbound_base_address`](registers.md#outbound_base_address) with the _inclusive_ base address of the Outbox memory region.
4. Program [`outbound_limit_address`](registers.md#outbound_limit_address) with the _inclusive_ end address of the Outbox, i.e. this is the highest valid address from which a DWORD may be read by the Outbox logic.

Having supplied the address ranges, the RoT firmware shall declare the ranges valid by writing a value of 1 to the [`address_range_valid`](registers.md#address_range_valid) register, and may optionally lock the address range by writing MuBi4False to register [`address_range_regwen`](registers.md#address_range_regwen).
Clearing the 'write enable' register in this manner prevents any further changes to the address range configuration until the mailbox IP block is reset, protecting against accidental or malicious changes.

## Request message from SoC to RoT

A software/hardware agent on the SoC side is required to check that the BUSY bit is clear before starting to send a request to the RoT.
The BUSY bit indicates that the mailbox is already part-way through a request-response operation, so another request cannot be accepted.

The request itself is sent by writing each 32-bit DWORD of the message to the WDATA register on the SoC-side interface.
The write data will be accepted into the Inbox handler when it can be presented onto the RoT-side fabric for writing to the Inbox memory.
A back-pressure/flow control mechanism prevents data loss at this point in the event that the SoC side faster.

The request is written into the mailbox memory of the RoT side starting at the address specified in [`inbound_base_address`](registers.md#inbound_base_address) and incrementing for each DWORD transferred.
When the entire request has been written to the Inbox via the WDATA register, the SoC-side agent must set the GO bit of the [`soc_control`](registers.md#soc_control) register to present it to the RoT firmware.
This causes the Inbox handler to assert the `mbx_ready` to the RoT firmware so that it may collect and process the request message.

The RoT firmware shall consult the [`inbound_write_ptr`](registers.md#inbound_write_ptr) register to ascertain the length of the transferred request message.
The address in this register is advanced whenever a DWORD of the request message is written to the Inbox, so upon receipt of the complete request it holds the 4-byte aligned address _beyond_ the final DWORD of the request. The register [`inbound_write_ptr`](registers.md#inbound_write_ptr) is a read only register to the RoT firmware and its value is automatically reset to that of [`inbound_base_address`](registers.md#inbound_base_address) at the start of each request message.

## Collection of RoT response message by SoC

When the RoT firmware has performed the requested operation it is required to produce a response for the SoC side to collect.
The firmware shall write the response message into the Outbox memory starting at the address specified in [`outbound_base_address`](registers.md#outbound_base_address), and shall then specify the number of DWORDs of message data by writing a non-zero value to the [`outbound_object_size`](registers.md#outbound_object_size) register.
This register permits the sending of responses that are up to 1024 DWORDs in length for a maximum size of 4 KiB.

## Abort mechanism

If the SoC side needs to cancel an in-progress service request, it may use the Abort mechanism of the DOE mailbox control register.
Setting the `abort` bit of the [`soc_control`](registers.md#soc_control) register will raise the `mbx_abort` interrupt to the RoT firmware, instructing it that any in-progress operation shall be aborted.

The RoT firmware should then clear the `abort` indicator via its [`control`](registers.md#control) register on the RoT side and initiate any recovery procedures.

## Firmware-initiated reset

In addition to the SoC-side Abort mechanism specified for DOE mailboxes, the RoT firmware has the ability to perform a complete reset of the mailbox logic to recover from any error condition or synchronization issue that may have been detected.

This is achieved by writing 1 to the `abort` bit of the [`control`](registers.md#control) register. In addition to clearing any pending Abort condition from the SoC side this action has the effect of resetting all of the internal mailbox logic as a fallback recovery mechanism.
