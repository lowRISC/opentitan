# Programmer's Guide

This section details how software can interface with the mailbox.

## Module Initialization

Before initiating memory transfers using the mailbox, it needs to configured for the accessible memory.
This involves a specific sequence of register writes:

1.  **Define the Memory Range for Inbound and Outbound Ranges:** First, software must write the base address for the inbound range to the [`INBOUND_BASE_ADDRESS`](registers.md#inbound_base_address) register and the upper limit of the inbound range to the [`INBOUND_LIMIT_ADDRESS`](registers.md#inbound_limit_address) register. The same operation needs to be performed for the outbound range to the registers [`OUTBOUND_BASE_ADDRESS`](registers.md#outbound_base_address) and [`OUTBOUND_LIMIT_ADDRESS`](registers.md#outboundlimit_address).
2.  **Validate the Range:** Next, to indicate that the configured range contains valid data, software must write to the [`ADDRESS_RANGE_VALID`](registers.md#address_range_valid) register.
3.  **Optional Range Locking:** Optionally, software can write to the [`ADDRESS_RANGE_REGWEN`](registers.md#address_range_regwen) register to lock the configured memory range. Once locked, the range configuration cannot be modified until the next reset of the mailbox.

## Inbound Transfer

## Outbound Transfer

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../sw/device/lib/dif/dif_dma.h)
