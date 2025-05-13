# Programmer's Guide

This section details how software can interface with the Direct Memory Access (DMA) controller.

## Module Initialization

Before initiating memory transfers using the DMA for OpenTitan internal memory, software must define the accessible memory range for the DMA.
This involves a specific sequence of register writes:

1.  **Define the Memory Range:** First, software must write the base address to the [`ENABLED_MEMORY_RANGE_BASE`](registers.md#enabled_memory_range_base) register and the upper limit of the accessible range to the [`ENABLED_MEMORY_RANGE_LIMIT`](registers.md#enabled_memory_range_limit) register.
2.  **Validate the Range:** Next, to indicate that the configured range contains valid data, software must write to the [`RANGE_VALID`](registers.md#range_valid) register.
3.  **Optional Range Locking:** Optionally, software can write to the [`RANGE_REGWEN`](registers.md#range_regwEN) register to lock the configured memory range. Once locked, the range configuration cannot be modified until the next reset of the DMA.

## Initiate a Memory transfer

To start a memory transfer, software needs to configure several registers that define the source and destination of the data, as well as the transfer size and access pattern:

1.  **Source and Destination Configuration:** Configure the source and destination address modes using the [`SRC_CONFIG`](registers.md#src_config) and [`DST_CONFIG`](registers.md#dst_config) registers. The DMA supports 3 addressing modes, which can be configured independently for the source and destination via the aforementioned registers:
  * Continuously accessing the same address (`increment = 0`, `wrap = 0`)
  * Linear addressing (`increment = 1`, `wrap = 0`), with an address increment after each transfer
  * Wrap Mode:  (`increment = 1`, `wrap = 1`), with an address increment after each transfer and a wrap to the start address after finishing the transfer of one chunk.
2.  **Source and Destination Addresses:** Specify the starting memory addresses for the source and destination using the lower and upper 32-bit parts of the addresses in the [`SRC_ADDR_LO`](registers.md#src_addr_lo), [`SRC_ADDR_HI`](registers.md#src_addr_hi), [`DST_ADDR_LO`](registers.md#dst_addr_lo), and [`DST_ADDR_HI`](registers.md#dst_addr_hi) registers.
3.  **Total Transfer Size:** Define the total number of bytes to be transferred using the [`TOTAL_DATA_SIZE`](registers.md#total_data_size) register.
4.  **Access Stride:** Configure the access stride (the number of bytes accessed in each burst) using the [`TRANSFER_WIDTH`](registers.md#transfer_width) register.
5.  **Chunk Size (Memory-to-Memory):** The DMA performs memory access in chunks. For a standard memory-to-memory transfer, the [`CHUNK_DATA_SIZE`](registers.md#chunk_data_size) register is typically set to the same value as the [`TOTAL_DATA_SIZE`](registers.md#total_data_size) register. The concept of chunked transfers is further explained in the [Chunked Data Transfers](#Chunked_Data_Transfers) section.
6.  **Start the Transfer:** Initiate the transfer by writing to the `go` bit along with the `initial_transfer` bit in the [`CONTROL`](registers.md#control) register.
7.  **Monitor Transfer Completion:** After starting the transfer, software can monitor its progress by either polling the [`STATUS`](registers.md#status) register or by waiting for a specific interrupt to be raised.

### Interrupt Handling

The DMA can signal various events to the software through interrupts.
The following three types of interrupts are supported:

1.  **Transfer Completion:** An interrupt is raised when the entire data transfer (as defined by `TOTAL_DATA_SIZE`) is complete.
2.  **Chunk Completion:** An interrupt is raised after the transfer of a single chunk of data (as defined by `CHUNK_DATA_SIZE`) is finished. This interrupt is only available when not using the [Hardware Handshaking Mode](#Hardware_Handshaking_Mode).
3.  **Error Condition:** An interrupt is raised if an error occurs during the transfer process.

The current status of the DMA, including pending interrupts, can be read from the [`STATUS`](registers.md#status) register.
Since interrupts are implemented as status bits, they are cleared by writing a '1' to the corresponding bit in the `STATUS` register.

### Aborting a Transfer

Software can terminate an ongoing DMA transfer at any point by writing to the `abort` bit in the [`CONTROL`](registers.md#control) register.
Aborting an operation happens immediately after writing the `abort` bit and does not require any further scheduling or waiting.
The [`STATUS`](registers.md#status) indicates via the `aborted` bit that the DMA operation was aborted and the DMA stopped its operation.

## Chunked Data Transfers

The DMA performs memory transfers in discrete units called chunks.
Each chunk consists of a contiguous block of data with a size defined by the [`CHUNK_DATA_SIZE`](#chunk_data_size) register.
After transferring a chunk, the DMA can optionally generate an interrupt.

While chunked transfers are primarily utilized in conjunction with the [Hardware Handshaking Mode](#Hardware_Handshaking_Mode) for interacting with IO peripherals, they can also be employed in memory-to-memory transfers.
A potential use case for chunked memory-to-memory transfers is memory initialization, where a small chunk of data (e.g., a block of zeros) can be repeatedly transferred to a larger memory region.
For chunked data transfers the first transfer needs to assert the `initial_transfer` bit in the [`CONTROL`](registers.md#control) register.
Initiating the transfer of subsequent chunks must not assert the `initial_transfer` bit.

## Hardware Handshaking Mode

The DMA supports a hardware handshaking mode that enables seamless data transfers between IO peripherals and memory.
This mode leverages the chunked data transfer mechanism and interrupts from the IO peripheral.

In this mode, the IO peripheral fills its internal transfer FIFO and then signals the DMA by raising an interrupt.
Upon receiving this interrupt, the DMA reads the data from the peripheral's FIFO and writes it to the destination memory.
This process continues in a loop: the DMA transfers a chunk of data, waits for the IO peripheral to fill its FIFO and issue another interrupt, and then transfers the next chunk.
This loop repeats until the total number of bytes specified by [`TOTAL_DATA_SIZE`](registers.md#total_data_size) has been transferred.

To enable hardware handshaking, software must set the `hardware_handshake_enable` bit in the [`CONTROL`](#control) register and configure the appropriate addressing mode to access the IO peripheral.

The DMA's chunked transfer mechanism in hardware handshaking mode supports two address update modes for the peripheral:

  * **Fixed address:** The DMA accesses the same address for each chunk.
  * **Wrap-around:** After transferring a chunk, the DMA's peripheral address wraps around to the starting address configured for the transfer.

These modes are configured via the [`SRC_CONFIG`](registers.md#src_config) and [`DST_CONFIG`](registers.md#dst_config) registers as described above.
For interrupt handling in hardware handshaking mode, software needs to enable the corresponding interrupt using the [`HANDSHAKE_INTR_ENABLE`](#handshake_intr_enable) register.

The DMA also provides a mechanism to acknowledge the interrupt received from the IO peripheral by performing a configurable write operation.
If interrupt acknowledgement is required, software must enable it in the [`CLEAR_INTR_SRC`](#clear_intr_src) register.
The address space for this write operation is configured using the [`CLEAR_INTR_BUS`](#clear_intr_bus) register.
The specific address and data value to be written for acknowledgement are defined by the [`INTR_SRC_ADDR_0-10`](#intr_src_addr) and [`INTR_SRC_WR_VAL_0-10`](#intr_src_wr_val) registers, respectively.

## Inline Hashing

The DMA incorporates an inline hashing capability for SHA-2 algorithms (SHA-256, SHA-384, and SHA-512).
This allows the DMA to compute the hash digest of the transferred data concurrently with the memory transfer.

To enable inline hashing, software must set the desired SHA-2 algorithm as the opcode in the `opcode` field of the [`CONTROL`](registers.md#control) register.
This will instruct the DMA to perform the data copy operation along with the hash computation.

When initiating a transfer with inline hashing, the `initial_transfer` bit in the [`CONTROL`](registers.md#control) register must be asserted.
This signals the DMA to initialize its internal hash state.
When using chunked transfers with inline hashing, subsequent chunk transfers should have the `initial_transfer` bit cleared to prevent re-initialization of the hash state between chunks.

The endianness of the resulting hash digest can be configured using the `digest_swap` bit in the [`CONTROL`](registers.md#control) register.

Once the transfer is complete, the computed hash digest value can be read from the [`SHA2_DIGEST_0-15`](registers.md#sha2_digest) registers.

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../sw/device/lib/dif/dif_dma.h)
