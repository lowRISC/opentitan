# DMA Controller (dma)

The Direct Memory Access (DMA) controller is a peripheral within the OpenTitan system-on-chip (SoC).
It is designed to provide processor-independent data transfer capabilities between different locations in the system memory map and/or peripherals.
Its primary purpose is to free the main processor (the Ibex core) from the overhead of large or slow data copy operations, thereby freeing up the CPU for other computational tasks.

The DMA controller is a single-channel device that processes one data transaction at a time. It acts as a master on the system's **TileLink Uncached Lightweight (TL-UL)** bus, allowing it to autonomously read from and write to any memory-mapped peripheral or memory region.
The DMA enforces a hardware-based isolation mechanism to restrict the access to the OpenTitan internal memory.

## Features

The DMA controller's RTL implementation includes the following features:

* Support for 3 bus interfaces:
    1.  Private OpenTitan (OT) Address Space Interface (TL-UL)
    2.  Control Network (CTN) Interface (TL-UL)
    3.  64-bit System (sys) Interface (custom protocol)

* **Flexible Data Transfer & Addressing Modes**:
    * **Transfer Modes**:
        * Memory-to-Memory
        * Memory-to-Peripheral
        * Peripheral-to-Memory
    * **Addressing Modes**:
        * **Incrementing Address**: The source/destination address automatically increments after each data word transfer. This is the standard mode for accessing sequential data in memory.
        * **Fixed Address**: The source/destination address remains constant throughout the transaction. This is essential for reading from or writing to a peripheral's fixed-address data register (e.g., a FIFO).
        * **Wrapping / Circular Buffer Address**: When used with chunked transfers, the address automatically wraps around to the starting address of the chunk after each chunk is transferred.

* **Configurable Transfer Granularity**: Supports data transfers in 1-byte, 2-byte, or 4-byte granularities to accommodate various peripheral and memory types.

* **Inline Hashing**: The DMA can be configured to feed all transferred data directly through an internal **SHA2** accelerator. This allows for a cryptographic hash of the data to be calculated "on-the-fly" as it is being moved, supporting **SHA2-256, SHA2-384, and SHA2-512** modes.

* **Hardware Handshake Mode**: Allows the DMA to be triggered by a hardware signal from a peripheral, enabling efficient servicing of peripheral FIFOs without CPU intervention.

* **Interrupt Generation**: Capable of generating interrupts to the processor upon:
    * Completion of a full transaction (`dma_done`).
    * Completion of a data chunk (`dma_chunk_done`).
    * Detection of an error (`dma_error`).

## Use Cases

This section describes possible use cases of the DMA controller.

### Bulk Data Transfer

The services of an integrated OpenTitan require the movement of bulk data from SoC / system memory to the OpenTitan (OT) private memory and vice-versa.
The DMA controller provides OpenTitan with the ability to move data blobs securely in and out of the OpenTitan memory while offloading the Ibex core to focus on security critical tasks.
The DMA provides a hardware isolation layer between OpenTitan and the rest of the SoC.
It provides the hardware enforcement of security properties through well defined isolation & access control techniques, hardware based checking and other protection mechanisms.
Note that depending upon the use case, it is expected that the SoC provides proper security mechanisms for code / data protections such as access control mechanisms, encrypted and integrity protected memory regions, etc.

An example scenario where a secure DMA could potentially be used is firmware controlled secure boot operation:

* Configure the DMA to move a signed firmware image (or a manifest) into the OT DMA enabled memory.
* OT performs a digital cryptographic hash operation and a signature-based verification of the firmware image / manifest.
* If the digital signature verification passes, the DMA is configured to move the firmware to a protected location within the SoC secured by     access control to prevent further modification.
* Enable other firmware-based processing elements to boot from this secure location.

Additional efficiency benefits are derived by supporting inline operations within the DMA controller such as on-the-fly hashing.

### IO Data Transfer

The DMA controller features a hardware-handshake mode that enables automatic data transfers with a peripheral's I/O FIFO.
This mode offloads the main processor by allowing the DMA to read or write multiple data frames without software intervention, which is ideal for long-running I/O operations.

The hardware-handshake mode is compatible with the following OpenTitan peripherals:
* I2C
* UART
* SPI Device
* SPI Host

The DMA supports two trigger mechanisms. The peripherals listed can use a dedicated hardware signal to automatically manage the transfer handshake.
Alternatively, for peripherals without this feature, the DMA can use standard interrupt-based triggers, which require it to clear the interrupt source within the RISC-V Platform-Level Interrupt Controller (PLIC).
