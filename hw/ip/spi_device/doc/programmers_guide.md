# Programmer's Guide

## Initialization

## Dual-port SRAM Layout

The figure below shows the SRAM layout.
The SRAM begins at `0x1000`, which in the figure is `0x000`.

![SPI Device Dual-port SRAM Layout](../doc/spid_sram_layout.svg)

In addition to the various buffers for Flash and Passthrough modes, the TPM Read and Write FIFOs are also assigned to the SRAM.
The TPM Read FIFO presents a FIFO interface to software, which writes the [`TPM_READ_FIFO` CSR](registers.md#tpm_read_fifo) for each word instead of the underlying TPM Read Buffer SRAM region directly.
The TPM Write FIFO, however, presents only the RAM interface to software, with data for each command always starting at the lowest address of the TPM Write Buffer region.

The SRAM is divided into two large blocks.
The first block is for the egress flows, where software writes data to the SRAM, and the SPI host reads it.
That first block includes the flash read buffer, the mailbox, the SFDP, and the TPM Read FIFO.
The second block is for the ingress flows, where the SPI host writes to the SRAM, and software reads from it.
That second block includes the flash command upload buffers and the TPM Write FIFO.

This separation of flows allows the memory to be implemented by two SRAM instances that each have one read-only and one write-only port (the "1r1w" SRAM macro).
In addition, regardless of whether the memory is implemented using a single instance with two read-write ports or the two 1r1w instances, the access controls are the same.
Software can only write to the egress memory, and it can only read from the ingress memory.

## TPM over SPI

### Initialization

The SW should enable the TPM submodule by writing 1 to the TPM_CFG.en CSR field.
Other SPI_DEVICE features (Flash, Passthrough) CSRs do not affect the TPM feature.

Update TPM_ACCESS_0, TPM_ACCESS_1 CSRs.
The TPM submodule uses TPM_ACCESS_x.activeLocality to determine if the TPM_STS is returned to the host system.
The SW may configure TPM_CFG.hw_reg_dis and/or TPM_CFG.invalid_locality to fully control the TPM transactions.

### TPM mode: FIFO and CRB

The TPM protocol supports two protocol interfaces: FIFO and CRB (Command Response Buffer).
In terms of hardware design, these two interfaces differ in how return-by-HW registers are handled.

In FIFO mode, when [`TPM_CFG.tpm_mode`](registers.md#tpm_cfg) is set to 0, HW registers reads must be returned after a maximum of 1 wait state.
In CRB mode, when [`TPM_CFG.tpm_mode`](registers.md#tpm_cfg) is set to 1, there are no such restrictions.
The logic always uploads both the command and address to the SW and waits for the return data in CRB mode.

### Return-by-HW register update

The SW manages the return-by-HW registers.
The contents are placed inside the SPI_DEVICE CSRs.
The SW must maintain the other TPM registers outside of the SPI_DEVICE HWIP and use write/read FIFOs to receive the content from/ send the register value to the host system.

When the SW updates the return-by-HW registers, the SW is recommended to read back the register to confirm the value is written.
Due to the CDC issue, the SW is only permitted to update the registers when the TPM CS# is de-asserted.

### TPM Read

1. The host system sends the TPM read command with the address.
2. The SW reads a word from TPM_CMD_ADDR CSR (optional cmdaddr_notempty interrupt).
  1. If the address falls into the return-by-HW registers and TPM_CFG.hw_reg_dis is not set, the HW does not push the command and address bytes into the TPM_CMD_ADDR CSR.
3. The SW prepares the register value and writes the value into the read FIFO.
4. The TPM submodule sends `WAIT` until the read FIFO is available.
   When available, the TPM submodule sends `START` followed by the register value.
5. Optionally, SW may choose to monitor the `tpm_rdfifo_cmd_end` interrupt to be notified when commands targeting read FIFO commands end.
  1. `TPM_STATUS.rdfifo_aborted` will show whether the triggering command failed.

### TPM Write

1. The host system sends the TPM write command with the address.
2. The TPM submodule checks the write FIFO and cmdaddr FIFO statuses.
3. If the write FIFO is busy or the cmdaddr FIFO is not empty, the TPM submodule sends `WAIT` to the host system.
4. When both FIFOs are empty and/or not busy, the TPM sends `START` to the host system, receives the payload, and stores the data into the write FIFO.
5. On the last bit of the data, the TPM submodule pushes the command and the address to the TPM_CMD_ADDR CSR.
6. The SW reads TPM_CMD_ADDR and then reads the write FIFO data from the RAM.
7. The SW writes TPM_STATUS to release the write FIFO buffer, marking it not busy.

### TPM_CMDADDR_NOTEMPTY Interrupt

`TPM_CMDADDR_NOTEMPTY` interrupt remains high even SW clears the interrupt unless the cause is disappeared.
SW should mask the interrupt if SW wants to process the event in a deferred way.

```c
void spi_tpm_isr() {
  uint32_t irq_deferred = 0;
  uint32_t irq_status = spi_tpm_get_irq_status();
  if (irq_status & kSpiTpmFifoIrq) {
    irq_deferred |= kSpiTpmFifoIrq;
    schedule_deferred_work(spi_tpm_deferred_work);
  }
  // ...
  spi_tpm_mask_irq(irq_deferred);
}

void spi_tpm_deferred_work() {
  uint32_t irq_handled = 0;
  uint32_t irq_status = spi_tpm_get_irq_status();
  if (irq_status & kSpiTpmFifoIrq) {
    spi_tpm_handle_fifo_irq();
    irq_handled |= kSpiTpmFifoIrq;
  }
  // ...
  // Now that we think the FIFO has been emptied, clear the latched status.
  spi_tpm_clear_irq_status(irq_handled);
  spi_tpm_unmask_irq(irq_handled);
  // If the FIFO received more data after handling, the interrupt would assert
  // again here.
}
```


### TPM Interrupt

The TPM submodule does not process the TPM over SPI interrupt.
The SW must check TPM_INT_ENABLE, TPM_INT_STATUS and control the GPIO pin that is designated to the TPM over SPI interrupt.

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../sw/device/lib/dif/dif_spi_device.h)

## Register Table

* [Register Table](registers.md#registers)
