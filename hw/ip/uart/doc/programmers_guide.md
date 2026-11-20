# Programmer's Guide

## Initialization

### Reset

Before utilizing the UART, it is recommended to reset the UART and clear any existing state.
You can do this by writing `0x0` to the [`CTRL`](registers.md#ctrl) register, and then writing `0x1` to [`FIFO_CTRL.RXRST`](registers.md#fifo_ctrl--rxrst) and [`FIFO_CTRL.TXRST`](registers.md#fifo_ctrl--txrst), which will clear the UART's FIFOs.
It may also be advisable to write `0x0` to the [`OVRD`](registers.md#ovrd), [`TIMEOUT_CTRL`](registers.md#timeout_ctrl), and [`INTR_ENABLE`](registers.md#intr_enable) registers to clear any previous configuration, and clear any existing interrupts by writing `0xffff_ffff` to [`INTR_STATE`](registers.md#intr_state).

### Configuration

To program the baud rate of the UART, the clock rate of the Numerically Controlled Oscillator ([`CTRL.NCO`](registers.md#ctrl--nco)) can be configured.
The `NCO` is calculated using the following equation:

$$ NCO = {{16 * 2^{bits(NCO)} * f\_{baud}} \over {f\_{pclk}}} $$

Where `f_baud` is the desired baud rate in bits per second, and `f_pclk` is the fixed clock frequency of the UART's main clock input.
For example, in Earlgrey's design this is currently configured as the IO clock divided by 4.
The additional multiple of 16 arises from the 16x [oversampling](theory_of_operation.md#reception) applied by the UART.

The [`CTRL.NCO`](registers.md#ctrl--nco) field is 16 bits, meaning that you can use a simplified calculation:

$$ NCO = {{2^{20} * f\_{baud}} \over {f\_{pclk}}} $$

Note that the result of the above formulae can be some non-integer value, whilst the [`CTRL.NCO`](registers.md#ctrl--nco) field only accepts integer values.
See the "[Reception](theory_of_operation.md#reception)" and "[Setting the baud rate](theory_of_operation.md#setting-the-baud-rate)" sections of the theory of operation documentation for more discussion of these calculations and targeting specific baud rate errors -- and clarifications on cases where extra care may be needed.

Also note that when calculating the baud rate, some care is needed not to overflow 32 bit integer types.
As the baud rate is multiplied by `2^20`, and baud rates can easily exceed 12 bits, you must be careful to use 64-bit arithmetic.
The following code snippet shows an example of handling this:

```cpp
#define CLK_FIXED_FREQ_HZ (24ULL * 1000 * 1000)

void uart_init(unsigned int baud) {
  uint64_t nco = ((uint64_t)baud << 20) / CLK_FIXED_FREQ_HZ;
  // ...
}
```

Another recommendation is to compute the masked version of the final 16-bit `NCO` value, to be sure that it matches the calculated `NCO`.
For certain configurations (e.g. a UART baud rate of 1.6 Mbps, and a clock of 24 MHz) this may not be the case -- the requested baud rate may be too high for the clock frequency.
In these cases, you must determine if the error is tolerable and how such cases should be handled.

Then, the following steps can be customized to configure the UART as desired:

1. Write the [`CTRL`](registers.md#ctrl) register with the calculated [`CTRL.NCO`](registers.md#ctrl--nco) value, also writing `0x1` to [`CTRL.TX`](registers.md#ctrl--tx) and [`CTRL.RX`](registers.md#ctrl--rx) fields to enable UART transmission and reception respectively.
  Parity can be optionally enabled by writing `0x1` to the [`CTRL.PARITY_EN`](registers.md#ctrl--parity_en) field, whereas [`CTRL.PARITY_ODD`](registers.md#ctrl--parity_odd) configures the type of parity (`0x0` is even, `0x1` is odd).

2. Optionally write FIFO watermark interrupt thresholds to the [`FIFO_CTRL.TXILVL`](registers.md#fifo_ctrl--txilvl) and [`FIFO_CTRL.RXILVL`](registers.md#fifo_ctrl--rxilvl) fields.
  See the register documentation for exact thresholds -- for example, you could write a TX level of `0x4` and an RX level of `0x0` to configure interrupts when there are 16 or less characters in the TX FIFO, and 1 or more characters in the RX FIFO.

3. Optionally write `0x1` to the fields of the [`INTR_ENABLE`](registers.md#intr_enable) register to configure any interrupts that you would like to enable.
  A common configuration would be to enable the `tx_watermark` and `rx_watermark` interrupts, along with any break, error and/or overflow conditions (`rx_break_err`, `rx_frame_err`, `rx_parity_err` and `rx_overflow`).
  Note that these UART interrupts should also be enabled at the processor level via the PLIC.

## Common Examples

The following code shows the necessary steps to transmit a string of characters.

```cpp
bool uart_tx_full() {
  return (READ_REG(UART_STATUS_REG) & UART_STATUS_TXFULL_BIT) != 0u;
}

void uart_send_char(char val) {
  while (uart_tx_full()) {}
  WRITE_REG(UART_WDATA_REG, val);
}

void uart_send_str(char *str) {
  while (*str != '\0') {
    uart_send_char(*str++);
  }
}
```

Do the following to receive a character, returning `-1` if RX is empty.

```cpp
bool uart_rx_empty() {
  return (READ_REG(UART_STATUS_REG) & UART_STATUS_RXEMPTY_BIT) != 0u;
}

char uart_rcv_char() {
  if (uart_rx_empty()) {
    return -1;
  }
  return (char)(READ_REG(UART_RDATA_REG) & 0xff);
}
```

## Interrupt Handling

The code below shows one example of how to handle all UART interrupts in one service routine.

```cpp

void uart_interrupt_routine() {
  uint32_t intr_state = READ_REG(UART_INTR_STATE_REG);
  uint32_t intr_enable = READ_REG(UART_INTR_ENABLE_REG);

  // Disable UART interrupts (clear bits 7:0).
  WRITE_REG(UART_INTR_ENABLE_REG, intr_enable & 0xFFFFFF00);

  if (intr_state & UART_INTR_STATE_RX_PARITY_ERR_MASK) {
    // Do something...
  }
  if (intr_state & UART_INTR_STATE_RX_BREAK_ERR_MASK) {
    // Do something...
  }
  // Etc. (repeated for the frame error and TX/RX overflow errors)

  if (intr_state & UART_INTR_STATE_RX_WATERMARK_MASK) {
    while (1) {
      char recvd = uart_rcv_char();
      if (recvd == 0xff) {
        break;
      }
      // Do something with `recvd`, e.g. append to some `uart_buf`.
    }
  }

  // Clear interrupt state
  WRITE_REG(UART_INTR_STATE_REG, intr_state);

  // Restore interrupt enable
  WRITE_REG(UART_INTR_ENABLE, intr_enable);

  // Also complete the IRQ at the PLIC...
}
```

One potential use of the [`INTR_STATE.RX_TIMEOUT`](registers.md#intr_state) interrupt is for when the [`FIFO_CTRL.RXILVL`](registers.md#fifo_ctrl--rxilvl) field is configured for some watermark value **greater than one**.
In this scenario, an interrupt will only be fired when the the FIFO is filled over a certain level.
If the remote device sends fewer characters than the configured watermark before it stops sending (e.g. it may be waiting for an acknowledgement) then the usual `rx_watermark` interrupt would not be raised.
Instead, after some time an `rx_timeout` interrupt can be generated that would then allow the device to read these additional characters.

The [`TIMEOUT_CTRL`](registers.md#timeout_ctrl) register can be used to enable and configure this timeout value.
This timeout can therefore be selected based on the worst latency experienced by any individual character.
If characters happen to continue to arrive *just slower* than the configured timeout (the second character arrives just before the timeout for the first, the third just before the timeout for the second, etc.) then in this case the host will eventually receive an `rx_watermark` interrupt.
This will happen `((RXILVL - 1) * RX_TIMEOUT)` units after the first character was received, providing an upper bound on the possible latency.

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../sw/device/lib/dif/dif_uart.h)
