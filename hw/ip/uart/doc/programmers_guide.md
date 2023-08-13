# Programmer's Guide

## Initialization

The following code snippet demonstrates initializing the UART to a programmable
baud rate, clearing the RX and TX FIFO, setting up the FIFOs for interrupt
levels, and enabling some interrupts. The NCO register controls the baud rate,
and should be set using the equation below, where `f_pclk` is the fixed clock
frequency and `f_baud` is the baud rate in bits per second. The UART uses the
primary clock `clk_i` as a clock source.

$$ NCO = {{2^{20} * f\_{baud}} \over {f\_{pclk}}} $$

Note that the NCO result from the above formula can be a fraction but
the NCO register only accepts an integer value. See the
[Reception](#reception) and [Setting the baud
rate](#setting-the-baud-rate) sections for more discussion of the
baud rate error target and when care is needed.

Also note that because the baud rate is multiplied by 2^20 care is
needed not to overflow 32-bit registers. Baud rates can easily be more
than 12 bits. The code below is careful to force 64-bit
arithmetic. (Even if the compiler is pre-computing constants there can
be unexpected overflow).

```cpp
#define CLK_FIXED_FREQ_HZ (50ULL * 1000 * 1000)

void uart_init(unsigned int baud) {
  // nco = 2^20 * baud / fclk. Assume NCO width is 16bit.
  uint64_t uart_ctrl_nco = ((uint64_t)baud << 20) / CLK_FIXED_FREQ_HZ;
  REG32(UART_CTRL(0)) =
      ((uart_ctrl_nco & UART_CTRL_NCO_MASK) << UART_CTRL_NCO_OFFSET) |
      (1 << UART_CTRL_TX) |
      (1 << UART_CTRL_RX);

  // clear FIFOs and set up to interrupt on any RX, half-full TX
  *UART_FIFO_CTRL_REG =
      UART_FIFO_CTRL_RXRST                 | // clear both FIFOs
      UART_FIFO_CTRL_TXRST                 |
      (UART_FIFO_CTRL_RXILVL_RXFULL_1 <<3) | // intr on RX 1 character
      (UART_FIFO_CTRL_TXILVL_TXFULL_16<<5) ; // intr on TX 16 character

  // enable only RX, overflow, and error interrupts
  *UART_INTR_ENABLE_REG =
      UART_INTR_ENABLE_RX_WATERMARK_MASK  |
      UART_INTR_ENABLE_TX_OVERFLOW_MASK   |
      UART_INTR_ENABLE_RX_OVERFLOW_MASK   |
      UART_INTR_ENABLE_RX_FRAME_ERR_MASK  |
      UART_INTR_ENABLE_RX_PARITY_ERR_MASK;

  // at the processor level, the UART interrupts should also be enabled
}
```

## Common Examples

The following code shows the steps to transmit a string of characters.

```cpp
int uart_tx_rdy() {
  return ((*UART_FIFO_STATUS_REG & UART_FIFO_STATUS_TXLVL_MASK) == 32) ? 0 : 1;
}

void uart_send_char(char val) {
  while(!uart_tx_rdy()) {}
  *UART_WDATA_REG = val;
}

void uart_send_str(char *str) {
  while(*str != '\0') {
    uart_send_char(*str++);
}
```

Do the following to receive a character, with -1 returned if RX is empty.

```cpp
int uart_rx_empty() {
  return ((*UART_FIFO_STATUS_REG & UART_FIFO_STATUS_RXLVL_MASK) ==
          (0 << UART_FIFO_STATUS_RXLVL_LSB)) ? 1 : 0;
}

int uart_rcv_char() {
  if(uart_rx_empty())
    return -1;
  return *UART_RDATA_REG;
}
```

## Interrupt Handling

The code below shows one example of how to handle all UART interrupts
in one service routine.

```cpp
void uart_interrupt_routine() {
  volatile uint32 intr_state = *UART_INTR_STATE_REG;
  uint32 intr_state_mask = 0;
  char uart_ch;
  uint32 intr_enable_reg;

  // Turn off Interrupt Enable
  intr_enable_reg = *UART_INTR_ENABLE_REG;
  *UART_INTR_ENABLE_REG = intr_enable_reg & 0xFFFFFF00; // Clr bits 7:0

  if (intr_state & UART_INTR_STATE_RX_PARITY_ERR_MASK) {
    // Do something ...

    // Store Int mask
    intr_state_mask |= UART_INTR_STATE_RX_PARITY_ERR_MASK;
  }

  if (intr_state & UART_INTR_STATE_RX_BREAK_ERR_MASK) {
    // Do something ...

    // Store Int mask
    intr_state_mask |= UART_INTR_STATE_RX_BREAK_ERR_MASK;
  }

  // .. Frame Error

  // TX/RX Overflow Error

  // RX Int
  if (intr_state & UART_INTR_STATE_RX_WATERMARK_MASK) {
    while(1) {
      uart_ch = uart_rcv_char();
      if (uart_ch == 0xff) break;
      uart_buf.append(uart_ch);
    }
    // Store Int mask
    intr_state_mask |= UART_INTR_STATE_RX_WATERMARK_MASK;
  }

  // Clear Interrupt State
  *UART_INTR_STATE_REG = intr_state_mask;

  // Restore Interrupt Enable
  *UART_INTR_ENABLE_REG = intr_enable_reg;
}
```

One use of the `rx_timeout` interrupt is when the [`FIFO_CTRL.RXILVL`](registers.md#fifo_ctrl--rxilvl)
is set greater than one, so an interrupt is only fired when the fifo
is full to a certain level. If the remote device sends fewer than the
watermark number of characters before stopping sending (for example it
is waiting an acknowledgement) then the usual `rx_watermark` interrupt
would not be raised. In this case an `rx_timeout` would generate an
interrupt that allows the host to read these additional characters. The
`rx_timeout` can be selected based on the worst latency experienced by a
character. The worst case latency experienced by a character will happen
if characters happen to arrive just slower than the timeout: the second
character arrives just before the timeout for the first (resetting the
timer), the third just before the timeout from the second etc. In this
case the host will eventually get a watermark interrupt, this will happen
`((RXILVL - 1)*timeout)` after the first character was received.

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../sw/device/lib/dif/dif_uart.h)
