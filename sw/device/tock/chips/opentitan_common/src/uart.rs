//! UART driver.

use core::cell::Cell;

use tock::kernel::common::cells::OptionalCell;
use tock::kernel::common::cells::TakeCell;
use tock::kernel::hil;
use tock::kernel::ReturnCode;

use dif::dif_bind::*;
use dif::riscv32_c_types::*;

pub struct Uart<'a> {
    base_addr: u32,
    clock_frequency: u32,
    dif_uart: OptionalCell<dif_uart_t>,
    tx_client: OptionalCell<&'a dyn hil::uart::TransmitClient>,
    rx_client: OptionalCell<&'a dyn hil::uart::ReceiveClient>,
    tx_buffer: TakeCell<'static, [u8]>,
    tx_len: Cell<usize>,
    tx_index: Cell<usize>,
}

#[derive(Copy, Clone)]
pub struct UartParams {
    pub baud_rate: u32,
}

impl Uart<'a> {
    pub const fn new(base_addr: u32, clock_frequency: u32) -> Uart<'a> {
        Uart {
            base_addr: base_addr,
            clock_frequency: clock_frequency,
            dif_uart: OptionalCell::empty(),
            tx_client: OptionalCell::empty(),
            rx_client: OptionalCell::empty(),
            tx_buffer: TakeCell::empty(),
            tx_len: Cell::new(0),
            tx_index: Cell::new(0),
        }
    }

    fn interrupt_enable(
        &self,
        interrupt: dif_uart_interrupt_t,
        enable: dif_uart_enable_t,
    ) -> ReturnCode {
        self.dif_uart.map_or(ReturnCode::FAIL, |uart| unsafe {
            match dif_uart_irq_enable(uart, interrupt, enable) {
                kDifUartOk => ReturnCode::SUCCESS,
                _ => ReturnCode::FAIL,
            }
        })
    }

    fn bytes_send(&self, data: *const u8, num_to_send: usize) -> Result<usize, ReturnCode> {
        self.dif_uart.map_or(Err(ReturnCode::FAIL), |uart| unsafe {
            let mut bytes_sent: usize = 0;
            match dif_uart_bytes_send(uart, data, num_to_send, &mut bytes_sent) {
                kDifUartOk => Ok(bytes_sent),
                _ => Err(ReturnCode::FAIL),
            }
        })
    }

    fn interrupt_state(&self, interrupt: dif_uart_interrupt_t) -> Result<bool, ReturnCode> {
        self.dif_uart.map_or(Err(ReturnCode::FAIL), |uart| unsafe {
            let mut state: dif_uart_enable_t = kDifUartDisable;
            match dif_uart_irq_state_get(uart, interrupt, &mut state) {
                kDifUartOk => Ok(state == kDifUartEnable),
                _ => Err(ReturnCode::FAIL),
            }
        })
    }

    fn interrupt_clear(&self, interrupt: dif_uart_interrupt_t) -> ReturnCode {
        self.dif_uart.map_or(ReturnCode::FAIL, |uart| unsafe {
            match dif_uart_irq_state_clear(uart, interrupt) {
                kDifUartOk => ReturnCode::SUCCESS,
                _ => ReturnCode::FAIL,
            }
        })
    }

    fn tx_buffer_process(&self) {
        let mut total_bytes_sent = self.tx_index.get();
        let total_bytes_to_send = self.tx_len.get();

        if total_bytes_sent < total_bytes_to_send {
            self.tx_buffer.map(|tx_buf| {
                let bytes_to_send = total_bytes_to_send - total_bytes_sent;

                match self.bytes_send(&tx_buf[total_bytes_sent], bytes_to_send) {
                    Ok(bytes_sent) => {
                        total_bytes_sent += bytes_sent;
                        self.tx_index.set(total_bytes_sent)
                    }
                    Err(e) => (), // TODO - return error
                }
            });
        }

        if total_bytes_sent == total_bytes_to_send {
            self.tx_client.map(|client| {
                self.tx_buffer.take().map(|tx_buf| {
                    client.transmitted_buffer(tx_buf, self.tx_len.get(), ReturnCode::SUCCESS);
                });
            });
        }
    }

    pub fn handle_interrupt(&self) {
        let interrupt = kDifUartInterruptTxWatermark;
        match self.interrupt_state(interrupt) {
            Ok(set) => {
                if set {
                    self.tx_buffer_process();
                    self.interrupt_clear(interrupt); // TODO return this
                    () // TODO - return error
                }
            }
            Err(e) => (), // TODO - return error
        }

        // TODO - let interrupt = kDifUartInterruptRxWatermark;
    }

    pub fn transmit_sync(&self, bytes: &[u8]) {
        for i in 0..bytes.len() {
            // TODO - error codes (map_or)
            self.dif_uart.map_or((), |uart| unsafe {
                if dif_uart_byte_send_polled(uart, bytes[i]) != kDifUartOk {
                    return (); // TODO - error/success
                }
            })
        }
    }
}

impl hil::uart::UartData<'a> for Uart<'a> {}
impl hil::uart::Uart<'a> for Uart<'a> {}

impl hil::uart::Configure for Uart<'a> {
    fn configure(&self, params: hil::uart::Parameters) -> ReturnCode {
        let base_addr: mmio_region_t = mmio_region_t {
            base: self.base_addr as *mut c_void,
        };

        let mut config: dif_uart_config_t = dif_uart_config_t {
            baudrate: params.baud_rate,
            clk_freq_hz: self.clock_frequency,
            parity_enable: kDifUartDisable,
            parity: kDifUartParityEven,
        };

        let mut uart: dif_uart_t = Default::default();

        unsafe {
            match dif_uart_init(base_addr, &mut config, &mut uart) {
                kDifUartOk => self.dif_uart.set(uart),
                _ => return ReturnCode::FAIL,
            }
        }

        if self.interrupt_enable(kDifUartInterruptTxWatermark, kDifUartEnable)
            != ReturnCode::SUCCESS
        {
            return ReturnCode::FAIL;
        }

        // TODO - kDifUartInterruptRxWatermark

        ReturnCode::SUCCESS
    }
}

impl hil::uart::Transmit<'a> for Uart<'a> {
    fn set_transmit_client(&self, client: &'a dyn hil::uart::TransmitClient) {
        self.tx_client.set(client);
    }

    fn transmit_buffer(
        &self,
        tx_data: &'static mut [u8],
        tx_len: usize,
    ) -> (ReturnCode, Option<&'static mut [u8]>) {
        if tx_len == 0 {
            (ReturnCode::ESIZE, Some(tx_data))
        } else if self.tx_buffer.is_some() {
            (ReturnCode::EBUSY, Some(tx_data))
        } else {
            // Save the buffer so we can keep sending it.
            self.tx_buffer.replace(tx_data);
            self.tx_len.set(tx_len);
            self.tx_index.set(0);

            self.tx_buffer_process();
            (ReturnCode::SUCCESS, None)
        }
    }

    fn transmit_abort(&self) -> ReturnCode {
        ReturnCode::FAIL
    }

    fn transmit_word(&self, _word: u32) -> ReturnCode {
        ReturnCode::FAIL
    }
}

/* UART receive is not implemented yet, mostly due to a lack of tests avaliable */
impl hil::uart::Receive<'a> for Uart<'a> {
    fn set_receive_client(&self, client: &'a dyn hil::uart::ReceiveClient) {
        self.rx_client.set(client);
    }

    fn receive_buffer(
        &self,
        _rx_buffer: &'static mut [u8],
        _rx_len: usize,
    ) -> (ReturnCode, Option<&'static mut [u8]>) {
        (ReturnCode::FAIL, None)
    }

    fn receive_abort(&self) -> ReturnCode {
        ReturnCode::FAIL
    }

    fn receive_word(&self) -> ReturnCode {
        ReturnCode::FAIL
    }
}
