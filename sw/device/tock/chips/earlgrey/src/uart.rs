use opentitan_common::uart::Uart;

use crate::chip;
use crate::chip_config::DEVICE_CONFIG;

pub static mut UART0_BAUDRATE: u32 = DEVICE_CONFIG.uart_baudrate;
pub static mut UART0: Uart = Uart::new(0x4000_0000, chip::CHIP_FREQ);
