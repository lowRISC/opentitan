use tock::kernel;

use kernel::common::StaticRef;
use opentitan_common::uart::{Uart, UartRegisters};

use crate::chip;
use crate::chip_config::DEVICE_CONFIG;

pub static mut UART0_BAUDRATE: u32 = DEVICE_CONFIG.uart_baudrate;
pub static mut UART0: Uart = Uart::new(UART0_BASE, chip::CHIP_FREQ);

const UART0_BASE: StaticRef<UartRegisters> =
    unsafe { StaticRef::new(0x4000_0000 as *const UartRegisters) };
