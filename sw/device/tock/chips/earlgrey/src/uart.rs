use tock_deps::kernel as kernel;

use kernel::common::StaticRef;
use opentitan_common::uart::{Uart, UartRegisters};

use crate::chip;

pub static mut UART0: Uart = Uart::new(UART0_BASE, chip::CHIP_FREQ);

const UART0_BASE: StaticRef<UartRegisters> =
    unsafe { StaticRef::new(0x4000_0000 as *const UartRegisters) };
