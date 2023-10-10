// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{ensure, Result};

use crate::util::tty::{scan_usb_ttys, UsbTty};

pub trait Board {
    const VENDOR_ID: u16 = 0x2b3e;
    const PRODUCT_ID: u16;

    // Pins needed for SPI on the Chip Whisperer board.
    const PIN_CLK: &'static str;
    const PIN_SDI: &'static str;
    const PIN_SDO: &'static str;
    const PIN_CS: &'static str;
    // Pins needed for reset & bootstrap on the Chip Whisperer board.
    const PIN_TRST: &'static str;
    const PIN_POR_N: &'static str;
    const PIN_SW_STRAP0: &'static str;
    const PIN_SW_STRAP1: &'static str;
    const PIN_SW_STRAP2: &'static str;
    const PIN_TAP_STRAP0: &'static str;
    const PIN_TAP_STRAP1: &'static str;

    /// Auto-detect UARTs for this board (if possible).
    fn auto_detect_uarts(serial_number: &str) -> Result<Vec<String>>;
}

/// Helper function: return a list of serial port name of the
/// serial ports exported by the SAM3X with a given serial number.
/// Ports are returned by increasing interface number.
fn find_sam3x_uarts(ttys: &[UsbTty], serial_number: &str) -> Result<Vec<UsbTty>> {
    let mut ports: Vec<UsbTty> = ttys
        .iter()
        .filter(|tty| tty.serial_number == Some(serial_number.to_string()))
        .cloned()
        .collect();
    ensure!(
        ports.len() == 2,
        "The SAM3x has two serial ports but {} were found",
        ports.len()
    );
    // Sort by interface number.
    ports.sort_by(|a, b| a.interface.cmp(&b.interface));
    // Only keep the serial port name.
    Ok(ports)
}

pub struct Cw310 {}

impl Board for Cw310 {
    const PRODUCT_ID: u16 = 0xc310;

    // Pins needed for SPI on the Chip Whisperer board.
    const PIN_CLK: &'static str = "USB_SPI_SCK";
    const PIN_SDI: &'static str = "USB_SPI_COPI";
    const PIN_SDO: &'static str = "USB_SPI_CIPO";
    const PIN_CS: &'static str = "USB_SPI_CS";
    // Pins needed for reset & bootstrap on the Chip Whisperer board.
    const PIN_TRST: &'static str = "USB_A13";
    const PIN_POR_N: &'static str = "USB_A14";
    const PIN_SW_STRAP0: &'static str = "USB_A15";
    const PIN_SW_STRAP1: &'static str = "USB_A16";
    const PIN_SW_STRAP2: &'static str = "USB_A17";
    const PIN_TAP_STRAP0: &'static str = "USB_A18";
    const PIN_TAP_STRAP1: &'static str = "USB_A19";

    fn auto_detect_uarts(serial_number: &str) -> Result<Vec<String>> {
        // Per the documentation [1], the default CW310/SAM3X firmware exposes
        // two serial interfaces with two interfaces:
        // - interface 0: pins AB22/AA24, this corresponds to OT UART2 [2]
        // - interface 1: pins AA22/W24, this corresponds to OT UART0 [2]
        // The opentitanlib app expects the console UART (UART0) to be at index 0. [3]
        //
        // [1] https://rtfm.newae.com/Targets/CW310%20Bergen%20Board/
        // [2] https://github.com/lowRISC/opentitan/blob/master/hw/top_earlgrey/data/pins_cw310.xdc
        // [3] https://github.com/lowRISC/opentitan/blob/master/sw/host/opentitanlib/src/app/config/opentitan_cw310.json

        let ttys = scan_usb_ttys()?;
        let mut ports = find_sam3x_uarts(&ttys, serial_number)?;
        // Reverse ports
        ports.reverse();
        Ok(ports.into_iter().map(|tty| tty.port_name).collect())
    }
}

pub struct Cw340 {}

impl Board for Cw340 {
    const PRODUCT_ID: u16 = 0xc340;

    // Pins needed for SPI on the Chip Whisperer board.
    const PIN_SDI: &'static str = "PA26";
    const PIN_SDO: &'static str = "PA25";
    const PIN_CLK: &'static str = "PA27";
    const PIN_CS: &'static str = "PA28";
    // Pins needed for reset & bootstrap on the Chip Whisperer board.
    const PIN_TRST: &'static str = "USB_A13";
    const PIN_POR_N: &'static str = "PC30";
    const PIN_SW_STRAP0: &'static str = "PC23";
    const PIN_SW_STRAP1: &'static str = "PC22";
    const PIN_SW_STRAP2: &'static str = "PC21";
    const PIN_TAP_STRAP0: &'static str = "PB13";
    const PIN_TAP_STRAP1: &'static str = "PB12";

    fn auto_detect_uarts(serial_number: &str) -> Result<Vec<String>> {
        const USE_FTDI_FOR_SERIAL: bool = true;
        const FTDI_CW340_VID: u16 = 0x0403;
        const FTDI_CW340_PID: u16 = 0x6011;
        const FTDI_CW340_UART0_INTF: u8 = 2;
        const FTDI_CW340_UART2_INTF: u8 = 3;

        let mut ttys = scan_usb_ttys()?;
        let sam_ports = find_sam3x_uarts(&ttys, serial_number)?;

        // The CW340 has jumpers to route the UARTs to the SAM3x, to the FTDI or the HD.
        if USE_FTDI_FOR_SERIAL {
            // When routed to the FTDI, UART0 is routed to port C and UART2 to port D [1]
            // so we need to find all ttys that correspond to the FTDI and use interfaces
            // 2 and 3. In order to find the FTDI, we know the USB VID and PID and that they
            // are under the some USB hub on the board. Unfortunately, the FTDI does not
            // come programmed with a serial number which is quite harder.
            //
            // [1] https://raw.githubusercontent.com/newaetech/cw340-luna-board/main/docs/NPCA-CW340-LUNABOARD-05.PDF

            assert!(!sam_ports.is_empty()); // Should always be true since find_sam3x_uarts() already checks
            let bus = sam_ports[0].bus;
            let mut parent_ports = sam_ports[0].ports.clone();
            parent_ports.pop(); // remove last port to get to the parent
                                // Now only keep devices that match a given VID&PID and share a parent.
                                // Also only keep interfaces 2 and 3.
            ttys.retain(|tty| {
                tty.vid == FTDI_CW340_VID
                    && tty.pid == FTDI_CW340_PID
                    && tty.bus == bus
                    && !tty.ports.is_empty()
                    && tty.ports[0..tty.ports.len() - 1] == parent_ports
                    && (tty.interface == FTDI_CW340_UART0_INTF
                        || tty.interface == FTDI_CW340_UART2_INTF)
            });
            ttys.sort_by(|a, b| a.interface.cmp(&b.interface));

            Ok(ttys.into_iter().map(|tty| tty.port_name).collect())
        } else {
            // When routed to the SAM3x,the configuration is similar to the CW310 but
            // the not inverted: interface 0 corresponds to UART0, and interface 1 to UART 2.
            Ok(sam_ports.into_iter().map(|tty| tty.port_name).collect())
        }
    }
}
