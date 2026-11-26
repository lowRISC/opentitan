// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! Pads the gpio tests drive and read from both the chip and the host.

use ot_hal::top::earlgrey::PinmuxMioOut;

/// A MIO pad and whether the host can test it on each board.
pub struct Pad {
    pub name: &'static str,
    pub valid_cw310: bool,
    pub valid_cw340: bool,
    pub valid_silicon: bool,
}

/// All MIO pads in MIO order, `MIO_PADS[i]` is MIO pad i.
///
/// A pad is valid on a board if a plain HyperDebug GPIO is behind it and nothing else drives it.
/// - Valid on CW310: IOR6/7, IOR10-13
/// - Valid on CW340: IOA2/3, IOB6/8, IOC10-12, IOR0-2, IOR7, IOR10-13
/// - Valid on Silicon: IOA6, IOB6, IOC9-12, IOR5-7, IOR10-13
///
/// See the `top_earlgrey/data/pins_{cw310_hyperdebug,cw341}.xdc` files. Not used on the CW340:
/// - IOA0, IOA1, IOA4-6: JTAG
/// - IOA7, IOA8, IOB0-2, IOB9-12: HyperDebug I2C and SPI2 pins
/// - IOB3-5: HyperDebug SPI2 and UART3 pins
/// - IOB7: I3C test board UART TX, driven permanently by the board
/// - IOC0-2: SW Strap 0-2
/// - IOC3-4: UART0 RX/TX (requires rework as test uses a UART console)
/// - IOC5: TAP Strap 1
/// - IOC6: PWM / EXT_CLK
/// - IOC7: USB VBUS DETECT
/// - IOC8: TAP Strap 0
/// - IOC9: PMOD2 IO2
/// - IOR3-6: HyperDebug UART4 and UART5 pins
/// - IOR8-9: sysrst_ctrl ec_rst_l and flash_wp_l
#[rustfmt::skip]
pub const MIO_PADS: &[Pad] = &[
    Pad { name: "SPI_HOST_D0",   valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 0
    Pad { name: "SPI_HOST_D1",   valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 1
    Pad { name: "SPI_HOST_D2",   valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 2
    Pad { name: "SPI_HOST_D3",   valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 3
    Pad { name: "SPI_HOST_CLK",  valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 4
    Pad { name: "SPI_HOST_CS_L", valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 5
    Pad { name: "SPI_DEV_D0",    valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 6
    Pad { name: "SPI_DEV_D1",    valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 7
    Pad { name: "SPI_DEV_D2",    valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 8
    Pad { name: "SPI_DEV_D3",    valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 9
    Pad { name: "SPI_DEV_CLK",   valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 10
    Pad { name: "SPI_DEV_CS_L",  valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 11
    Pad { name: "IOA0",  valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 12
    Pad { name: "IOA1",  valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 13
    Pad { name: "IOA2",  valid_cw310: false, valid_cw340: true,  valid_silicon: false },  // MIO Pad 14
    Pad { name: "IOA3",  valid_cw310: false, valid_cw340: true,  valid_silicon: false },  // MIO Pad 15
    Pad { name: "IOA4",  valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 16
    Pad { name: "IOA5",  valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 17
    Pad { name: "IOA6",  valid_cw310: false, valid_cw340: false, valid_silicon: true  },  // MIO Pad 18
    Pad { name: "IOA7",  valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 19
    Pad { name: "IOA8",  valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 20
    Pad { name: "IOB0",  valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 21
    Pad { name: "IOB1",  valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 22
    Pad { name: "IOB2",  valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 23
    Pad { name: "IOB3",  valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 24
    Pad { name: "IOB4",  valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 25
    Pad { name: "IOB5",  valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 26
    Pad { name: "IOB6",  valid_cw310: false, valid_cw340: true,  valid_silicon: true  },  // MIO Pad 27
    Pad { name: "IOB7",  valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 28
    Pad { name: "IOB8",  valid_cw310: false, valid_cw340: true,  valid_silicon: false },  // MIO Pad 29
    Pad { name: "IOB9",  valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 30
    Pad { name: "IOB10", valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 31
    Pad { name: "IOB11", valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 32
    Pad { name: "IOB12", valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 33
    Pad { name: "IOC0",  valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 34
    Pad { name: "IOC1",  valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 35
    Pad { name: "IOC2",  valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 36
    Pad { name: "IOC3",  valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 37
    Pad { name: "IOC4",  valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 38
    Pad { name: "IOC5",  valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 39
    Pad { name: "IOC6",  valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 40
    Pad { name: "IOC7",  valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 41
    Pad { name: "IOC8",  valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 42
    Pad { name: "IOC9",  valid_cw310: false, valid_cw340: false, valid_silicon: true  },  // MIO Pad 43
    Pad { name: "IOC10", valid_cw310: false, valid_cw340: true,  valid_silicon: true  },  // MIO Pad 44
    Pad { name: "IOC11", valid_cw310: false, valid_cw340: true,  valid_silicon: true  },  // MIO Pad 45
    Pad { name: "IOC12", valid_cw310: false, valid_cw340: true,  valid_silicon: true  },  // MIO Pad 46
    Pad { name: "IOR0",  valid_cw310: false, valid_cw340: true,  valid_silicon: false },  // MIO Pad 47
    Pad { name: "IOR1",  valid_cw310: false, valid_cw340: true,  valid_silicon: false },  // MIO Pad 48
    Pad { name: "IOR2",  valid_cw310: false, valid_cw340: true,  valid_silicon: false },  // MIO Pad 49
    Pad { name: "IOR3",  valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 50
    Pad { name: "IOR4",  valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 51
    Pad { name: "IOR5",  valid_cw310: false, valid_cw340: false, valid_silicon: true  },  // MIO Pad 52
    Pad { name: "IOR6",  valid_cw310: true,  valid_cw340: false, valid_silicon: true  },  // MIO Pad 53
    Pad { name: "IOR7",  valid_cw310: true,  valid_cw340: true,  valid_silicon: true  },  // MIO Pad 54
    Pad { name: "IOR8",  valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 55
    Pad { name: "IOR9",  valid_cw310: false, valid_cw340: false, valid_silicon: false },  // MIO Pad 56
    Pad { name: "IOR10", valid_cw310: true,  valid_cw340: true,  valid_silicon: true  },  // MIO Pad 57
    Pad { name: "IOR11", valid_cw310: true,  valid_cw340: true,  valid_silicon: true  },  // MIO Pad 58
    Pad { name: "IOR12", valid_cw310: true,  valid_cw340: true,  valid_silicon: true  },  // MIO Pad 59
    Pad { name: "IOR13", valid_cw310: true,  valid_cw340: true,  valid_silicon: true  },  // MIO Pad 60
];

/// Returns whether the host can test the pad on the board of the transport interface.
pub fn is_valid_pad(pad: &Pad, interface: &str) -> bool {
    match interface {
        "hyper310" => pad.valid_cw310,
        "hyper340" => pad.valid_cw340,
        "teacup" => pad.valid_silicon,
        _ => false,
    }
}

/// Returns the pads valid on the CW340.
pub fn cw340_pads() -> Vec<PinmuxMioOut> {
    MIO_PADS
        .iter()
        .enumerate()
        .filter(|(_, pad)| pad.valid_cw340)
        .map(|(mio, _)| PinmuxMioOut(mio as u32))
        .collect()
}

/// The pad each GPIO pin can reach in the sparse pinmux, as `GPIO_PIN_PADS[instance][pin]`.
///
/// Hand-kept copy of the `gpio0` and `gpio1` pads in `top_earlgrey.hjson`, like
/// `kPinmuxTestutilsGpioPads` in `pinmux_testutils.c`. gpio1 pins 29-31 repeat the pads of pins
/// 25-27 (IOR10-IOR12).
pub const GPIO_PIN_PADS: [[PinmuxMioOut; 32]; 2] = [
    [
        PinmuxMioOut::SpiHostD0,
        PinmuxMioOut::SpiHostD1,
        PinmuxMioOut::SpiHostD2,
        PinmuxMioOut::SpiHostD3,
        PinmuxMioOut::SpiHostClk,
        PinmuxMioOut::SpiHostCsL,
        PinmuxMioOut::SpiDevD0,
        PinmuxMioOut::SpiDevD1,
        PinmuxMioOut::SpiDevD2,
        PinmuxMioOut::SpiDevD3,
        PinmuxMioOut::SpiDevClk,
        PinmuxMioOut::SpiDevCsL,
        PinmuxMioOut::Ioa0,
        PinmuxMioOut::Ioa1,
        PinmuxMioOut::Ioa2,
        PinmuxMioOut::Ioa3,
        PinmuxMioOut::Ioa4,
        PinmuxMioOut::Ioa5,
        PinmuxMioOut::Ioa6,
        PinmuxMioOut::Ioa7,
        PinmuxMioOut::Ioa8,
        PinmuxMioOut::Iob0,
        PinmuxMioOut::Iob1,
        PinmuxMioOut::Iob2,
        PinmuxMioOut::Iob3,
        PinmuxMioOut::Iob4,
        PinmuxMioOut::Iob5,
        PinmuxMioOut::Iob6,
        PinmuxMioOut::Iob7,
        PinmuxMioOut::Iob8,
        PinmuxMioOut::Iob9,
        PinmuxMioOut::Iob10,
    ],
    [
        PinmuxMioOut::Iob11,
        PinmuxMioOut::Iob12,
        PinmuxMioOut::Ioc0,
        PinmuxMioOut::Ioc1,
        PinmuxMioOut::Ioc2,
        PinmuxMioOut::Ioc3,
        PinmuxMioOut::Ioc4,
        PinmuxMioOut::Ioc5,
        PinmuxMioOut::Ioc6,
        PinmuxMioOut::Ioc7,
        PinmuxMioOut::Ioc8,
        PinmuxMioOut::Ioc9,
        PinmuxMioOut::Ioc10,
        PinmuxMioOut::Ioc11,
        PinmuxMioOut::Ioc12,
        PinmuxMioOut::Ior0,
        PinmuxMioOut::Ior1,
        PinmuxMioOut::Ior2,
        PinmuxMioOut::Ior3,
        PinmuxMioOut::Ior4,
        PinmuxMioOut::Ior5,
        PinmuxMioOut::Ior6,
        PinmuxMioOut::Ior7,
        PinmuxMioOut::Ior8,
        PinmuxMioOut::Ior9,
        PinmuxMioOut::Ior10,
        PinmuxMioOut::Ior11,
        PinmuxMioOut::Ior12,
        PinmuxMioOut::Ior13,
        PinmuxMioOut::Ior10,
        PinmuxMioOut::Ior11,
        PinmuxMioOut::Ior12,
    ],
];

/// Returns the GPIO instance and pin that reach the pad, the lowest pin if several do.
pub fn gpio_pin_of_pad(pad: PinmuxMioOut) -> Option<(u8, u32)> {
    GPIO_PIN_PADS
        .iter()
        .enumerate()
        .find_map(|(instance, pads)| {
            pads.iter()
                .position(|&p| p == pad)
                .map(|pin| (instance as u8, pin as u32))
        })
}
