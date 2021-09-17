use serde::Deserialize;

#[derive(Deserialize, Clone, Debug)]
pub enum PinMode {
    Input,
    PushPull,
    OpenDrain,
}

#[derive(Deserialize, Clone, Debug)]
pub struct PinConfiguration {
    pub name: String,
    pub mode: PinMode,
    pub initial_level: bool,
    pub pullup: bool,
    pub alias_of: String, // Name of a pin defined by the transport
}

#[derive(Deserialize, Clone, Debug)]
pub enum UartParity {
    None,
    Even,
    Odd,
    Mark,
    Space,
}

#[derive(Deserialize, Clone, Debug)]
pub enum UartStopBits {
    Stop1,
    Stop1_5,
    Stop2,
}

#[derive(Deserialize, Clone, Debug)]
pub struct UartConfiguration {
    pub name: String,
    pub baudrate: u32,
    pub parity: UartParity,
    pub stopbits: UartStopBits,
    pub alias_of: String, // Name of a uart defined by the transport
}

#[derive(Deserialize, Clone, Debug)]
pub struct SpiConfiguration {
    pub name: String,
    pub alias_of: String, // Name of a spi port defined by the transport
}

#[derive(Deserialize, Clone, Debug, PartialEq, Eq)]
pub enum FlashAddressMode {
    Mode3b,
    Mode4b,
}

#[derive(Deserialize, Clone, Debug)]
// Defines the way to reach and program flash storage
pub enum FlashDriver {
    SpiEeprom {
        size: u32,
        erase_block_size: u32,
        erase_opcode: u8,
        program_block_size: u32,
        address_mode: FlashAddressMode,
        spi_bus: String, // Name of a bus defined by the transport
        // Possibly add more fields to declare SPI mode/speed
    },
    SpiExternalDriver {
        command: String,
        spi_bus: String, // Name of a bus defined by the transport
        // Possibly add more fields to declare SPI mode/speed
    }
}

#[derive(Deserialize, Clone, Debug)]
pub struct FlashConfiguration {
    pub name: String,
    pub reset_pin: String,
    pub bootloader_pin: String, // Could be absent (empty)
    pub driver: FlashDriver,
}

#[derive(Deserialize, Clone, Debug)]
pub struct ConfigurationFile {
    pub pins: Vec<PinConfiguration>,
    pub uarts: Vec<UartConfiguration>,
    pub flash: Vec<FlashConfiguration>,
}
