// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::io::uart::Uart;
use anyhow::Result;
use std::io::{Read, Write};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum XmodemError {
    #[error("Cancelled")]
    Cancelled,
    #[error("Exhausted retries: {0}")]
    ExhaustedRetries(usize),
    #[error("Unsupported mode: {0}")]
    UnsupportedMode(String),
}

#[derive(Debug, Clone, Copy)]
#[repr(usize)]
pub enum XmodemBlock {
    Block128 = 128,
    Block1k = 1024,
}

#[derive(Debug)]
pub struct Xmodem {
    pub max_errors: usize,
    pub pad_byte: u8,
    pub block_len: XmodemBlock,
}

impl Default for Xmodem {
    fn default() -> Self {
        Self::new()
    }
}

impl Xmodem {
    const POLYNOMIAL: u16 = 0x1021;
    const CRC: u8 = 0x43;
    const SOH: u8 = 0x01;
    const STX: u8 = 0x02;
    const EOF: u8 = 0x04;
    const ACK: u8 = 0x06;
    const NAK: u8 = 0x15;
    const CAN: u8 = 0x18;

    pub fn new() -> Self {
        Xmodem {
            max_errors: 16,
            pad_byte: 0xff,
            block_len: XmodemBlock::Block1k,
        }
    }

    fn crc16(buf: &[u8]) -> u16 {
        let mut crc = 0u16;
        for byte in buf {
            crc ^= (*byte as u16) << 8;
            for _bit in 0..8 {
                let msb = crc & 0x8000 != 0;
                crc <<= 1;
                if msb {
                    crc ^= Self::POLYNOMIAL;
                }
            }
        }
        crc
    }

    pub fn send(&self, uart: &dyn Uart, data: impl Read) -> Result<()> {
        self.send_start(uart)?;
        self.send_data(uart, data)?;
        self.send_finish(uart)?;
        Ok(())
    }

    fn send_start(&self, uart: &dyn Uart) -> Result<()> {
        let mut ch = 0u8;
        let mut cancels = 0usize;
        // Wait for the XMODEM CRC start sequence.
        loop {
            uart.read(std::slice::from_mut(&mut ch))?;
            match ch {
                Self::CRC => {
                    return Ok(());
                }
                Self::NAK => {
                    return Err(XmodemError::UnsupportedMode("standard checksums".into()).into());
                }
                Self::CAN => {
                    cancels += 1;
                    if cancels >= 2 {
                        return Err(XmodemError::Cancelled.into());
                    }
                }
                _ => {
                    let p = ch as char;
                    log::info!(
                        "Unknown byte received while waiting for XMODEM start: {p:?} ({ch:#x?})"
                    );
                }
            }
        }
    }

    fn send_data(&self, uart: &dyn Uart, mut data: impl Read) -> Result<()> {
        let mut block = 0usize;
        let mut errors = 0usize;
        loop {
            block += 1;
            let mut buf = vec![self.pad_byte; self.block_len as usize + 3];
            let n = data.read(&mut buf[3..])?;
            if n == 0 {
                break;
            }

            buf[0] = match self.block_len {
                XmodemBlock::Block128 => Self::SOH,
                XmodemBlock::Block1k => Self::STX,
            };
            buf[1] = block as u8;
            buf[2] = 255 - buf[1];
            let crc = Self::crc16(&buf[3..]);
            buf.push((crc >> 8) as u8);
            buf.push((crc & 0xFF) as u8);
            log::info!("Sending block {block}");

            let mut cancels = 0usize;
            loop {
                uart.write(&buf)?;
                let mut ch = 0u8;
                uart.read(std::slice::from_mut(&mut ch))?;
                match ch {
                    Self::ACK => break,
                    Self::NAK => {
                        log::info!("XMODEM send got NAK.  Retrying.");
                        errors += 1;
                    }
                    Self::CAN => {
                        cancels += 1;
                        if cancels >= 2 {
                            return Err(XmodemError::Cancelled.into());
                        }
                    }
                    _ => {
                        log::info!("Expected ACK. Got {ch:#x}.");
                        errors += 1;
                    }
                }
                if errors >= self.max_errors {
                    return Err(XmodemError::ExhaustedRetries(errors).into());
                }
            }
        }
        Ok(())
    }

    fn send_finish(&self, uart: &dyn Uart) -> Result<()> {
        uart.write(&[Self::EOF])?;
        let mut ch = 0u8;
        uart.read(std::slice::from_mut(&mut ch))?;
        if ch != Self::ACK {
            log::info!("Expected ACK. Got {ch:#x}.");
        }
        Ok(())
    }

    pub fn receive(&self, uart: &dyn Uart, data: &mut impl Write) -> Result<()> {
        // Send the byte indicating the protocol we want (Xmodem-CRC).
        uart.write(&[Self::CRC])?;

        let mut block = 1u8;
        let mut errors = 0usize;
        loop {
            // The first byte of the packet is the packet type which indicates the block size.
            let mut byte = 0u8;
            uart.read(std::slice::from_mut(&mut byte))?;
            let block_len = match byte {
                Self::SOH => 128,
                Self::STX => 1024,
                Self::EOF => {
                    // End of file.  Send an ACK.
                    uart.write(&[Self::ACK])?;
                    break;
                }
                _ => {
                    return Err(XmodemError::UnsupportedMode(format!(
                        "bad start of packet: {byte:?}"
                    ))
                    .into());
                }
            };

            // The next two bytes are the block number and its complement.
            let mut bnum = 0u8;
            let mut bcom = 0u8;
            uart.read(std::slice::from_mut(&mut bnum))?;
            uart.read(std::slice::from_mut(&mut bcom))?;
            let cancel = block != bnum || bnum != 255 - bcom;

            // The next `block_len` bytes are the packet itself.
            let mut buffer = Vec::new();
            buffer.resize(block_len, 0);
            let mut total = 0;
            while total < block_len {
                let n = uart.read(&mut buffer[total..])?;
                total += n;
            }

            // The final two bytes are the CRC16.
            let mut crc1 = 0u8;
            let mut crc2 = 0u8;
            uart.read(std::slice::from_mut(&mut crc1))?;
            uart.read(std::slice::from_mut(&mut crc2))?;
            let crc = u16::from_be_bytes([crc1, crc2]);

            // If we should cancel, do it now.
            if cancel {
                uart.write(&[Self::CAN, Self::CAN])?;
                return Err(XmodemError::Cancelled.into());
            }
            if Self::crc16(&buffer) == crc {
                // CRC was good; send an ACK and keep the data.
                uart.write(&[Self::ACK])?;
                data.write_all(&buffer)?;
                block = block.wrapping_add(1);
            } else {
                uart.write(&[Self::NAK])?;
                errors += 1;
            }
            if errors >= self.max_errors {
                return Err(XmodemError::ExhaustedRetries(errors).into());
            }
        }
        Ok(())
    }
}

// The xmodem tests depend on the lrzsz package which contains the classic
// XMODEM/YMODEM/ZMODEM file transfer programs dating back to the 1980s and
// 1990s.
#[cfg(test)]
mod test {
    use super::*;
    use crate::util::testing::{ChildUart, TransferState};
    use crate::util::tmpfilename;

    #[rustfmt::skip]
    const GETTYSBURG: &str =
r#"Four score and seven years ago our fathers brought forth on this
continent, a new nation, conceived in Liberty, and dedicated to the
proposition that all men are created equal.
Now we are engaged in a great civil war, testing whether that nation,
or any nation so conceived and so dedicated, can long endure. We are met
on a great battle-field of that war. We have come to dedicate a portion
of that field, as a final resting place for those who here gave their
lives that that nation might live. It is altogether fitting and proper
that we should do this.
But, in a larger sense, we can not dedicate -- we can not consecrate --
we can not hallow -- this ground. The brave men, living and dead, who
struggled here, have consecrated it, far above our poor power to add or
detract. The world will little note, nor long remember what we say here,
but it can never forget what they did here. It is for us the living,
rather, to be dedicated here to the unfinished work which they who
fought here have thus far so nobly advanced. It is rather for us to be
here dedicated to the great task remaining before us -- that from these
honored dead we take increased devotion to that cause for which they gave
the last full measure of devotion -- that we here highly resolve that
these dead shall not have died in vain -- that this nation, under God,
shall have a new birth of freedom -- and that government of the people,
by the people, for the people, shall not perish from the earth.
Abraham Lincoln
November 19, 1863
"#;

    #[test]
    fn test_xmodem_send() -> Result<()> {
        let filename = tmpfilename("test_xmodem_send");
        let child = ChildUart::spawn(&["rx", "--with-crc", &filename])?;
        let xmodem = Xmodem::new();
        let gettysburg = GETTYSBURG.as_bytes();
        xmodem.send(&child, gettysburg)?;
        assert!(child.wait()?.success());
        let result = std::fs::read(&filename)?;
        // The file should be a multiple of the block size.
        assert_eq!(result.len() % 1024, 0);
        assert!(result.len() >= gettysburg.len());
        assert_eq!(&result[..gettysburg.len()], gettysburg);
        Ok(())
    }

    #[test]
    fn test_xmodem_send_with_errors() -> Result<()> {
        let filename = tmpfilename("test_xmodem_send_with_errors");
        let child = ChildUart::spawn_corrupt(
            &["rx", "--with-crc", &filename],
            TransferState::default(),
            TransferState::new(&[3, 136]),
        )?;
        let xmodem = Xmodem {
            max_errors: 2,
            pad_byte: 0,
            block_len: XmodemBlock::Block128,
        };
        let gettysburg = GETTYSBURG.as_bytes();
        let err = xmodem.send(&child, gettysburg);
        assert!(err.is_err());
        assert_eq!(err.unwrap_err().to_string(), "Exhausted retries: 2");
        Ok(())
    }

    #[test]
    fn test_xmodem_checksum_mode() -> Result<()> {
        let filename = tmpfilename("test_xmodem_checksum_mode");
        let child = ChildUart::spawn(&["rx", &filename])?;
        let xmodem = Xmodem::new();
        let gettysburg = GETTYSBURG.as_bytes();
        let result = xmodem.send(&child, gettysburg);
        assert_eq!(child.wait()?.success(), false);
        assert!(result.is_err());
        let err = result.unwrap_err().downcast::<XmodemError>().unwrap();
        assert_eq!(err.to_string(), "Unsupported mode: standard checksums");
        Ok(())
    }

    #[test]
    fn test_xmodem_recv() -> Result<()> {
        let filename = tmpfilename("test_xmodem_recv");
        let gettysburg = GETTYSBURG.as_bytes();
        std::fs::write(&filename, gettysburg)?;
        let child = ChildUart::spawn(&["sx", &filename])?;
        let xmodem = Xmodem::new();
        let mut result = Vec::new();
        xmodem.receive(&child, &mut result)?;
        assert!(child.wait()?.success());
        // The received data should be a multiple of the block size.
        assert_eq!(result.len() % 128, 0);
        assert!(result.len() >= gettysburg.len());
        assert_eq!(&result[..gettysburg.len()], gettysburg);
        Ok(())
    }

    #[test]
    fn test_xmodem1k_recv() -> Result<()> {
        let filename = tmpfilename("test_xmodem1k_recv");
        let gettysburg = GETTYSBURG.as_bytes();
        std::fs::write(&filename, gettysburg)?;
        let child = ChildUart::spawn(&["sx", "--1k", &filename])?;
        let xmodem = Xmodem::new();
        let mut result = Vec::new();
        xmodem.receive(&child, &mut result)?;
        assert!(child.wait()?.success());
        // The received data should be a multiple of the block size.
        // Even though we're using 1K blocks, the lrzsz programs use
        // shorter blocks for the last bit of the data.
        assert_eq!(result.len() % 128, 0);
        assert!(result.len() >= gettysburg.len());
        assert_eq!(&result[..gettysburg.len()], gettysburg);
        Ok(())
    }

    #[test]
    fn test_xmodem_recv_with_errors() -> Result<()> {
        let filename = tmpfilename("test_xmodem_recv_with_errors");
        let gettysburg = GETTYSBURG.as_bytes();
        std::fs::write(&filename, gettysburg)?;
        let child = ChildUart::spawn_corrupt(
            &["sx", &filename],
            TransferState::new(&[3, 136]),
            TransferState::default(),
        )?;
        let xmodem = Xmodem {
            max_errors: 2,
            pad_byte: 0,
            block_len: XmodemBlock::Block128,
        };
        let mut result = Vec::new();
        let err = xmodem.receive(&child, &mut result);
        assert!(err.is_err());
        assert_eq!(err.unwrap_err().to_string(), "Exhausted retries: 2");
        Ok(())
    }

    #[test]
    fn test_xmodem_recv_with_cancel() -> Result<()> {
        let filename = tmpfilename("test_xmodem_recv_with_cancel");
        let gettysburg = GETTYSBURG.as_bytes();
        std::fs::write(&filename, gettysburg)?;
        let child = ChildUart::spawn_corrupt(
            &["sx", &filename],
            TransferState::new(&[1, 134]),
            TransferState::default(),
        )?;
        let xmodem = Xmodem {
            max_errors: 2,
            pad_byte: 0,
            block_len: XmodemBlock::Block128,
        };
        let mut result = Vec::new();
        let err = xmodem.receive(&child, &mut result);
        assert!(err.is_err());
        assert_eq!(err.unwrap_err().to_string(), "Cancelled");
        Ok(())
    }
}
