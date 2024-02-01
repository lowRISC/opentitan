// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// These test cases are nearly identical to those in
// `//sw/host/opentitanlib/src/bootstrap/xmodem.rs`.  In fact, the test cases
// check the same conditions as those in the aforementioned module.  The
// differencees are:
// - This module tests against the C implementation of xmodem used in firmware.
// - The error codes herein refer to the errors returned by the C implementation.
//
// The xmodem tests depend on the lrzsz package which contains the classic
// XMODEM/YMODEM/ZMODEM file transfer programs dating back to the 1980s and
// 1990s.
#[cfg(test)]
mod test {
    //use opentitanlib::io::uart::Uart;
    use anyhow::Result;
    //use std::io::{Read, Write};
    use opentitanlib::util::testing::{ChildUart, TransferState};
    use opentitanlib::util::tmpfilename;
    use xmodem::XmodemFirmware;

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
        let _ = TransferState::default();
        let filename = tmpfilename("test_xmodem_send");
        let child = ChildUart::spawn(&["rx", "--with-crc", &filename])?;
        let xmodem = XmodemFirmware::new();
        let gettysburg = GETTYSBURG.as_bytes();
        xmodem.send(&child, gettysburg)?;
        assert!(child.wait()?.success());
        let result = std::fs::read(&filename)?;
        // The file should be a multiple of the block size.
        assert_eq!(result.len() % 128, 0);
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
            TransferState::new(&[3, 1032]),
        )?;
        let xmodem = XmodemFirmware::new();
        let gettysburg = GETTYSBURG.as_bytes();
        let err = xmodem.send(&child, gettysburg);
        assert!(err.is_err());
        assert_eq!(err.unwrap_err().to_string(), "TooManyErrors");
        Ok(())
    }

    #[test]
    fn test_xmodem_checksum_mode() -> Result<()> {
        let filename = tmpfilename("test_xmodem_checksum_mode");
        let child = ChildUart::spawn(&["rx", &filename])?;
        let xmodem = XmodemFirmware::new();
        let gettysburg = GETTYSBURG.as_bytes();
        let result = xmodem.send(&child, gettysburg);
        assert_eq!(child.wait()?.success(), false);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().to_string(), "Protocol");
        Ok(())
    }

    #[test]
    fn test_xmodem_recv() -> Result<()> {
        let filename = tmpfilename("test_xmodem_recv");
        let gettysburg = GETTYSBURG.as_bytes();
        std::fs::write(&filename, gettysburg)?;
        let child = ChildUart::spawn(&["sx", &filename])?;
        let xmodem = XmodemFirmware::new();
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
        let xmodem = XmodemFirmware::new();
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
            TransferState::new(&[3, 1032]),
            TransferState::default(),
        )?;
        let xmodem = XmodemFirmware { max_errors: 2 };
        let mut result = Vec::new();
        let err = xmodem.receive(&child, &mut result);
        assert!(err.is_err());
        assert_eq!(err.unwrap_err().to_string(), "Crc");
        Ok(())
    }

    #[test]
    fn test_xmodem_recv_with_cancel() -> Result<()> {
        let filename = tmpfilename("test_xmodem_recv_with_cancel");
        let gettysburg = GETTYSBURG.as_bytes();
        std::fs::write(&filename, gettysburg)?;
        let child = ChildUart::spawn_corrupt(
            &["sx", &filename],
            TransferState::new(&[1, 1030]),
            TransferState::default(),
        )?;
        let xmodem = XmodemFirmware { max_errors: 2 };
        let mut result = Vec::new();
        let err = xmodem.receive(&child, &mut result);
        assert!(err.is_err());
        assert_eq!(err.unwrap_err().to_string(), "Cancel");
        Ok(())
    }
}
