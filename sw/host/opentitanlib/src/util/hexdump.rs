// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use regex::RegexBuilder;
use std::io::Write;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum HexdumpError {
    #[error("odd number of input characters")]
    BadLength,
    #[error("unrecognized hexdump format")]
    UnrecognizedFormat,
}

/// Print a hexdump of a buffer to `writer`.
/// The hexdump includes the offset, hex bytes and printable ASCII characters.
///
///  00000000: 53 46 44 50 06 01 02 ff 00 06 01 10 30 00 00 ff  SFDP........0...
///  00000010: c2 00 01 04 10 01 00 ff 84 00 01 02 c0 00 00 ff  ................
///  00000020: ff ff ff ff ff ff ff ff ff ff ff ff ff ff ff ff  ................
///  00000030: e5 20 fb ff ff ff ff 3f 44 eb 08 6b 08 3b 04 bb  . .....?D..k.;..
///
/// Note: This format can be consumed by `xxd -r` and converted back into binary.
pub fn hexdump(mut writer: impl Write, buf: &[u8]) -> Result<()> {
    for (i, chunk) in buf.chunks(16).enumerate() {
        let mut ascii = [b'.'; 16];
        write!(writer, "{:08x}:", i * 16)?;
        for (j, byte) in chunk.iter().copied().enumerate() {
            write!(writer, " {:02x}", byte)?;
            // For printable ASCII chars, place them in the ascii buffer.
            if byte == b' ' || byte.is_ascii_graphic() {
                ascii[j] = byte;
            }
        }
        // Align and print the ascii buffer.
        let j = chunk.len();
        for _ in 0..(16 - j) {
            write!(writer, "   ")?;
        }
        writeln!(writer, "  {}", std::str::from_utf8(&ascii[0..j]).unwrap())?;
    }
    Ok(())
}

/// Print a hexdump of a buffer to a string.
pub fn hexdump_string(buf: &[u8]) -> Result<String> {
    let mut s = Vec::new();
    hexdump(&mut s, buf)?;
    Ok(String::from_utf8(s)?)
}

// Translate an ASCII byte into its hex numerical value.
fn unhex(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        _ => None,
    }
}

// Given a hex string, parse hex bytes and append them to `vec`.
fn from_hex(text: &str, vec: &mut Vec<u8>) -> Result<()> {
    let mut it = text.bytes().filter_map(unhex);
    while let Some(a) = it.next() {
        if let Some(b) = it.next() {
            vec.push(a << 4 | b);
        } else {
            return Err(HexdumpError::BadLength.into());
        }
    }
    Ok(())
}

/// Parses a hexdump string in a variety of forms, returning the resulting bytes.
pub fn hexdump_parse(text: &str) -> Result<Vec<u8>> {
    // Detects `xxd -g<n>` formats.
    let xxd = RegexBuilder::new(r"^[[:xdigit:]]{8}:\s+((?:[[:xdigit:]]{2,}\s)+)\s+.{1,16}$")
        .multi_line(true)
        .build()
        .unwrap();
    // Detects `hexdump -vC`
    let hexdump =
        RegexBuilder::new(r"^[[:xdigit:]]{8}\s+((?:[[:xdigit:]]{2}\s+?){1,16})\s+\|.*\|$")
            .multi_line(true)
            .build()
            .unwrap();
    // Detects a simple hex string with optional whitespace.
    let hexstr = RegexBuilder::new(r"(?:0[xX])?((?:[[:xdigit:]]{2}\s*)+)")
        .multi_line(false)
        .build()
        .unwrap();

    let mut res = Vec::new();
    let captures = if xxd.is_match(text) {
        xxd.captures_iter(text)
    } else if hexdump.is_match(text) {
        hexdump.captures_iter(text)
    } else if hexstr.is_match(text) {
        hexstr.captures_iter(text)
    } else {
        return Err(HexdumpError::UnrecognizedFormat.into());
    };
    for c in captures {
        from_hex(c.get(1).unwrap().as_str(), &mut res)?;
    }
    Ok(res)
}

#[cfg(test)]
mod tests {
    use super::*;
    use anyhow::Result;

    const TEST_STR: &str = "The quick brown fox jumped over the lazy dog!";

    // Output from `hexdump -vC ...`
    const HEXDUMP_C: &str = "\
00000000  54 68 65 20 71 75 69 63  6b 20 62 72 6f 77 6e 20  |The quick brown |\n\
00000010  66 6f 78 20 6a 75 6d 70  65 64 20 6f 76 65 72 20  |fox jumped over |\n\
00000020  74 68 65 20 6c 61 7a 79  20 64 6f 67 21           |the lazy dog!|\n";

    // Output from `xxd -g<n> ...` where n = {1,2,4,8}
    const XXD_G1: &str = "\
00000000: 54 68 65 20 71 75 69 63 6b 20 62 72 6f 77 6e 20  The quick brown \n\
00000010: 66 6f 78 20 6a 75 6d 70 65 64 20 6f 76 65 72 20  fox jumped over \n\
00000020: 74 68 65 20 6c 61 7a 79 20 64 6f 67 21           the lazy dog!\n";

    const XXD_G2: &str = "\
00000000: 5468 6520 7175 6963 6b20 6272 6f77 6e20  The quick brown \n\
00000010: 666f 7820 6a75 6d70 6564 206f 7665 7220  fox jumped over \n\
00000020: 7468 6520 6c61 7a79 2064 6f67 21         the lazy dog!\n";

    const XXD_G4: &str = "\
00000000: 54686520 71756963 6b206272 6f776e20  The quick brown \n\
00000010: 666f7820 6a756d70 6564206f 76657220  fox jumped over \n\
00000020: 74686520 6c617a79 20646f67 21        the lazy dog!\n";

    const XXD_G8: &str = "\
00000000: 5468652071756963 6b2062726f776e20  The quick brown \n\
00000010: 666f78206a756d70 6564206f76657220  fox jumped over \n\
00000020: 746865206c617a79 20646f6721        the lazy dog!\n";

    const XXD: [&str; 4] = [XXD_G1, XXD_G2, XXD_G4, XXD_G8];

    #[test]
    fn test_hexdump() -> Result<()> {
        let buf = TEST_STR;
        let res = hexdump_string(buf.as_bytes())?;
        assert_eq!(res, XXD_G1);
        Ok(())
    }

    #[test]
    fn test_from_hexstr() -> Result<()> {
        let buf = "5468652071756963\n6b2062726f776e20";
        let res = hexdump_parse(buf)?;
        let s = std::str::from_utf8(&res)?;
        assert_eq!(s, "The quick brown ");
        Ok(())
    }

    #[test]
    fn test_from_hexdump() -> Result<()> {
        let res = hexdump_parse(HEXDUMP_C)?;
        let s = std::str::from_utf8(&res)?;
        assert_eq!(s, TEST_STR);
        Ok(())
    }

    #[test]
    fn test_from_xxd() -> Result<()> {
        for xxd in &XXD {
            let res = hexdump_parse(xxd)?;
            let s = std::str::from_utf8(&res)?;
            assert_eq!(s, TEST_STR);
        }
        Ok(())
    }
}
