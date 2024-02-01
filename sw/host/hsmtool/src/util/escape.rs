// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum EscapeError {
    #[error("Incomplete escape sequence")]
    IncompleteEscape,
    #[error("Invalid character in escape sequence")]
    InvalidCharacter(char),
    #[error("Invalid character in hex escape sequence")]
    InvalidHexCharacter(char),
}

const HEX: &[u8; 16] = b"0123456789ABCDEF";

pub fn escape(val: &[u8]) -> String {
    let mut data = String::new();
    for ch in val {
        match ch {
            b'\t' => data.push_str("\\t"),
            b'\r' => data.push_str("\\r"),
            b'\n' => data.push_str("\\n"),
            b'\'' => data.push_str("\\'"),
            b'\"' => data.push_str("\\\""),
            b'\\' => data.push_str("\\\\"),
            0x20..=0x7e => data.push(*ch as char),
            _ => {
                data.push_str("\\x");
                data.push(HEX[(ch >> 4) as usize] as char);
                data.push(HEX[(ch & 15) as usize] as char);
            }
        }
    }
    data
}

pub fn unhex(ch: char) -> Result<u8> {
    match ch {
        '0'..='9' => Ok(ch as u8 - b'0'),
        'A'..='F' => Ok(ch as u8 - b'A' + 10),
        'a'..='f' => Ok(ch as u8 - b'a' + 10),
        _ => Err(EscapeError::InvalidHexCharacter(ch).into()),
    }
}

pub fn unescape(val: &str) -> Result<Vec<u8>> {
    let mut data = Vec::new();
    let mut it = val.chars();
    while let Some(ch) = it.next() {
        if !ch.is_ascii() {
            return Err(EscapeError::InvalidCharacter(ch).into());
        }
        if ch == '\\' {
            let ch = it.next().ok_or(EscapeError::IncompleteEscape)?;
            let decoded = match ch {
                't' => b'\t',
                'r' => b'\r',
                'n' => b'\n',
                '"' => b'\"',
                '\'' => b'\'',
                '\\' => b'\\',
                'x' => {
                    let mut v = 0;
                    v = (v << 4) | unhex(it.next().ok_or(EscapeError::IncompleteEscape)?)?;
                    v = (v << 4) | unhex(it.next().ok_or(EscapeError::IncompleteEscape)?)?;
                    v
                }
                _ => return Err(EscapeError::InvalidCharacter(ch).into()),
            };
            data.push(decoded);
        } else {
            data.push(ch as u8);
        }
    }
    Ok(data)
}

pub fn as_hex(v: &[u8]) -> String {
    let mut s = String::with_capacity(v.len() * 3);
    for (i, &byte) in v.iter().enumerate() {
        if i > 0 {
            s.push(':');
        }
        s.push(HEX[(byte >> 4) as usize] as char);
        s.push(HEX[(byte & 15) as usize] as char);
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_escape() -> Result<()> {
        let bytes = b"The quick brown fox\n\tjumped over the \"lazy\" dog.";
        assert_eq!(
            escape(bytes),
            r#"The quick brown fox\n\tjumped over the \"lazy\" dog."#
        );

        let bytes = b"\t\r\n\"\'\\\x00\x7F\xFF";
        assert_eq!(escape(bytes), r#"\t\r\n\"\'\\\x00\x7F\xFF"#);
        Ok(())
    }

    #[test]
    fn test_unescape() -> Result<()> {
        let s = r#"The quick brown fox\n\tjumped over the \"lazy\" dog."#;
        assert_eq!(
            unescape(s)?,
            b"The quick brown fox\n\tjumped over the \"lazy\" dog."
        );

        let s = r#"\t\r\n\"\'\\\x00\x7F\xFF"#;
        assert_eq!(unescape(s)?, b"\t\r\n\"\'\\\x00\x7F\xFF");
        Ok(())
    }

    #[test]
    fn test_unescape_err() -> Result<()> {
        let pounds = "\u{00A3}";
        assert!(unescape(pounds).is_err());

        let invalid_escape = "\\z";
        assert!(unescape(invalid_escape).is_err());

        let incomplete_escape = "\\";
        assert!(unescape(incomplete_escape).is_err());

        let bad_hex = "\\xzz";
        assert!(unescape(bad_hex).is_err());
        Ok(())
    }
}
