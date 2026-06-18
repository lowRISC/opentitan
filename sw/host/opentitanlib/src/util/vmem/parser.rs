// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! Parsing of Verilog VMEM files into the [`Vmem`] representation.
//!
//! See the [srec_vmem] documentation for a description of the file format.
//!
//! To summarise:
//! * Files specify hexadecimal data for sequential addresses.
//! * Start addresses for a run can be specified in hex with '@____'.
//! * Address and data values are separated by whitespace or comments.
//! * C-style '//' and '/* */' comments are supported.
//!
//! [srec_vmem]: https://srecord.sourceforge.net/man/man5/srec_vmem.5.html

use std::num::ParseIntError;

use thiserror::Error;

use super::{Section, Vmem, Word};

pub type ParseResult<T> = Result<T, ParseError>;

/// Errors that can occur when parsing VMEM files.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ParseError {
    /// Failure to parse an integer from hexadecimal.
    #[error("failed to parse as hexadecimal integer")]
    DecodeHexAddr(#[from] ParseIntError),

    #[error("failed to parse as hexadecimal integer")]
    DecodeHexValue(String),

    /// An opened comment was not closed.
    #[error("unclosed comment")]
    UnclosedComment,

    /// An address was started with an '@' character, but no address value followed.
    #[error("address is missing a value")]
    AddrMissingValue,

    /// Catch-all for any characters that don't belong in VMEM files.
    #[error("unknown character '{0}'")]
    UnknownChar(char),
}

impl From<hex::FromHexError> for ParseError {
    // hex::FromHexError does not support PartialEq/Eq, so convert the error to a String.
    fn from(err: hex::FromHexError) -> Self {
        Self::DecodeHexValue(err.to_string())
    }
}

/// Representation of the possible tokens found in VMEM files.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Token {
    /// End of file.
    Eof,
    /// Address directive, e.g. `@123abc`.
    Addr(u32),
    /// Data value, e.g. `abc123`.
    Value(Vec<u8>),
    /// Comments, e.g. `/* comment */` or `// comment`.
    Comment,
    /// Whitespace, including newlines.
    Whitespace,
}

/// Some span of the input text representing a token.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Span {
    token: Token,
    len: usize,
}

/// Parser for VMEM files.
pub struct VmemParser;

impl VmemParser {
    /// Parse a complete VMEM file from a string.
    pub fn parse(mut s: &str, addr_stride: Option<usize>) -> ParseResult<Vmem> {
        // Build up the vmem file as sections.
        let mut vmem = Vmem::default();
        vmem.sections.push(Section::default());

        loop {
            // Parse a token from the input string, and move along by its span.
            let Span { len, token } = Self::token(s)?;
            s = &s[len..];

            match token {
                Token::Eof => break,
                Token::Addr(addr) => {
                    // Add a new section to the `Vmem` at this address.
                    // Here we translate between a "word index" to a byte address.
                    if addr != 0 || vmem.sections.last().unwrap().addr != 0 {
                        vmem.sections.push(Section {
                            addr: addr * addr_stride.unwrap_or(1) as u32,
                            data: Vec::new(),
                        });
                    }
                }
                Token::Value(value) => {
                    // Add the value to the current (last added) section's data.
                    let section = vmem.sections.last_mut().unwrap();
                    section.data.push(Word::new(value))
                }
                // Whitespace and comments are ignored.
                Token::Whitespace => continue,
                Token::Comment => continue,
            }
        }

        Ok(vmem)
    }

    /// Parse a single token from the beginning of a string.
    fn token(s: &str) -> ParseResult<Span> {
        let parsers = [
            Self::parse_eof,
            Self::parse_addr,
            Self::parse_value,
            Self::parse_comment,
            Self::parse_whitespace,
        ];

        // Run each parser in order, stopping when one gets a matching parse.
        let span = parsers.iter().find_map(|p| p(s).transpose());

        // If no parsers succeeded, return an error.
        match span {
            Some(span) => span,
            None => Err(ParseError::UnknownChar(s.chars().next().unwrap())),
        }
    }

    /// Try to parse an EOF from the beginning of a string.
    fn parse_eof(s: &str) -> ParseResult<Option<Span>> {
        // Empty strings give a 0-length `Token::Eof` span.
        match s.is_empty() {
            true => Ok(Some(Span {
                len: 0,
                token: Token::Eof,
            })),
            false => Ok(None),
        }
    }

    /// Try to parse an address from the beginning of a string.
    fn parse_addr(s: &str) -> ParseResult<Option<Span>> {
        // Check for the beginning '@' symbol.
        let Some(addr) = s.strip_prefix('@') else {
            return Ok(None);
        };

        // Find the length of the actual address string.
        let addr_len = match addr.find(|c: char| !c.is_ascii_hexdigit()) {
            Some(0) => return Err(ParseError::AddrMissingValue),
            Some(len) => len,
            None => addr.len(),
        };
        // Ensure the '@' is included in the span's length!
        let len = '@'.len_utf8() + addr_len;

        // Parse from hexadecimal.
        let val = u32::from_str_radix(&addr[..addr_len], 16)?;
        let token = Token::Addr(val);
        let span = Span { token, len };

        Ok(Some(span))
    }

    /// Try parse a value from the beginning of a string.
    fn parse_value(s: &str) -> ParseResult<Option<Span>> {
        // Check for hexadecimal characters in the input.
        let len = match s.find(|c: char| !c.is_ascii_hexdigit()) {
            Some(0) => return Ok(None),
            Some(len) => len,
            None => s.len(),
        };
        let s = if len % 2 == 1 {
            format!("0{s}")
        } else {
            s.to_string()
        };

        let val = hex::decode(&s[..len.div_ceil(2) * 2])?;
        let token = Token::Value(val);
        let span = Span { token, len };

        Ok(Some(span))
    }

    /// Try parse a comment from the beginning of a string.
    fn parse_comment(s: &str) -> ParseResult<Option<Span>> {
        // Look for commend identifiers and their closers.
        let len = match s {
            s if s.starts_with("//") => s.find('\n').unwrap_or(s.len()),
            s if s.starts_with("/*") => {
                // `find` gives us the _start_ of the `*/`, so include its length as well.
                s.find("*/").ok_or(ParseError::UnclosedComment)? + "*/".len()
            }
            _ => return Ok(None),
        };

        let token = Token::Comment;
        let span = Span { token, len };

        Ok(Some(span))
    }

    /// Try to parse whitespace from the beginning of a string.
    fn parse_whitespace(s: &str) -> ParseResult<Option<Span>> {
        // Check for whitespace at the beginning of the input.
        let len = match s.find(|c: char| !c.is_whitespace()) {
            Some(0) => return Ok(None),
            Some(len) => len,
            None => s.len(),
        };

        let token = Token::Whitespace;
        let span = Span { len, token };

        Ok(Some(span))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn parse() {
        let input = r#"
            AB
            // comment
            CD EF
            @42
            12 /* comment */ 34
        "#;
        let expected = Vmem {
            sections: vec![
                Section {
                    addr: 0x00,
                    data: [0xAB, 0xCD, 0xEF]
                        .iter()
                        .map(|&b| Word::new(vec![b]))
                        .collect(),
                },
                Section {
                    addr: 0x108,
                    data: [0x12, 0x34].iter().map(|&b| Word::new(vec![b])).collect(),
                },
            ],
        };

        assert_eq!(VmemParser::parse(input, Some(4)).unwrap(), expected);
    }

    #[test]
    fn token() {
        // Check we can pick out the correct token from a string:
        let expected = [
            ("", Token::Eof, 0),
            ("@ff", Token::Addr(0xff), 3),
            ("12345678", Token::Value(vec![0x12, 0x34, 0x56, 0x78]), 8),
            ("// X", Token::Comment, 4),
            ("/* X */", Token::Comment, 7),
            (" 	", Token::Whitespace, 2),
        ];

        for (s, token, len) in expected {
            let span = Span { token, len };
            assert_eq!(VmemParser::token(s), Ok(span));
        }

        // Unknown non-token:
        assert_eq!(VmemParser::token("X"), Err(ParseError::UnknownChar('X')));
    }

    #[test]
    fn eof() {
        // Not EOF:
        assert_eq!(VmemParser::parse_eof(" ").unwrap(), None);

        // EOF:
        let expected = Some(Span {
            len: 0,
            token: Token::Eof,
        });
        assert_eq!(VmemParser::parse_eof("").unwrap(), expected);
    }

    #[test]
    fn addr() {
        // No address:
        assert_eq!(VmemParser::parse_addr("/* X */").unwrap(), None);

        let expected = Some(Span {
            len: 9,
            token: Token::Addr(0x0123abcd),
        });
        // Partially an address:
        assert_eq!(VmemParser::parse_addr("@0123ABCD FF").unwrap(), expected);
        // Entirely an address:
        assert_eq!(VmemParser::parse_addr("@0123ABCD").unwrap(), expected);
        // Lower-case hex characters:
        assert_eq!(VmemParser::parse_addr("@0123abcd").unwrap(), expected);

        // u32 overflow:
        assert!(VmemParser::parse_addr("@123456789").is_err());
        // Missing address after '@':
        assert!(VmemParser::parse_addr("@").is_err());
        assert!(VmemParser::parse_addr("@ FF").is_err());
    }

    #[test]
    fn value() {
        // No value:
        assert_eq!(VmemParser::parse_value("/* X */").unwrap(), None);

        let expected = Some(Span {
            len: 8,
            token: Token::Value(vec![0x01, 0x23, 0xab, 0xcd]),
        });
        // Partially a value:
        assert_eq!(VmemParser::parse_value("0123ABCD FF").unwrap(), expected);
        // Entirely a value:
        assert_eq!(VmemParser::parse_value("0123ABCD").unwrap(), expected);
        // Lower-case hex characters:
        assert_eq!(VmemParser::parse_value("0123abcd").unwrap(), expected);
    }

    #[test]
    fn comment() {
        // No whitespace:
        assert_eq!(VmemParser::parse_comment("FF").unwrap(), None);

        let expected = Some(Span {
            len: 7,
            token: Token::Comment,
        });

        // Partial block comment:
        assert_eq!(VmemParser::parse_comment("/* X */ FF").unwrap(), expected);
        // Entirely a block comment:
        assert_eq!(VmemParser::parse_comment("/* X */").unwrap(), expected);
        // Unclosed block comment:
        assert!(VmemParser::parse_comment("/* X").is_err());

        // Line comment ending in newline:
        assert_eq!(
            VmemParser::parse_comment(concat!("// XXXX", '\n', "FF")).unwrap(),
            expected
        );
        // Line comment ending at EOF:
        assert_eq!(VmemParser::parse_comment("// XXXX").unwrap(), expected);
    }

    #[test]
    fn whitespace() {
        // No whitespace:
        assert_eq!(VmemParser::parse_whitespace("FF").unwrap(), None);

        let expected = Some(Span {
            len: 2,
            token: Token::Whitespace,
        });
        // Partial whitespace:
        assert_eq!(VmemParser::parse_whitespace(" 	FF").unwrap(), expected);
        // Entirely whitespace:
        assert_eq!(VmemParser::parse_whitespace(" 	").unwrap(), expected);
    }
}
