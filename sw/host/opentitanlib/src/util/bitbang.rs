// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, ensure, Result};
use std::collections::HashMap;
use std::iter::Peekable;
use std::ops::Mul;
use std::time::Duration;

use crate::io::gpio::BitbangEntry;

#[derive(Debug, Eq, PartialEq)]
enum Token<'a> {
    Numeric(&'a str),
    Alphabetic(&'a str),
    Quoted(&'a str),
}

fn get_token<'a>(
    input: &'a str,
    iter: &mut Peekable<std::str::CharIndices<'a>>,
) -> Result<Option<Token<'a>>> {
    // Skip any initial whitespace
    let (token_start, first_char) = loop {
        match iter.peek() {
            Some((_, ch)) if ch.is_whitespace() => {
                iter.next();
            }
            Some((idx, ch)) => break (*idx, *ch),
            None => return Ok(None),
        }
    };
    iter.next();
    if first_char.is_numeric() || first_char == '.' {
        let token_end = loop {
            match iter.peek() {
                Some((_, ch)) if ch.is_numeric() || *ch == '.' => {
                    iter.next();
                }
                Some((idx, _)) => break *idx,
                None => break input.len(),
            }
        };
        Ok(Some(Token::Numeric(&input[token_start..token_end])))
    } else if first_char.is_alphabetic() {
        let token_end = loop {
            match iter.peek() {
                Some((_, ch)) if ch.is_alphabetic() => {
                    iter.next();
                }
                Some((idx, _)) => break *idx,
                None => break input.len(),
            }
        };
        Ok(Some(Token::Alphabetic(&input[token_start..token_end])))
    } else if first_char == '\'' {
        let token_end = loop {
            match iter.next() {
                Some((_, '\'')) => {
                    if let Some((idx, _)) = iter.peek() {
                        break *idx;
                    } else {
                        break input.len();
                    }
                }
                Some(_) => (),
                None => bail!("Unterminated string"),
            }
        };
        Ok(Some(Token::Quoted(&input[token_start..token_end])))
    } else if first_char == '\"' {
        let token_end = loop {
            match iter.next() {
                Some((_, '\"')) => {
                    if let Some((idx, _)) = iter.peek() {
                        break *idx;
                    } else {
                        break input.len();
                    }
                }
                Some(_) => (),
                None => bail!("Unterminated string"),
            }
        };
        Ok(Some(Token::Quoted(&input[token_start..token_end])))
    } else {
        bail!("Unexpected character `{}`", first_char);
    }
}

fn get_all_tokens(input: &str) -> Result<Vec<Token>> {
    let mut char_indices = input.char_indices().peekable();
    let mut all_tokens = Vec::new();
    loop {
        let Some(token) = get_token(input, &mut char_indices)? else {
            return Ok(all_tokens);
        };
        all_tokens.push(token);
    }
}

/// This function parses a tring of the form "10 ms" or "115.2 kHz" returning the clock period as
/// a `Duration`.
pub fn parse_clock_frequency(input: &str) -> Result<Duration> {
    let all_tokens = get_all_tokens(input)?;
    let tokens: &[Token] = &all_tokens;
    match tokens {
        [Token::Numeric(num), Token::Alphabetic(time_unit)] => Ok(match *time_unit {
            "ns" => Duration::from_nanos(num.parse().unwrap()),
            "us" => Duration::from_secs_f64(num.parse::<f64>().unwrap() / 1000000.0),
            "ms" => Duration::from_secs_f64(num.parse::<f64>().unwrap() / 1000.0),
            "s" => Duration::from_secs_f64(num.parse().unwrap()),
            "Hz" => Duration::from_secs(1).div_f64(num.parse().unwrap()),
            "kHz" => Duration::from_secs(1).div_f64(num.parse::<f64>().unwrap() * 1000.0),
            "MHz" => Duration::from_secs(1).div_f64(num.parse::<f64>().unwrap() * 1000000.0),
            _ => bail!("Unknown unit: {}", time_unit),
        }),
        _ => bail!("Parse error"),
    }
}

/// This function parses the main string argument to `opentitantool gpio bit-bang`, producing a
/// list of `BitbangEntry` corresponding to the parsed instructions.  The slices in the entries
/// will refer to one of the two "accumulator vectors" provided by the caller, which this function
/// will clear out and resize according to need.
pub fn parse_sequence<'a, 'wr, 'rd>(
    input: &'a str,
    num_pins: usize,
    clock: Duration,
    accumulator_rd: &'rd mut Vec<u8>,
    accumulator_wr: &'wr mut Vec<u8>,
) -> Result<(Vec<BitbangEntry<'rd, 'wr>>, HashMap<&'a str, usize>)> {
    let all_tokens = get_all_tokens(input)?;

    let mut token_map: HashMap<&'a str, usize> = HashMap::new();

    // First pass, check how many data bytes are needed.
    let mut needed_bytes = 0usize;
    let mut last_token_was_capture = false;
    let mut tokens: &[Token] = &all_tokens;
    loop {
        match tokens {
            [Token::Numeric(_), Token::Alphabetic(_), rest @ ..] => {
                ensure!(
                    !last_token_was_capture,
                    "Capturing GPIO samples only supported immediately preceeding output, not with delay.  (Consider repeating the previous output values before the delay.)",
                );
                tokens = rest;
                last_token_was_capture = false;
            }
            [Token::Numeric(bits), rest @ ..] => {
                ensure!(
                    bits.len() % num_pins == 0,
                    "Unexpected number of bits {}, should be multiple of the number of pins {}",
                    bits.len(),
                    num_pins,
                );
                needed_bytes += bits.len() / num_pins;
                tokens = rest;
                last_token_was_capture = false;
            }
            [Token::Quoted(identifier), rest @ ..] => {
                token_map.insert(&identifier[1..identifier.len() - 1], needed_bytes);
                tokens = rest;
                last_token_was_capture = true;
            }
            [] => break,
            _ => bail!("Parse error"),
        }
    }
    accumulator_wr.clear();
    accumulator_wr.resize(needed_bytes, 0u8);
    accumulator_rd.clear();
    accumulator_rd.resize(needed_bytes, 0u8);
    let mut slice_wr: &'wr mut [u8] = accumulator_wr;
    let mut slice_rd: &'rd mut [u8] = accumulator_rd;

    // Second pass, create `BitbangEntry` instances referring to data in the accumulators.
    let mut result = Vec::new();
    let mut tokens: &[Token] = &all_tokens;
    loop {
        match tokens {
            [Token::Numeric(num), Token::Alphabetic(time_unit), rest @ ..] => {
                let ticks = if *time_unit == "ticks" {
                    num.parse::<u32>().unwrap()
                } else {
                    let duration = match *time_unit {
                        "us" => num.parse::<f64>().unwrap() / 1000000.0,
                        "ms" => num.parse::<f64>().unwrap() / 1000.0,
                        "s" => num.parse::<f64>().unwrap(),
                        unit => bail!("Unrecognized time unit: '{}'", unit),
                    };
                    let closest_ticks = (duration / clock.as_secs_f64()).round() as u32; // TODO overflow
                    let actual_duration = clock.mul(closest_ticks);
                    let _ = actual_duration; //TODO Verify precision to 1%
                    closest_ticks
                };
                ensure!(
                    ticks > 0,
                    "Zero length delay requested: {} {}",
                    num,
                    time_unit
                );
                result.push(BitbangEntry::Delay(ticks));
                tokens = rest;
            }
            [Token::Numeric(bits), rest @ ..] => {
                let samples = bits.len() / num_pins;
                let (left_wr, right_wr) = slice_wr.split_at_mut(samples);
                let (left_rd, right_rd) = slice_rd.split_at_mut(samples);

                for (sample_no, item) in left_wr.iter_mut().enumerate() {
                    for pin_no in 0..num_pins {
                        match bits.as_bytes()[sample_no * num_pins + pin_no] {
                            b'0' => (),
                            b'1' => *item |= 1 << pin_no,
                            _ => bail!("Non-binary digit encountered in '{}'", bits),
                        }
                    }
                }

                result.push(BitbangEntry::Both(left_wr, left_rd));
                slice_wr = right_wr;
                slice_rd = right_rd;
                tokens = rest;
            }
            [Token::Quoted(_), rest @ ..] => {
                tokens = rest;
            }
            [] => break,
            _ => bail!("Parse error"),
        }
    }

    Ok((result, token_map))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_all_tokens() {
        assert_eq!(
            // Simple list of tokens.
            get_all_tokens("01 14ms 11").unwrap(),
            [
                Token::Numeric("01"),
                Token::Numeric("14"),
                Token::Alphabetic("ms"),
                Token::Numeric("11"),
            ],
        );
        assert_eq!(
            // Same list with funny whitespace.
            get_all_tokens("\t01\r14\nms\x0B11\x0C").unwrap(),
            [
                Token::Numeric("01"),
                Token::Numeric("14"),
                Token::Alphabetic("ms"),
                Token::Numeric("11"),
            ],
        );
        assert_eq!(
            // Very long numerical token (used for subsequent binary values for pins.
            get_all_tokens("   0101010101010101010101010101010101010101010111   ").unwrap(),
            [Token::Numeric(
                "0101010101010101010101010101010101010101010111"
            ),],
        );
        assert_eq!(
            // Use of quoted named instants, at which input pins should be sampled.
            get_all_tokens("'s6' 17ms10's7'").unwrap(),
            [
                Token::Quoted("'s6'"),
                Token::Numeric("17"),
                Token::Alphabetic("ms"),
                Token::Numeric("10"),
                Token::Quoted("'s7'"),
            ],
        );
    }
}
