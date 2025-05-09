// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
use pem_rfc7468::{BASE64_WRAP_WIDTH, LineEnding};

/// Cleans PEM-like byte slices for parsing, attempting to handle non-standard formats.
///
/// This function is primarily designed as a recovery step when input PEM bytes have
/// already failed to be parsed by a standard PEM library.
///
/// Some signing tools or commands may generate custom header fields after the
/// '-----BEGIN ...-----' marker but before the actual Base64 encoded payload.
/// For example:
/// -----BEGIN AUTH SIGNATURE-----
/// ALGORITHM: ES256
///
/// [BASE64 PAYLOAD LINE 1]
/// [BASE64 PAYLOAD LINE 2]
/// -----END AUTH SIGNATURE-----
///
/// Such custom fields (like "ALGORITHM: ES256" and the subsequent blank line)
/// do not strictly adhere to PEM specifications like RFC 7468 for the text encoding
/// of the payload itself (which expects the Base64 block to follow.)
///
/// This function attempts to strip these non-standard intermediate lines and retain
/// only the BEGIN/END markers and the core Base64 payload.
///
/// Assumptions made by this function:
/// 1. The very first line of the `pem_bytes` input MUST be the '-----BEGIN ...-----' marker.
///    This line is always preserved.
/// 2. A line that is part of the actual Base64 payload is expected to have a length
///    equal to `pem_rfc7468::BASE64_WRAP_WIDTH`. This is used as a primary trigger
///    to identify the start of the payload.
/// 3. Any custom lines that appear between the '-----BEGIN ...-----' marker
///    and the Base64 payload are assumed NOT to have a length equal to
///    `pem_rfc7468::BASE64_WRAP_WIDTH`. Such lines will be discarded.
///
pub fn clean_pem_bytes_for_parsing(pem_bytes: &[u8]) -> Result<Vec<u8>, pem_rfc7468::Error> {
    let pem_content_str = std::str::from_utf8(pem_bytes)?;
    let mut lines_iter = pem_content_str.lines();
    let mut output_bytes: Vec<u8> = Vec::new();
    if let Some(begin_line_str) = lines_iter.next() {
        output_bytes.extend_from_slice(begin_line_str.as_bytes());
        output_bytes.extend_from_slice(LineEnding::default().as_bytes());
    } else {
        return Err(pem_rfc7468::Error::EncapsulatedText);
    }

    let mut processing_base64_payload = false;

    for line_str in lines_iter {
        if !processing_base64_payload && line_str.len() == BASE64_WRAP_WIDTH {
            processing_base64_payload = true;
        }
        if processing_base64_payload {
            output_bytes.extend_from_slice(line_str.as_bytes());
            output_bytes.extend_from_slice(LineEnding::default().as_bytes());
        }
    }
    Ok(output_bytes)
}
