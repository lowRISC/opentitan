// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use prost::Message;

use std::io::Read;

use spawn_proto::protos::SpawnExec;

// The size delimiter is encoded in LEB128.
const DELIMITER_SIZE_MAX: usize = 10;

pub fn read_spawn_exec<T: Read>(
    reader: &mut T,
    msg: &mut SpawnExec,
    buf: &mut Vec<u8>,
) -> Result<bool> {
    // Read delimiter.
    buf.resize(DELIMITER_SIZE_MAX, 0);
    match reader.read_exact(&mut buf[..]) {
        Ok(()) => (),
        Err(err) if err.kind() == std::io::ErrorKind::UnexpectedEof => return Ok(false),
        Err(err) => bail!(err),
    }
    // Read delimiter.
    let mut cursor = std::io::Cursor::new(&buf);
    let size = prost::decode_length_delimiter(&mut cursor)?;
    let delim_size = cursor.position() as usize;
    // Read more data if necessary (we don't handle the case where the
    // delimiter + message data is smaller than 10 bytes since it is never
    // the case and makes the code more complicated.
    assert!(buf.len() <= delim_size + size);
    buf.resize(delim_size + size, 0);
    reader.read_exact(&mut buf[DELIMITER_SIZE_MAX..])?;
    msg.clear();
    SpawnExec::merge(msg, &buf[delim_size..])?;
    Ok(true)
}
