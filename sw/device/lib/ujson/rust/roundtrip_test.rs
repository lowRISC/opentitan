// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use opentitanlib::test_utils::status::Status;
use std::io::{Read, Write};
use std::process::{Command, Stdio};

mod example {
    // Bring in the auto-generated sources.
    include!(env!("example"));
}

fn roundtrip(name: &str, data: &str) -> Result<String> {
    let mut command = Command::new(&std::env::var("ROUNDTRIP_CLIENT")?);
    command.args(&[name]);
    let mut child = command
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .spawn()?;

    let mut stdin = child.stdin.take().unwrap();
    eprintln!("sent: {}", data);
    stdin.write_all(data.as_bytes())?;

    let mut s = String::new();
    let mut stdout = child.stdout.take().unwrap();
    stdout.read_to_string(&mut s)?;
    eprintln!("recv: {}", s);
    Ok(s)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_foo() -> Result<()> {
        let before = example::Foo {
            foo: 5,
            bar: 10,
            message: "Hello".into(),
        };
        let after = roundtrip("foo", &serde_json::to_string_pretty(&before)?)?;
        let after = serde_json::from_str::<example::Foo>(&after)?;
        assert_eq!(before, after);
        Ok(())
    }

    #[test]
    fn test_rect() -> Result<()> {
        let before = example::Rect {
            top_left: example::Coord { x: 10, y: 20 },
            bottom_right: example::Coord { x: 30, y: 40 },
        };
        let after = roundtrip("rect", &serde_json::to_string(&before)?)?;
        let after = serde_json::from_str::<example::Rect>(&after)?;
        assert_eq!(before, after);
        Ok(())
    }

    #[test]
    fn test_matrix() -> Result<()> {
        let before = example::Matrix {
            k: [
                [0, 1, 2, 3, 4],
                [100, 200, 300, 400, 500],
                [-1, -2, -3, -4, -5],
            ],
        };
        let after = roundtrip("matrix", &serde_json::to_string(&before)?)?;
        let after = serde_json::from_str::<example::Matrix>(&after)?;
        assert_eq!(before, after);
        Ok(())
    }

    #[test]
    fn test_direction() -> Result<()> {
        let before = example::Direction::North;
        let after = roundtrip("direction", &serde_json::to_string(&before)?)?;
        let after = serde_json::from_str::<example::Direction>(&after)?;
        assert_eq!(before, after);
        Ok(())
    }

    #[test]
    fn test_direction_intvalue() -> Result<()> {
        let before = example::Direction::IntValue(45);
        let after = roundtrip("direction", &serde_json::to_string(&before)?)?;
        let after = serde_json::from_str::<example::Direction>(&after)?;
        assert_eq!(before, after);
        Ok(())
    }

    #[test]
    fn test_misc() -> Result<()> {
        let before = example::Misc {
            value: true,
            status: Status::InvalidArgument("FOO".into(), 5),
        };
        let after = roundtrip("misc", &serde_json::to_string(&before)?)?;
        let after = serde_json::from_str::<example::Misc>(&after)?;
        assert_eq!(before, after);
        Ok(())
    }
}
