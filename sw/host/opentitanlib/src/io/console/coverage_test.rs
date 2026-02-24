// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#[cfg(test)]
mod tests {
    use std::collections::VecDeque;
    use std::fs;
    use std::sync::Mutex;
    use std::task::{Context, Poll};
    use std::time::Duration;

    use crate::io::console::ext::ConsoleExt;
    use anyhow::Result;
    use tempfile::tempdir;

    use crate::io::console::ConsoleDevice;
    use crate::io::console::coverage::CoverageMiddleware;

    struct MockConsole {
        data: Mutex<VecDeque<u8>>,
        /// Number of times to return Pending before returning data.
        pending_count: Mutex<usize>,
    }

    impl ConsoleDevice for MockConsole {
        fn poll_read(&self, cx: &mut Context<'_>, _buf: &mut [u8]) -> Poll<Result<usize>> {
            let mut p_count = self.pending_count.lock().unwrap();
            if *p_count > 0 {
                *p_count -= 1;
                // Wake up immediately to continue polling.
                cx.waker().wake_by_ref();
                return Poll::Pending;
            }

            let mut data = self.data.lock().unwrap();
            if data.is_empty() {
                return Poll::Ready(Ok(0));
            }
            // Return only one byte at a time to test state machine transitions more thoroughly.
            _buf[0] = data.pop_front().unwrap();
            Poll::Ready(Ok(1))
        }

        fn write(&self, _buf: &[u8]) -> Result<()> {
            Ok(())
        }
    }

    fn create_coverage_block(content: &[u8]) -> Vec<u8> {
        let mut block = Vec::new();
        block.extend(b"== COVERAGE PROFILE START ==\r\n");
        let hex_data = hex::encode(content);
        let crc = crc::Crc::<u32>::new(&crc::CRC_32_ISO_HDLC).checksum(content);
        let hex_crc = hex::encode(crc.to_le_bytes());
        block.extend(hex_data.as_bytes());
        block.extend(hex_crc.as_bytes());
        block.extend(b"== COVERAGE PROFILE END ==\r\n");
        block
    }

    #[test]
    fn test_coverage_full_flow() -> Result<()> {
        let mut data = VecDeque::new();
        data.extend(b"Start of stream\n");
        data.extend(create_coverage_block(b"first block data"));
        data.extend(b"Between blocks\n");
        data.extend(b"== COVERAGE PROFILE SKIP ==\r\n"); // Standalone SKIP
        data.extend(b"After standalone skip\n");
        data.extend(b"== COVERAGE PROFILE START ==\r\n");
        data.extend(b"DEADBEEF"); // Incomplete/garbage hex but shouldn't crash
        data.extend(b"== COVERAGE PROFILE SKIP ==\r\n"); // SKIP inside coverage mode
        data.extend(b"After inner skip\n");
        data.extend(create_coverage_block(b"second block data"));
        data.extend(b"End of stream\n");

        let mock = MockConsole {
            data: Mutex::new(data),
            pending_count: Mutex::new(3), // Test initial pending
        };
        let tmp_dir = tempdir()?;
        let profraw_path = tmp_dir.path().join("full_flow.%p.profraw");

        let device =
            CoverageMiddleware::new_with_template(mock, profraw_path.to_str().unwrap().to_owned());

        let mut output = Vec::new();
        let mut buf = [0u8; 1024];

        crate::util::runtime::block_on(async {
            loop {
                let res = std::future::poll_fn(|cx| device.poll_read(cx, &mut buf)).await;
                match res {
                    Ok(0) => break,
                    Ok(len) => output.extend(&buf[..len]),
                    Err(e) => return Err(e),
                }
            }
            Ok(())
        })?;

        let expected_output = concat!(
            "Start of stream\n",
            "Between blocks\n",
            "After standalone skip\n",
            "After inner skip\n",
            "End of stream\n"
        );
        assert_eq!(String::from_utf8_lossy(&output), expected_output);

        // Verify two coverage files were created.
        let mut files: Vec<_> = fs::read_dir(tmp_dir.path())?
            .filter_map(|e| e.ok())
            .map(|e| e.path())
            .filter(|p| {
                p.file_name()
                    .is_some_and(|n| n.to_string_lossy().starts_with("full_flow."))
                    && p.extension().is_some_and(|ext| ext == "xprofraw")
            })
            .collect();
        files.sort();

        assert_eq!(files.len(), 2);

        let content1 = fs::read(&files[0])?;
        let content2 = fs::read(&files[1])?;

        // One should be "first block data", another "second block data".
        // Since %p is random, we check both.
        let mut contents = vec![content1, content2];
        contents.sort();

        let mut expected_contents =
            vec![b"first block data".to_vec(), b"second block data".to_vec()];
        expected_contents.sort();

        assert_eq!(contents, expected_contents);

        Ok(())
    }

    #[test]
    fn test_coverage_corrupted_crc() -> Result<()> {
        let mut data = VecDeque::new();
        data.extend(b"== COVERAGE PROFILE START ==\r\n");
        data.extend(hex::encode(b"good data").as_bytes());
        data.extend(b"00000000"); // Bad CRC
        data.extend(b"== COVERAGE PROFILE END ==\r\n");

        let mock = MockConsole {
            data: Mutex::new(data),
            pending_count: Mutex::new(0),
        };
        let tmp_dir = tempdir()?;
        let profraw_path = tmp_dir.path().join("corrupted.%p.profraw");

        let mut buf = [0u8; 1024];
        let device =
            CoverageMiddleware::new_with_template(mock, profraw_path.to_str().unwrap().to_owned());
        crate::util::runtime::block_on(async {
            loop {
                let res = std::future::poll_fn(|cx| device.poll_read(cx, &mut buf)).await;
                match res {
                    Ok(0) => break,
                    Ok(_) => {}
                    Err(e) => return Err(e),
                }
            }
            Ok(())
        })?;

        // No xprofraw file should be created because of CRC failure.
        let files_count = fs::read_dir(tmp_dir.path())?
            .filter_map(|e| e.ok())
            .filter(|e| {
                e.path()
                    .file_name()
                    .is_some_and(|n| n.to_string_lossy().starts_with("corrupted."))
                    && e.path().extension().is_some_and(|ext| ext == "xprofraw")
            })
            .count();
        assert_eq!(files_count, 0);

        Ok(())
    }

    #[test]
    fn test_coverage_invalid_hex() -> Result<()> {
        let mut data = VecDeque::new();
        data.extend(b"Normal text\n");
        data.extend(b"== COVERAGE PROFILE START ==\r\n");
        data.extend(b"ABCDEF"); // Valid hex
        data.extend(b"X"); // Invalid hex! Should exit coverage mode
        data.extend(b"GHIJKL"); // This will be treated as normal text
        data.extend(b"== COVERAGE PROFILE END ==\r\n"); // This will be unexpected end warning

        let mock = MockConsole {
            data: Mutex::new(data),
            pending_count: Mutex::new(0),
        };
        let tmp_dir = tempdir()?;
        let profraw_path = tmp_dir.path().join("invalid.%p.profraw");

        let mut output = Vec::new();
        let mut buf = [0u8; 1024];
        let device =
            CoverageMiddleware::new_with_template(mock, profraw_path.to_str().unwrap().to_owned());
        crate::util::runtime::block_on(async {
            loop {
                let res = std::future::poll_fn(|cx| device.poll_read(cx, &mut buf)).await;
                match res {
                    Ok(0) => break,
                    Ok(len) => output.extend(&buf[..len]),
                    Err(e) => return Err(e),
                }
            }
            Ok(())
        })?;

        // Verify output: Normal text + the invalid char + the rest
        let output_str = String::from_utf8_lossy(&output);
        assert!(output_str.starts_with("Normal text\n"));
        assert!(output_str.contains("XGHIJKL"));

        // No coverage file should be created.
        let files_count = fs::read_dir(tmp_dir.path())?
            .filter_map(|e| e.ok())
            .filter(|e| {
                e.path()
                    .file_name()
                    .is_some_and(|n| n.to_string_lossy().starts_with("invalid."))
                    && e.path().extension().is_some_and(|ext| ext == "xprofraw")
            })
            .count();
        assert_eq!(files_count, 0);

        Ok(())
    }

    #[test]
    fn test_wait_for_coverage() -> Result<()> {
        let mut data = VecDeque::new();
        data.extend(create_coverage_block(b"data1"));
        data.extend(b"== COVERAGE PROFILE SKIP ==\r\n");

        let mock = MockConsole {
            data: Mutex::new(data),
            pending_count: Mutex::new(0),
        };
        let device = CoverageMiddleware::new_with_template(mock, "wait.%p.profraw".to_string());

        // Wait for first block.
        device.wait_for_coverage(Duration::from_secs(1))?;

        // Wait for standalone skip.
        device.wait_for_coverage(Duration::from_secs(1))?;

        Ok(())
    }

    #[test]
    fn test_wait_for_coverage_with_logging() -> Result<()> {
        let mut data = VecDeque::new();
        data.extend(create_coverage_block(b"data_logged"));
        data.extend(b"Trailing data\n");

        let mock = MockConsole {
            data: Mutex::new(data),
            pending_count: Mutex::new(0),
        };
        // Use the extension methods to create the chain: Logged<CoverageMiddleware<MockConsole>>
        let device = mock.coverage().logged();

        // Wait for the block. This should poll Logged, which polls CoverageMiddleware, which polls MockConsole.
        device.wait_for_coverage(Duration::from_secs(1))?;

        // Ensure trailing data is still readable.
        let mut output = String::new();
        let mut buf = [0u8; 64];
        let timeout = Duration::from_millis(100);
        loop {
            let len = device.read_timeout(&mut buf, timeout)?;
            if len == 0 {
                break;
            }
            output.push_str(&String::from_utf8_lossy(&buf[..len]));
            if output.contains('\n') {
                break;
            }
        }
        assert_eq!(output, "Trailing data\n");

        Ok(())
    }
}
