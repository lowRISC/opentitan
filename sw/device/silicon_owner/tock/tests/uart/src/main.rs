// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![no_main]
#![no_std]

use core::cell::Cell;
use core::cmp::min;
use libtock::console::Console;
use libtock::platform::{share, AllowRo, DefaultConfig, Subscribe, Syscalls};
use libtock::runtime::{set_main, stack_size, TockSyscalls};

set_main!(main);
stack_size!(0x800);

const DRIVER_NUM: u32 = 1;
const ALLOW_RO_WRITE: u32 = 1;
const ALLOW_RW_READ: u32 = 1;
const COMMAND_WRITE: u32 = 1;
const COMMAND_READ: u32 = 2;
const SUBSCRIBE_WRITE: u32 = 1;
const SUBSCRIBE_READ: u32 = 2;

// Reads data from the console input. The data is read in chunks whose length is
// given by `lens`. The newly-read data is returned. Panics upon encountering an
// error condition.
fn read_exact<'b>(buffer: &'b mut [u8], lens: &[usize]) -> &'b [u8] {
    assert!(buffer.len() >= lens.iter().sum());
    let upcall: Cell<Option<(u32, u32)>> = Cell::new(None);
    let mut cursor = 0;
    share::scope(|handle| {
        TockSyscalls::subscribe::<_, _, DefaultConfig, DRIVER_NUM, SUBSCRIBE_READ>(handle, &upcall)
            .unwrap();
        for &len in lens {
            let bytes = share::scope(|handle| {
                TockSyscalls::allow_rw::<DefaultConfig, DRIVER_NUM, ALLOW_RW_READ>(
                    handle,
                    &mut buffer[cursor..],
                )
                .unwrap();
                if let Some(error) =
                    TockSyscalls::command(DRIVER_NUM, COMMAND_READ, len as u32, 0).get_failure()
                {
                    panic!("{:?}", error);
                }
                loop {
                    TockSyscalls::yield_wait();
                    if let Some((_, bytes)) = upcall.take() {
                        return bytes;
                    }
                }
            });
            assert_eq!(bytes as usize, len);
            cursor += len;
        }
    });
    &buffer[..cursor]
}

// Sends a message to the console while simultaneously reading data from the
// console. `to_send` is sent repeatedly until a total of `tx_len` bytes have
// been transmitted. Receives will be limited in size to `max_rx_len`; multiple
// receives will be issued if this is less than `rx_buffer.len()`. The received
// message will be returned.
fn send_and_receive<'b>(
    to_send: &[u8],
    tx_len: usize,
    rx_buffer: &'b mut [u8],
    max_rx_len: u32,
) -> &'b [u8] {
    let rx_upcall: Cell<Option<(u32, u32)>> = Cell::new(None);
    let tx_upcall: Cell<Option<(u32,)>> = Cell::new(Some((0,)));
    // rx_cursor and sent_bytes are updated when a read-write is complete, not
    // when one is issued.
    let mut rx_cursor = 0;
    let mut sent_bytes = 0;
    let rx_len = rx_buffer.len();
    share::scope::<
        (
            Subscribe<_, DRIVER_NUM, SUBSCRIBE_READ>,
            Subscribe<_, DRIVER_NUM, SUBSCRIBE_WRITE>,
            AllowRo<_, DRIVER_NUM, ALLOW_RO_WRITE>,
        ),
        _,
        _,
    >(|handle| {
        let (rx_upcall_handle, tx_upcall_handle, tx_allow_handle) = handle.split();
        TockSyscalls::subscribe::<_, _, DefaultConfig, DRIVER_NUM, SUBSCRIBE_READ>(
            rx_upcall_handle,
            &rx_upcall,
        )
        .unwrap();
        TockSyscalls::subscribe::<_, _, DefaultConfig, DRIVER_NUM, SUBSCRIBE_WRITE>(
            tx_upcall_handle,
            &tx_upcall,
        )
        .unwrap();
        TockSyscalls::allow_ro::<DefaultConfig, DRIVER_NUM, ALLOW_RO_WRITE>(
            tx_allow_handle,
            to_send,
        )
        .unwrap();
        while rx_cursor < rx_len || sent_bytes < tx_len {
            share::scope(|handle| {
                TockSyscalls::allow_rw::<DefaultConfig, DRIVER_NUM, ALLOW_RW_READ>(
                    handle,
                    &mut rx_buffer[rx_cursor..],
                )
                .unwrap();
                if rx_cursor < rx_len {
                    let read_len = min((rx_len - rx_cursor) as u32, max_rx_len);
                    if let Some(error) =
                        TockSyscalls::command(DRIVER_NUM, COMMAND_READ, read_len, 0).get_failure()
                    {
                        panic!("{:?}", error);
                    }
                }
                loop {
                    TockSyscalls::yield_wait();
                    if let Some((bytes,)) = tx_upcall.take() {
                        sent_bytes += bytes as usize;
                        if sent_bytes < tx_len {
                            let send_len = min(to_send.len(), tx_len - sent_bytes) as u32;
                            if let Some(error) =
                                TockSyscalls::command(DRIVER_NUM, COMMAND_WRITE, send_len, 0)
                                    .get_failure()
                            {
                                panic!("{:?}", error);
                            }
                        }
                    }
                    if let Some((_, bytes)) = rx_upcall.take() {
                        rx_cursor += bytes as usize;
                        break;
                    }
                    if rx_cursor >= rx_len && sent_bytes >= tx_len {
                        break;
                    }
                }
            });
        }
    });
    &rx_buffer[..rx_cursor]
}

fn main() {
    let mut buffer = [0; 256];

    // Test A: Send a message with all printable ASCII characters each
    // direction. We do host->device first then device->host. The host->device
    // message is padded to 128 bytes, which matches the hardware receive
    // buffer.
    assert_eq!(
        read_exact(
            &mut buffer,
            &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 8]
        ),
        concat!(
            r##"! "#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\]^_"##,
            r##"`abcdefghijklmnopqrstuvwxyz{|}~Padding to 128 bytes looooooooong"##,
        )
        .as_bytes()
    );
    Console::write(
        concat!(
            r##"! "#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOP"##,
            r##"QRSTUVWXYZ[\]^_`abcdefghijklmnopqrstuvwxyz{|}~"##,
            "\n",
        )
        .as_bytes(),
    )
    .unwrap();

    // Test B: The host sends a message broken into two parts, with a delay
    // between the parts. The app should be able to receive both of these in one
    // read operation.
    assert_eq!(read_exact(&mut buffer, &[15]), b"Broken message.",);

    // Test C: Attempt to send host->device and device->host messages
    // concurrently. host->device messages are in capital letters and
    // device->host messages are in lowercase.
    assert_eq!(
        send_and_receive(b"abcdefghijklmnopqrstuvwxyz", 26, &mut buffer[..26], 5,),
        b"ABCDEFGHIJKLMNOPQRSTUVWXYZ",
    );
    assert_eq!(
        send_and_receive(&[b'a'; 25], 100, &mut buffer[..50], 25,),
        [b'A'; 50],
    );
    assert_eq!(
        send_and_receive(&[b'b'; 6], 37, &mut buffer[..42], 42,),
        [b'B'; 42],
    );

    // Tell the host we are done (this makes sure the final receive in Test C
    // has completed).
    Console::write(b"DEVICE DONE.\n").unwrap();
}
