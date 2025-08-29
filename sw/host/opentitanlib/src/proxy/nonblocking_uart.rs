// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use mio::event::Event;
use mio::{Interest, Registry, Token};
use std::collections::HashMap;
use std::collections::hash_map::Entry::{Occupied, Vacant};
use std::hash::{Hash, Hasher};
use std::io::{Read, Write};
use std::ptr::hash;
use std::rc::Rc;
use std::sync::{Arc, Mutex, Weak};
use std::task::{Context, Poll, Wake, Waker};

use super::ExtraEventHandler;
use super::socket_server::{Connection, get_next_token};
use crate::io::uart::Uart;

pub struct NonblockingUartRegistry {
    pub token_map: HashMap<Token, UartKey>,
    // Set of Uart objects in "nonblocking read" mode.  Key is the address of the Uart object.
    // Once switched to nonblocking mode, they do not go back.
    pub nonblocking_uarts: HashMap<UartKey, NonblockingUart>,
}

struct UartWaker {
    send: mio::unix::pipe::Sender,
    recv: mio::unix::pipe::Receiver,
}

impl UartWaker {
    fn reset(&self) {
        loop {
            if self.recv.try_io(|| (&self.recv).read(&mut [0])).is_err() {
                break;
            }
        }
    }
}

impl Wake for UartWaker {
    fn wake(self: Arc<Self>) {
        self.wake_by_ref();
    }

    fn wake_by_ref(self: &Arc<Self>) {
        let _ = (&self.send).write(&[1]);
    }
}

impl NonblockingUartRegistry {
    pub fn new() -> Self {
        Self {
            token_map: HashMap::new(),
            nonblocking_uarts: HashMap::new(),
        }
    }

    pub fn nonblocking_uart_init(
        &mut self,
        uart: &std::rc::Rc<dyn crate::io::uart::Uart>,
        conn: &Arc<Mutex<Connection>>,
        registry: &Registry,
    ) -> Result<u32> {
        match self.nonblocking_uarts.entry(UartKey(uart.clone())) {
            Vacant(entry) => {
                let token = get_next_token();
                self.token_map.insert(token, UartKey(uart.clone()));
                let (send, mut recv) = mio::unix::pipe::new()?;
                registry.register(&mut recv, token, Interest::READABLE)?;
                let waker = Arc::new(UartWaker { send, recv });
                waker.wake_by_ref();

                let mut nonblocking_uart = NonblockingUart::new(uart, waker, token.0 as u32);
                nonblocking_uart.add_connection(conn);
                let channel = nonblocking_uart.channel;
                entry.insert(nonblocking_uart);
                Ok(channel)
            }
            Occupied(mut entry) => {
                let nonblocking_uart = entry.get_mut();
                nonblocking_uart.add_connection(conn);
                Ok(nonblocking_uart.channel)
            }
        }
    }
}

impl ExtraEventHandler for NonblockingUartRegistry {
    fn handle_poll_event(&mut self, event: &Event) -> Result<bool> {
        match self.token_map.get(&event.token()) {
            Some(uart_key) => {
                if event.is_readable() {
                    self.nonblocking_uarts
                        .get_mut(uart_key)
                        .unwrap()
                        .process()?;
                }
                Ok(true)
            }
            None => Ok(false),
        }
    }
}

pub struct NonblockingUart {
    conn: Vec<Weak<Mutex<Connection>>>,
    uart: std::rc::Rc<dyn crate::io::uart::Uart>,
    waker: Arc<UartWaker>,
    channel: u32,
}

impl NonblockingUart {
    fn new(
        uart: &std::rc::Rc<dyn crate::io::uart::Uart>,
        waker: Arc<UartWaker>,
        channel: u32,
    ) -> Self {
        Self {
            conn: Vec::new(),
            uart: uart.clone(),
            waker,
            channel,
        }
    }

    pub fn add_connection(&mut self, conn: &Arc<Mutex<Connection>>) {
        let downgrade = Arc::downgrade(conn);
        if self.conn.iter().any(|x| Weak::ptr_eq(x, &downgrade)) {
            return;
        }
        self.conn.push(downgrade);
    }

    fn process(&mut self) -> Result<()> {
        let mut buf = [0u8; 256];
        // We need to keep reading until a read returns pending, otherwise the waker will not be notified.
        let waker: Waker = self.waker.clone().into();
        let mut cx = Context::from_waker(&waker);
        loop {
            self.waker.reset();
            let len = match self.uart.poll_read(&mut cx, &mut buf)? {
                Poll::Pending => return Ok(()),
                Poll::Ready(len) => len,
            };

            // Iterate through list of connections who "subscribe" to this UART instance, putting
            // data into each of their outgoing buffers.  If any connection has been closed,
            // remove the reference to it from `conn`.
            let mut connections = Vec::with_capacity(self.conn.len());
            self.conn.retain(|x| {
                // Upgrade reference. If this fails, it means that the last instance is gone
                // and we shouldn't try further.
                if let Some(v) = x.upgrade() {
                    connections.push(v);
                    true
                } else {
                    false
                }
            });

            for conn in connections.into_iter() {
                conn.lock()
                    .unwrap()
                    .transmit_outgoing_msg(super::protocol::Message::Async {
                        channel: self.channel,
                        msg: super::protocol::AsyncMessage::UartData {
                            data: buf[0..len].to_vec(),
                        },
                    })?
            }
        }
    }
}

/// Struct allowing `HashMap` to use `Uart` object identity as the key.
#[derive(Clone)]
pub struct UartKey(pub Rc<dyn Uart>);

impl Hash for UartKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        hash(&*self.0, state)
    }
}
impl PartialEq for UartKey {
    /// Determines whether the two `Rc`s point to the same `Uart` instance.
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for UartKey {}
