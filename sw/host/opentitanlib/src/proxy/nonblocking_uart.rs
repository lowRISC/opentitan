// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use mio::event::Event;
use mio::{Registry, Token};
use std::collections::hash_map::Entry::{Occupied, Vacant};
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::ptr::hash;
use std::rc::Rc;
use std::time::Duration;

use super::socket_server::{get_next_token, Connection};
use super::ExtraEventHandler;
use crate::io::uart::Uart;

pub struct NonblockingUartRegistry {
    pub token_map: HashMap<Token, UartKey>,
    // Set of Uart objects in "nonblocking read" mode.  Key is the address of the Uart object.
    // Once switched to nonblocking mode, they do not go back.
    pub nonblocking_uarts: HashMap<UartKey, NonblockingUart>,
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
        conn_token: Token,
        registry: &Registry,
    ) -> Result<u32> {
        match self.nonblocking_uarts.entry(UartKey(uart.clone())) {
            Vacant(entry) => {
                let token = get_next_token();
                self.token_map.insert(token, UartKey(uart.clone()));
                uart.register_nonblocking_read(registry, token)?;

                let mut nonblocking_uart = NonblockingUart::new(uart, token.0 as u32);
                nonblocking_uart.add_connection(conn_token);
                let channel = nonblocking_uart.channel;
                entry.insert(nonblocking_uart);
                Ok(channel)
            }
            Occupied(mut entry) => {
                let nonblocking_uart = entry.get_mut();
                nonblocking_uart.add_connection(conn_token);
                Ok(nonblocking_uart.channel)
            }
        }
    }
}

impl ExtraEventHandler for NonblockingUartRegistry {
    fn handle_poll_event(
        &mut self,
        event: &Event,
        connection_map: &mut HashMap<Token, Connection>,
    ) -> Result<bool> {
        match self.token_map.get(&event.token()) {
            Some(uart_key) => {
                if event.is_readable() {
                    self.nonblocking_uarts
                        .get_mut(uart_key)
                        .unwrap()
                        .process(connection_map)?;
                }
                Ok(true)
            }
            None => Ok(false),
        }
    }
}

pub struct NonblockingUart {
    conn_tokens: HashSet<Token>,
    uart: std::rc::Rc<dyn crate::io::uart::Uart>,
    channel: u32,
}

impl NonblockingUart {
    pub fn new(uart: &std::rc::Rc<dyn crate::io::uart::Uart>, channel: u32) -> Self {
        Self {
            conn_tokens: HashSet::new(),
            uart: uart.clone(),
            channel,
        }
    }

    pub fn add_connection(&mut self, conn_token: Token) {
        self.conn_tokens.insert(conn_token);
    }

    fn process(&mut self, connection_map: &mut HashMap<Token, Connection>) -> Result<()> {
        let mut buf = [0u8; 256];
        // `mio` convention demands that we keep reading until a read returns zero bytes,
        // otherwise next `poll()` is not guaranteed to notice more data.
        loop {
            let len = self.uart.read_timeout(&mut buf, Duration::from_millis(1))?;
            if len == 0 {
                return Ok(());
            }
            // Iterate through list of connections who "subscribe" to this UART instance, putting
            // data into each of their outgoing buffers.  If any connection has been closed,
            // remove the reference to it from `conn_tokens`.
            let mut closed_connections = Vec::new();
            for conn_token in &self.conn_tokens {
                if let Some(conn) = connection_map.get_mut(conn_token) {
                    conn.transmit_outgoing_msg(super::protocol::Message::Async {
                        channel: self.channel,
                        msg: super::protocol::AsyncMessage::UartData {
                            data: buf[0..len].to_vec(),
                        },
                    })?
                } else {
                    // The particular TCP connection has been closed, and should be removed from the
                    // list of subsribers to this `Uart`.  Keep its ID for removal when this
                    // iteration is done.
                    closed_connections.push(*conn_token);
                }
            }
            for conn_token in closed_connections {
                self.conn_tokens.remove(&conn_token);
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
    #[allow(clippy::vtable_address_comparisons)]
    fn eq(&self, other: &Self) -> bool {
        Rc::as_ptr(&self.0) == Rc::as_ptr(&other.0)
    }
}

impl Eq for UartKey {}
