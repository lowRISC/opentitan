// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashMap;
use std::collections::hash_map::Entry::{Occupied, Vacant};
use std::hash::{Hash, Hasher};
use std::ptr::hash;
use std::rc::Rc;
use std::sync::{Arc, Mutex, Weak};

use anyhow::Result;

use opentitanlib::io::uart::Uart;

use super::socket_server::Connection;

pub struct NonblockingUartRegistry {
    // Set of Uart objects in "nonblocking read" mode.  Key is the address of the Uart object.
    // Once switched to nonblocking mode, they do not go back.
    pub nonblocking_uarts: HashMap<UartKey, NonblockingUart>,
}

impl NonblockingUartRegistry {
    pub fn new() -> Self {
        Self {
            nonblocking_uarts: HashMap::new(),
        }
    }

    pub fn nonblocking_uart_init(
        &mut self,
        uart: &Rc<dyn Uart>,
        conn: &Arc<Mutex<Connection>>,
    ) -> Result<u32> {
        match self.nonblocking_uarts.entry(UartKey(uart.clone())) {
            Vacant(entry) => {
                pub fn get_next_channel() -> u32 {
                    use std::sync::atomic::{AtomicU32, Ordering};

                    static CHANNEL_COUNTER: AtomicU32 = AtomicU32::new(0);
                    CHANNEL_COUNTER.fetch_add(1, Ordering::Relaxed)
                }

                let channel = get_next_channel();
                let mut nonblocking_uart = NonblockingUart::new(uart.clone(), channel);
                nonblocking_uart.add_connection(conn);
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

struct NonblockingUartInner {
    conn: Vec<Weak<Mutex<Connection>>>,
}

pub struct NonblockingUart {
    inner: Arc<Mutex<NonblockingUartInner>>,
    channel: u32,
}

impl NonblockingUart {
    fn new(uart: Rc<dyn Uart>, channel: u32) -> Self {
        let inner = Arc::new(Mutex::new(NonblockingUartInner { conn: Vec::new() }));

        let inner_clone = inner.clone();
        tokio::task::spawn_local(async move { Self::process(inner_clone, uart, channel).await });

        Self { inner, channel }
    }

    pub fn add_connection(&mut self, conn: &Arc<Mutex<Connection>>) {
        let mut inner = self.inner.lock().unwrap();
        let downgrade = Arc::downgrade(conn);
        if inner.conn.iter().any(|x| Weak::ptr_eq(x, &downgrade)) {
            return;
        }
        inner.conn.push(downgrade);
    }

    async fn process(
        inner: Arc<Mutex<NonblockingUartInner>>,
        uart: Rc<dyn Uart>,
        channel: u32,
    ) -> Result<()> {
        let mut buf = [0u8; 256];
        loop {
            let len = std::future::poll_fn(|cx| uart.poll_read(cx, &mut buf)).await?;

            // Iterate through list of connections who "subscribe" to this UART instance, putting
            // data into each of their outgoing buffers.  If any connection has been closed,
            // remove the reference to it from `conn`.
            let mut connections = Vec::new();
            {
                let mut inner = inner.lock().unwrap();
                inner.conn.retain(|x| {
                    // Upgrade reference. If this fails, it means that the last instance is gone
                    // and we shouldn't try further.
                    if let Some(v) = x.upgrade() {
                        connections.push(v);
                        true
                    } else {
                        false
                    }
                });
            }

            for conn in connections.into_iter() {
                conn.lock()
                    .unwrap()
                    .transmit_outgoing_msg(ot_proxy_proto::Message::Async {
                        channel,
                        msg: ot_proxy_proto::AsyncMessage::UartData {
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
