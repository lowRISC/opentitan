// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashMap;
use std::io::ErrorKind;
use std::marker::PhantomData;
use std::rc::Rc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Weak};
use std::task::Wake;

use anyhow::{Context, Result};
use serde::Serialize;
use serde::de::DeserializeOwned;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt};
use tokio::net::TcpListener;
use tokio::net::tcp::{OwnedReadHalf, OwnedWriteHalf};
use tokio::sync::Mutex;

use opentitanlib::io::console::Broadcaster;
use opentitanlib::io::uart::Uart;

use super::CommandHandler;

/// This struct listens on a TCP socket, and maintains a number of concurrent connections,
/// receiving serialized JSON representations of `Msg`, passing them to the given
/// `CommandHandler` to obtain responses to be sent as socket flow contol permits.  Note that
/// this implementaion is not specific to (and does not refer to) any particular protocol.
pub struct JsonSocketServer<Msg: DeserializeOwned + Serialize, T: CommandHandler<Msg>> {
    command_handler: T,
    socket: TcpListener,
    phantom: PhantomData<Msg>,
}

#[allow(clippy::type_complexity)]
impl<Msg: DeserializeOwned + Serialize + Send + 'static, T: CommandHandler<Msg> + 'static>
    JsonSocketServer<Msg, T>
{
    pub fn new(command_handler: T, socket: TcpListener) -> Result<Self> {
        Ok(Self {
            command_handler,
            socket,
            phantom: PhantomData,
        })
    }

    pub async fn run_loop(&mut self) -> Result<()> {
        // Store all connections in a join set so they're aborted when terminating.
        let mut set = tokio::task::JoinSet::new();

        // Since opentitanlib is mostly not multi-thread-safe, we have to stay on this thread to deal with
        // `command_handler`.
        // We do this by using a mpsc queue that each connection can push to.
        let (sender, mut recv) = tokio::sync::mpsc::channel(32);

        // We would like to store some data derived from OT-lib in connection-specific structure, which needs to
        // stay on this thread. So instead of only send an ID to another thread, keep all other info locally.
        let mut id_counter = 0;
        let connections = Mutex::new(HashMap::new());

        let listener = async {
            loop {
                // Drain connections that are already completed.
                while set.try_join_next().is_some() {}

                let (conn_socket, _address) = self
                    .socket
                    .accept()
                    .await
                    .context("Error accepting TCP connection")?;
                conn_socket.set_nodelay(true)?;

                let (conn_rx, conn_tx) = conn_socket.into_split();
                // `conn_tx` is used both for unsolicited messages and response messages.
                let conn_tx = Arc::new(Mutex::new(conn_tx));

                let id = id_counter;
                id_counter += 1;
                log::info!("New connection id:{:#X}", id);

                connections
                    .lock()
                    .await
                    .insert(id, Connection::new(conn_tx.clone()));

                let sender_clone = sender.clone();
                set.spawn(async move {
                    if let Err(err) =
                        Self::process_connection(&sender_clone, id, conn_rx, conn_tx).await
                    {
                        log::warn!("Connection {:#X} error: {}", id, err);
                    }

                    // Upon connection closing, send a message to the handler to finish it.
                    let _ = sender_clone.send((id, None)).await;
                });
            }

            // Type hint
            #[allow(unreachable_code)]
            Ok::<(), anyhow::Error>(())
        };

        let handler = async {
            loop {
                let (id, req) = recv.recv().await.expect("recv shouldn't be dropped");
                let mut conn = connections.lock().await;

                // Handle closing connections.
                let Some((request, resp_send)) = req else {
                    log::info!("Closing connection id:{:#X}", id);

                    conn.remove(&id);
                    continue;
                };

                let resp = self
                    .command_handler
                    .execute_cmd(conn.get_mut(&id).unwrap(), &request)?;
                // Ignore error which indicates the connection has been closed.
                let _ = resp_send.send(resp);
            }

            // Type hint
            #[allow(unreachable_code)]
            Ok::<(), anyhow::Error>(())
        };

        tokio::select! {
            r = listener => r,
            r = handler => r,
        }
    }

    /// Read and write as much as possible from one particular socket connection.
    async fn process_connection(
        sender: &tokio::sync::mpsc::Sender<(u32, Option<(Msg, tokio::sync::oneshot::Sender<Msg>)>)>,
        id: u32,
        conn_rx: OwnedReadHalf,
        conn_tx: Arc<Mutex<OwnedWriteHalf>>,
    ) -> Result<()> {
        let mut conn_rx = tokio::io::BufReader::new(conn_rx);
        let mut buf = Vec::new();

        loop {
            buf.clear();
            let len = conn_rx.read_until(b'\n', &mut buf).await?;
            if len == 0 {
                if !buf.is_empty() {
                    anyhow::bail!(std::io::Error::new(
                        ErrorKind::UnexpectedEof,
                        "Server unexpectedly closed connection"
                    ));
                }
                break;
            }

            let request = serde_json::from_slice::<Msg>(&buf)?;

            let (resp_send, resp_recv) = tokio::sync::oneshot::channel();
            sender.send((id, Some((request, resp_send)))).await.unwrap();
            let resp = resp_recv.await?;
            transmit_outgoing_msg(&conn_tx, resp).await?;
        }

        Ok(())
    }
}

async fn transmit_outgoing_msg<M: Serialize>(
    conn_tx: &Mutex<OwnedWriteHalf>,
    msg: M,
) -> Result<()> {
    // Encode response into tx_buf.
    let mut tx_buf = serde_json::to_vec(&msg)?;
    tx_buf.push(b'\n');

    let mut tx = conn_tx.lock().await;
    tx.write_all(&tx_buf).await?;
    Ok(())
}

/// Represents one connection with a remote OpenTitan tool invocation.
pub struct Connection {
    pub(crate) conn_tx: Arc<Mutex<OwnedWriteHalf>>,
    /// Map from address of a UART instance to a copy of the broadcaster.
    ///
    /// This ensures that initialized UARTs would be able to receive all data.
    /// Address is used so if an UART instance has multiple aliases, they're still backend
    /// by the same instance.
    pub(crate) uarts: HashMap<usize, Broadcaster<Rc<dyn Uart>>>,
}

impl Connection {
    fn new(conn_tx: Arc<Mutex<OwnedWriteHalf>>) -> Self {
        Self {
            conn_tx,
            uarts: HashMap::default(),
        }
    }
}

pub struct ProxyWaker {
    conn_tx: Weak<Mutex<OwnedWriteHalf>>,
    id: u32,
    triggered: AtomicBool,
}

impl ProxyWaker {
    pub(crate) fn new(conn_tx: &Arc<Mutex<OwnedWriteHalf>>, id: u32) -> Self {
        Self {
            conn_tx: Arc::downgrade(conn_tx),
            id,
            triggered: AtomicBool::new(false),
        }
    }

    pub(crate) fn dismiss(&self) {
        self.triggered.store(true, Ordering::Relaxed);
    }

    fn send(&self, triggered: bool) {
        if let Some(conn_tx) = self.conn_tx.upgrade() {
            let id = self.id;
            opentitanlib::util::runtime().spawn(async move {
                if let Err(err) =
                    transmit_outgoing_msg(&conn_tx, ot_proxy_proto::Message::Wake { id, triggered })
                        .await
                {
                    log::warn!("Transmission error while sending waker {id}: {err}");
                }
            });
        }
    }
}

impl Drop for ProxyWaker {
    fn drop(&mut self) {
        if self.triggered.load(Ordering::Relaxed) {
            return;
        }

        self.send(false);
    }
}

impl Wake for ProxyWaker {
    fn wake(self: Arc<Self>) {
        self.wake_by_ref();
    }

    fn wake_by_ref(self: &Arc<Self>) {
        if self
            .triggered
            .compare_exchange(false, true, Ordering::Relaxed, Ordering::Relaxed)
            .is_err()
        {
            return;
        }

        self.send(true);
    }
}
