// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::io::ErrorKind;
use std::marker::PhantomData;
use std::sync::Arc;

use anyhow::{Context, Result, bail};
use serde::Serialize;
use serde::de::DeserializeOwned;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt};
use tokio::net::TcpListener;
use tokio::net::tcp::{OwnedReadHalf, OwnedWriteHalf};

use super::CommandHandler;

const EOL_CODE: u8 = b'\n';

/// This struct listens on a TCP socket, and maintains a number of concurrent connections,
/// receiving serialized JSON representations of `Msg`, passing them to the given
/// `CommandHandler` to obtain responses to be sent as socket flow contol permits.  Note that
/// this implementaion is not specific to (and does not refer to) any particular protocol.
pub struct JsonSocketServer<Msg: DeserializeOwned + Serialize, T: CommandHandler<Msg>> {
    command_handler: T,
    socket: TcpListener,
    phantom: PhantomData<Msg>,
}

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
        // Create a local set to allow `spawn_local`. This is needed as majority of opentitanlib is not
        // multi-thread-safe currently.
        let local_set = tokio::task::LocalSet::new();
        let _local_set_guard = local_set.enter();

        // Store all connections in a join set so they're aborted when terminating.
        let mut set = tokio::task::JoinSet::new();
        let mut id_counter = 0;

        // Since opentitanlib is mostly not multi-thread-safe, we have to stay on this thread to deal with
        // `command_handler`.
        // We do this by using a mpsc queue that each connection can push to.
        let (sender, mut recv) = tokio::sync::mpsc::channel(32);

        let listener = async {
            loop {
                // Drain connections that are already completed.
                while set.try_join_next().is_some() {}

                let (conn, _) = self
                    .socket
                    .accept()
                    .await
                    .context("Error accepting TCP connection")?;

                let id = id_counter;
                id_counter += 1;
                log::info!("New connection id:{:#X}", id);

                conn.set_nodelay(true)?;
                let (conn_rx, conn_tx) = conn.into_split();

                // For sending messages, create an unbounded channel and a task that keeps transmitting.
                // This ensures that we can send message in any context without blocking.
                let (tx_send, tx_recv) = tokio::sync::mpsc::unbounded_channel();
                set.spawn(async move {
                    if let Err(err) = Self::process_tx(tx_recv, conn_tx).await {
                        log::warn!("Connection {:#X} error: {}", id, err);
                    }
                });
                let conn = Arc::new(Connection::new(tx_send));

                let sender_clone = sender.clone();
                set.spawn(async move {
                    if let Err(err) = Self::process_rx(sender_clone, conn, conn_rx).await {
                        log::warn!("Connection {:#X} error: {}", id, err);
                    }

                    log::info!("Closing connection id:{:#X}", id);
                });
            }

            // Type hint
            #[allow(unreachable_code)]
            Ok::<(), anyhow::Error>(())
        };

        let handler = async {
            loop {
                let (conn, request, resp_send) =
                    recv.recv().await.expect("recv shouldn't be dropped");
                let resp = self.command_handler.execute_cmd(&conn, &request)?;
                // Ignore error which indicates the connection has been closed.
                let _ = resp_send.send(resp);
            }

            // Type hint
            #[allow(unreachable_code)]
            Ok::<(), anyhow::Error>(())
        };

        // Ensure that the local set never completes so we can keep polling it using `select!`.
        local_set.spawn_local(std::future::pending::<()>());

        tokio::select! {
            r = listener => r,
            r = handler => r,
            _ = local_set => unreachable!(),
        }
    }

    /// Read and write as much as possible from one particular socket connection.
    async fn process_rx(
        sender: tokio::sync::mpsc::Sender<(
            Arc<Connection>,
            Msg,
            tokio::sync::oneshot::Sender<Msg>,
        )>,
        conn: Arc<Connection>,
        conn_rx: OwnedReadHalf,
    ) -> Result<()> {
        let mut conn_rx = tokio::io::BufReader::new(conn_rx);
        let mut buf = Vec::new();

        loop {
            buf.clear();
            let len = conn_rx.read_until(b'\n', &mut buf).await?;
            if len == 0 {
                if !buf.is_empty() {
                    bail!(std::io::Error::new(
                        ErrorKind::UnexpectedEof,
                        "Server unexpectedly closed connection"
                    ));
                }
                break;
            }

            let request = serde_json::from_slice::<Msg>(&buf)?;

            let (resp_send, resp_recv) = tokio::sync::oneshot::channel();
            sender
                .send((conn.clone(), request, resp_send))
                .await
                .unwrap();
            let resp = resp_recv.await?;
            conn.transmit_outgoing_msg(resp)?;
        }

        Ok(())
    }

    /// Task processing transmission of packets over the proxy link.
    async fn process_tx(
        mut msg: tokio::sync::mpsc::UnboundedReceiver<Vec<u8>>,
        mut conn_tx: OwnedWriteHalf,
    ) -> Result<()> {
        while let Some(mut vec) = msg.recv().await {
            vec.push(EOL_CODE);
            conn_tx.write_all(&vec).await?;
            conn_tx.flush().await?;
        }
        Ok(())
    }
}

/// Represents one connection with a remote OpenTitan tool invocation.
pub struct Connection {
    tx: tokio::sync::mpsc::UnboundedSender<Vec<u8>>,
}

impl Connection {
    fn new(tx: tokio::sync::mpsc::UnboundedSender<Vec<u8>>) -> Self {
        Self { tx }
    }

    pub fn transmit_outgoing_msg<T: Serialize>(&self, msg: T) -> Result<()> {
        self.tx
            .send(serde_json::to_vec(&msg)?)
            .context("tx connection broken")
    }
}
